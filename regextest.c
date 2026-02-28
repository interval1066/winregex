#include "regex.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdbool.h>
#include <time.h>  /* Added for potential performance testing */

/* Internal node types for regex AST */
typedef enum {
    NODE_CHAR,           /* Single character */
    NODE_ANY,            /* Any character (.) */
    NODE_STAR,           /* Kleene star (*) */
    NODE_PLUS,           /* Plus (+) */
    NODE_QUESTION,       /* Question mark (?) */
    NODE_CONCAT,         /* Concatenation */
    NODE_ALT,            /* Alternation (|) */
    NODE_BRACKET,        /* Character class [...] */
    NODE_NEG_BRACKET,    /* Negated character class [^...] */
    NODE_ANCHOR_START,   /* Start anchor (^) */
    NODE_ANCHOR_END,     /* End anchor ($) */
    NODE_PAREN,          /* Parenthesized group */
    NODE_BACKREF,        /* Back reference (\n) */
    NODE_RANGE           /* Range {m,n} */
} NodeType;

/* AST node structure */
typedef struct Node {
    NodeType type;
    union {
        char c;                 /* For NODE_CHAR */
        struct {
            struct Node* left;
            struct Node* right;
        } binary;               /* For binary ops */
        struct {
            struct Node* child;
            int min;
            int max;
        } quantifier;           /* For quantifiers */
        struct {
            bool negated;
            char* chars;
            size_t char_count;
            char* ranges;        /* For character ranges */
            size_t range_count;
        } bracket;              /* For character classes */
        int backref_num;        /* For back references */
    } data;
} Node;

/* Compilation context */
typedef struct {
    const char* pattern;
    int cflags;
    size_t pos;
    int error;
    Node* ast;
    size_t nsub;                /* Number of capturing groups */
    int* group_starts;          /* Start positions of groups in pattern */
    int* group_ends;            /* End positions of groups in pattern */
} CompContext;

/* Execution context */
typedef struct {
    const char* string;
    size_t len;
    int eflags;
    regmatch_t* pmatch;
    size_t nmatch;
    int* backref_matches;       /* For backreference tracking */
} ExecContext;

/* Function prototypes for internal use */
static Node* parse_bre(CompContext* ctx);
static Node* parse_ere(CompContext* ctx);
static Node* parse_branch_ere(CompContext* ctx);
static Node* parse_piece_ere(CompContext* ctx);
static Node* parse_atom_ere(CompContext* ctx);
static Node* parse_bracket(CompContext* ctx);
static void free_node(Node* node);
static int compile_node(Node* node, char* output, int* output_pos);
static int match_node(ExecContext* ctx, Node* node, size_t pos, size_t* new_pos);
static bool char_in_class(char c, Node* bracket_node, bool icase);
static bool is_quantifier(char c, int cflags);
static void handle_error(CompContext* ctx, int error);

/* Utility functions */
static bool is_special_bre(char c) {
    return c == '.' || c == '[' || c == '\\' || c == '*' || c == '^' || c == '$';
}

static bool is_special_ere(char c) {
    return c == '.' || c == '[' || c == '\\' || c == '*' ||
        c == '+' || c == '?' || c == '|' || c == '(' ||
        c == ')' || c == '{' || c == '}' || c == '^' ||
        c == '$';
}

/* Main compilation function */
int regcomp(regex_t* preg, const char* pattern, int cflags) {
    if (!preg || !pattern) return REG_BADPAT;

    CompContext ctx;
    memset(&ctx, 0, sizeof(CompContext));
    ctx.pattern = pattern;
    ctx.cflags = cflags;
    ctx.pos = 0;
    ctx.nsub = 0;

    /* Allocate temporary storage for group tracking */
    ctx.group_starts = malloc(strlen(pattern) * sizeof(int));
    ctx.group_ends = malloc(strlen(pattern) * sizeof(int));

    if (!ctx.group_starts || !ctx.group_ends) {
        free(ctx.group_starts);
        free(ctx.group_ends);
        return REG_ESPACE;
    }

    /* Parse based on regex type */
    if (cflags & REG_EXTENDED) {
        ctx.ast = parse_ere(&ctx);
    }
    else {
        ctx.ast = parse_bre(&ctx);
    }

    if (ctx.error) {
        free_node(ctx.ast);
        free(ctx.group_starts);
        free(ctx.group_ends);
        return ctx.error;
    }

    /* Store compiled data */
    preg->re_nsub = ctx.nsub;
    preg->re_data = ctx.ast;
    preg->re_cflags = cflags;

    free(ctx.group_starts);
    free(ctx.group_ends);

    return 0;
}

/* Basic Regular Expression parser */
static Node* parse_bre(CompContext* ctx) {
    Node* root = NULL;
    Node* current = NULL;
    Node* last_char = NULL;

    while (ctx->pattern[ctx->pos] && ctx->pattern[ctx->pos] != '\0') {
        char c = ctx->pattern[ctx->pos];

        if (c == '\\') {
            ctx->pos++;
            if (!ctx->pattern[ctx->pos]) {
                ctx->error = REG_EESCAPE;
                return NULL;
            }

            c = ctx->pattern[ctx->pos];
            if (isdigit(c)) {
                /* Back reference */
                Node* node = malloc(sizeof(Node));
                if (!node) {
                    ctx->error = REG_ESPACE;
                    return NULL;
                }
                node->type = NODE_BACKREF;
                node->data.backref_num = c - '0';
                ctx->pos++;

                if (!root) root = node;
                else if (current) current->data.binary.right = node;
                last_char = node;
            }
            else {
                /* Escaped character */
                Node* node = malloc(sizeof(Node));
                if (!node) {
                    ctx->error = REG_ESPACE;
                    return NULL;
                }
                node->type = NODE_CHAR;
                node->data.c = c;
                ctx->pos++;

                if (!root) root = node;
                else if (current) current->data.binary.right = node;
                last_char = node;
            }
        }
        else if (c == '[') {
            Node* node = parse_bracket(ctx);
            if (!node) return NULL;

            if (!root) root = node;
            else if (current) current->data.binary.right = node;
            last_char = node;
        }
        else if (c == '.') {
            Node* node = malloc(sizeof(Node));
            if (!node) {
                ctx->error = REG_ESPACE;
                return NULL;
            }
            node->type = NODE_ANY;
            ctx->pos++;

            if (!root) root = node;
            else if (current) current->data.binary.right = node;
            last_char = node;
        }
        else if (c == '*') {
            if (!last_char) {
                ctx->error = REG_BADRPT;
                return NULL;
            }

            Node* star = malloc(sizeof(Node));
            if (!star) {
                ctx->error = REG_ESPACE;
                return NULL;
            }
            star->type = NODE_STAR;
            star->data.quantifier.child = last_char;
            star->data.quantifier.min = 0;
            star->data.quantifier.max = -1;

            /* Replace last_char in the tree with star */
            if (root == last_char) {
                root = star;
            }
            else {
                Node* temp = root;
                while (temp->type == NODE_CONCAT &&
                    temp->data.binary.right != last_char) {
                    temp = temp->data.binary.right;
                }
                if (temp->type == NODE_CONCAT) {
                    temp->data.binary.right = star;
                }
                else if (temp->data.binary.right) {
                    temp->data.binary.right = star;
                }
            }
            last_char = star;
            ctx->pos++;
        }
        else if (c == '^' && ctx->pos == 0) {
            Node* node = malloc(sizeof(Node));
            if (!node) {
                ctx->error = REG_ESPACE;
                return NULL;
            }
            node->type = NODE_ANCHOR_START;
            ctx->pos++;

            if (!root) root = node;
            else if (current) current->data.binary.right = node;
            last_char = node;
        }
        else if (c == '$' && !ctx->pattern[ctx->pos + 1]) {
            Node* node = malloc(sizeof(Node));
            if (!node) {
                ctx->error = REG_ESPACE;
                return NULL;
            }
            node->type = NODE_ANCHOR_END;
            ctx->pos++;

            if (!root) root = node;
            else if (current) current->data.binary.right = node;
            last_char = node;
        }
        else {
            /* Regular character */
            Node* node = malloc(sizeof(Node));
            if (!node) {
                ctx->error = REG_ESPACE;
                return NULL;
            }
            node->type = NODE_CHAR;
            node->data.c = c;
            ctx->pos++;

            if (!root) {
                root = node;
            }
            else {
                /* Create concatenation if needed */
                Node* concat = malloc(sizeof(Node));
                if (!concat) {
                    free(node);
                    ctx->error = REG_ESPACE;
                    return NULL;
                }
                concat->type = NODE_CONCAT;
                concat->data.binary.left = last_char;
                concat->data.binary.right = node;

                if (root == last_char) {
                    root = concat;
                }
                else {
                    Node* temp = root;
                    while (temp->type == NODE_CONCAT &&
                        temp->data.binary.right != last_char) {
                        temp = temp->data.binary.right;
                    }
                    if (temp->type == NODE_CONCAT) {
                        temp->data.binary.right = concat;
                    }
                    else if (temp->data.binary.right) {
                        temp->data.binary.right = concat;
                    }
                }
                last_char = node;
            }
        }
    }

    return root;
}

/* Extended Regular Expression parser */
static Node* parse_ere(CompContext* ctx) {
    return parse_branch_ere(ctx);
}

static Node* parse_branch_ere(CompContext* ctx) {
    Node* left = parse_piece_ere(ctx);
    if (!left || ctx->error) return left;

    while (ctx->pattern[ctx->pos] == '|') {
        ctx->pos++;
        Node* right = parse_piece_ere(ctx);
        if (!right) {
            free_node(left);
            return NULL;
        }

        Node* alt = malloc(sizeof(Node));
        if (!alt) {
            free_node(left);
            free_node(right);
            ctx->error = REG_ESPACE;
            return NULL;
        }

        alt->type = NODE_ALT;
        alt->data.binary.left = left;
        alt->data.binary.right = right;
        left = alt;
    }

    return left;
}

static Node* parse_piece_ere(CompContext* ctx) {
    Node* atom = parse_atom_ere(ctx);
    if (!atom || ctx->error) return atom;

    /* Check for quantifiers */
    char c = ctx->pattern[ctx->pos];
    if (c == '*' || c == '+' || c == '?' || c == '{') {
        Node* quant = malloc(sizeof(Node));
        if (!quant) {
            free_node(atom);
            ctx->error = REG_ESPACE;
            return NULL;
        }

        if (c == '*') {
            quant->type = NODE_STAR;
            quant->data.quantifier.min = 0;
            quant->data.quantifier.max = -1;
            ctx->pos++;
        }
        else if (c == '+') {
            quant->type = NODE_PLUS;
            quant->data.quantifier.min = 1;
            quant->data.quantifier.max = -1;
            ctx->pos++;
        }
        else if (c == '?') {
            quant->type = NODE_QUESTION;
            quant->data.quantifier.min = 0;
            quant->data.quantifier.max = 1;
            ctx->pos++;
        }
        else if (c == '{') {
            /* Handle {m,n} range */
            ctx->pos++;
            int min = 0, max = -1;

            /* Parse min */
            while (isdigit(ctx->pattern[ctx->pos])) {
                min = min * 10 + (ctx->pattern[ctx->pos] - '0');
                ctx->pos++;
            }

            if (ctx->pattern[ctx->pos] == ',') {
                ctx->pos++;
                if (isdigit(ctx->pattern[ctx->pos])) {
                    max = 0;
                    while (isdigit(ctx->pattern[ctx->pos])) {
                        max = max * 10 + (ctx->pattern[ctx->pos] - '0');
                        ctx->pos++;
                    }
                }
            }
            else {
                max = min;
            }

            if (ctx->pattern[ctx->pos] != '}') {
                free_node(atom);
                free(quant);
                ctx->error = REG_EBRACE;
                return NULL;
            }
            ctx->pos++;

            quant->type = NODE_RANGE;
            quant->data.quantifier.min = min;
            quant->data.quantifier.max = max;
        }

        quant->data.quantifier.child = atom;
        return quant;
    }

    return atom;
}

static Node* parse_atom_ere(CompContext* ctx) {
    if (!ctx->pattern[ctx->pos]) return NULL;

    char c = ctx->pattern[ctx->pos];

    if (c == '\\') {
        ctx->pos++;
        if (!ctx->pattern[ctx->pos]) {
            ctx->error = REG_EESCAPE;
            return NULL;
        }

        c = ctx->pattern[ctx->pos];
        if (isdigit(c)) {
            /* Back reference */
            Node* node = malloc(sizeof(Node));
            if (!node) {
                ctx->error = REG_ESPACE;
                return NULL;
            }
            node->type = NODE_BACKREF;
            node->data.backref_num = c - '0';
            ctx->pos++;
            return node;
        }
        else {
            /* Escaped character */
            Node* node = malloc(sizeof(Node));
            if (!node) {
                ctx->error = REG_ESPACE;
                return NULL;
            }
            node->type = NODE_CHAR;
            node->data.c = c;
            ctx->pos++;
            return node;
        }
    }
    else if (c == '[') {
        return parse_bracket(ctx);
    }
    else if (c == '.') {
        Node* node = malloc(sizeof(Node));
        if (!node) {
            ctx->error = REG_ESPACE;
            return NULL;
        }
        node->type = NODE_ANY;
        ctx->pos++;
        return node;
    }
    else if (c == '^') {
        Node* node = malloc(sizeof(Node));
        if (!node) {
            ctx->error = REG_ESPACE;
            return NULL;
        }
        node->type = NODE_ANCHOR_START;
        ctx->pos++;
        return node;
    }
    else if (c == '$') {
        Node* node = malloc(sizeof(Node));
        if (!node) {
            ctx->error = REG_ESPACE;
            return NULL;
        }
        node->type = NODE_ANCHOR_END;
        ctx->pos++;
        return node;
    }
    else if (c == '(') {
        ctx->pos++;
        ctx->nsub++;
        int group_num = ctx->nsub;
        ctx->group_starts[group_num] = ctx->pos;

        Node* inner = parse_ere(ctx);
        if (!inner) return NULL;

        if (ctx->pattern[ctx->pos] != ')') {
            free_node(inner);
            ctx->error = REG_EPAREN;
            return NULL;
        }
        ctx->pos++;
        ctx->group_ends[group_num] = ctx->pos;

        Node* paren = malloc(sizeof(Node));
        if (!paren) {
            free_node(inner);
            ctx->error = REG_ESPACE;
            return NULL;
        }
        paren->type = NODE_PAREN;
        paren->data.quantifier.child = inner;
        return paren;
    }
    else if (is_special_ere(c)) {
        ctx->error = REG_BADPAT;
        return NULL;
    }
    else {
        /* Regular character */
        Node* node = malloc(sizeof(Node));
        if (!node) {
            ctx->error = REG_ESPACE;
            return NULL;
        }
        node->type = NODE_CHAR;
        node->data.c = c;
        ctx->pos++;
        return node;
    }
}

/* Parse character class [..] */
static Node* parse_bracket(CompContext* ctx) {
    if (ctx->pattern[ctx->pos] != '[') {
        ctx->error = REG_EBRACK;
        return NULL;
    }
    ctx->pos++;

    Node* node = malloc(sizeof(Node));
    if (!node) {
        ctx->error = REG_ESPACE;
        return NULL;
    }

    /* Check for negated class */
    bool negated = false;
    if (ctx->pattern[ctx->pos] == '^') {
        negated = true;
        ctx->pos++;
    }

    node->type = negated ? NODE_NEG_BRACKET : NODE_BRACKET;
    node->data.bracket.negated = negated;

    /* Temporary storage for characters and ranges */
    char chars[256];
    size_t char_count = 0;
    char ranges[128][2];
    size_t range_count = 0;

    /* Parse until closing bracket */
    while (ctx->pattern[ctx->pos] && ctx->pattern[ctx->pos] != ']') {
        char current = ctx->pattern[ctx->pos];

        /* Check for range */
        if (ctx->pattern[ctx->pos + 1] == '-' &&
            ctx->pattern[ctx->pos + 2] &&
            ctx->pattern[ctx->pos + 2] != ']') {

            char start = current;
            ctx->pos += 2;
            char end = ctx->pattern[ctx->pos];

            if (start > end) {
                free(node);
                ctx->error = REG_ERANGE;
                return NULL;
            }

            ranges[range_count][0] = start;
            ranges[range_count][1] = end;
            range_count++;
            ctx->pos++;
        }
        else {
            chars[char_count++] = current;
            ctx->pos++;
        }
    }

    if (ctx->pattern[ctx->pos] != ']') {
        free(node);
        ctx->error = REG_EBRACK;
        return NULL;
    }
    ctx->pos++;

    /* Copy data to node */
    node->data.bracket.chars = malloc(char_count);
    if (char_count > 0 && !node->data.bracket.chars) {
        free(node);
        ctx->error = REG_ESPACE;
        return NULL;
    }
    memcpy(node->data.bracket.chars, chars, char_count);
    node->data.bracket.char_count = char_count;

    node->data.bracket.ranges = malloc(range_count * 2);
    if (range_count > 0 && !node->data.bracket.ranges) {
        free(node->data.bracket.chars);
        free(node);
        ctx->error = REG_ESPACE;
        return NULL;
    }
    memcpy(node->data.bracket.ranges, ranges, range_count * 2);
    node->data.bracket.range_count = range_count;

    return node;
}

/* Free AST nodes recursively */
static void free_node(Node* node) {
    if (!node) return;

    switch (node->type) {
    case NODE_STAR:
    case NODE_PLUS:
    case NODE_QUESTION:
    case NODE_RANGE:
    case NODE_PAREN:
        free_node(node->data.quantifier.child);
        break;

    case NODE_CONCAT:
    case NODE_ALT:
        free_node(node->data.binary.left);
        free_node(node->data.binary.right);
        break;

    case NODE_BRACKET:
    case NODE_NEG_BRACKET:
        free(node->data.bracket.chars);
        free(node->data.bracket.ranges);
        break;

    default:
        break;
    }

    free(node);
}

/* Check if character matches bracket class */
static bool char_in_class(char c, Node* bracket_node, bool icase) {
    /* Check single characters */
    for (size_t i = 0; i < bracket_node->data.bracket.char_count; i++) {
        char class_char = bracket_node->data.bracket.chars[i];
        if (icase) {
            if (tolower(c) == tolower(class_char)) return true;
        }
        else {
            if (c == class_char) return true;
        }
    }

    /* Check ranges */
    for (size_t i = 0; i < bracket_node->data.bracket.range_count; i++) {
        char start = bracket_node->data.bracket.ranges[i * 2];
        char end = bracket_node->data.bracket.ranges[i * 2 + 1];

        if (icase) {
            c = tolower(c);
            start = tolower(start);
            end = tolower(end);
        }

        if (c >= start && c <= end) return true;
    }

    return false;
}

/* Match node against string at position pos */
static int match_node(ExecContext* ctx, Node* node, size_t pos, size_t* new_pos) {
    if (!node || pos > ctx->len) return 0;

    *new_pos = pos;

    switch (node->type) {
    case NODE_CHAR: {
        if (pos >= ctx->len) return 0;
        char c = ctx->string[pos];
        char pattern_c = node->data.c;

        if (ctx->eflags & REG_ICASE) {
            if (tolower(c) != tolower(pattern_c)) return 0;
        }
        else {
            if (c != pattern_c) return 0;
        }
        *new_pos = pos + 1;
        return 1;
    }

    case NODE_ANY: {
        if (pos >= ctx->len) return 0;
        char c = ctx->string[pos];
        if (c == '\n' && (ctx->eflags & REG_NEWLINE)) return 0;
        *new_pos = pos + 1;
        return 1;
    }

    case NODE_STAR: {
        /* Try longest match first */
        size_t best_pos = pos;
        size_t current_pos = pos;

        while (current_pos <= ctx->len) {
            size_t test_pos = current_pos;
            if (match_node(ctx, node->data.quantifier.child,
                test_pos, &test_pos)) {
                current_pos = test_pos;
                best_pos = current_pos;
            }
            else {
                break;
            }
        }

        /* Try shorter matches if needed */
        while (best_pos >= pos) {
            if (match_node(ctx, node->data.quantifier.child,
                best_pos, &best_pos)) {
                *new_pos = best_pos;
                return 1;
            }
            best_pos--;
        }

        *new_pos = pos;
        return 1;
    }

    case NODE_PLUS: {
        size_t temp_pos = pos;
        if (!match_node(ctx, node->data.quantifier.child,
            temp_pos, &temp_pos)) {
            return 0;
        }

        while (temp_pos <= ctx->len) {
            size_t next_pos = temp_pos;
            if (match_node(ctx, node->data.quantifier.child,
                next_pos, &next_pos)) {
                temp_pos = next_pos;
            }
            else {
                break;
            }
        }

        *new_pos = temp_pos;
        return 1;
    }

    case NODE_QUESTION: {
        size_t temp_pos = pos;
        if (match_node(ctx, node->data.quantifier.child,
            temp_pos, &temp_pos)) {
            *new_pos = temp_pos;
            return 1;
        }
        *new_pos = pos;
        return 1;
    }

    case NODE_RANGE: {
        int min = node->data.quantifier.min;
        int max = node->data.quantifier.max;
        int count = 0;
        size_t current_pos = pos;

        /* Match min times first */
        while (count < min && current_pos <= ctx->len) {
            if (!match_node(ctx, node->data.quantifier.child,
                current_pos, &current_pos)) {
                return 0;
            }
            count++;
        }

        /* Try to match up to max times */
        size_t best_pos = current_pos;
        while ((max == -1 || count < max) && current_pos <= ctx->len) {
            size_t test_pos = current_pos;
            if (match_node(ctx, node->data.quantifier.child,
                test_pos, &test_pos)) {
                current_pos = test_pos;
                best_pos = current_pos;
                count++;
            }
            else {
                break;
            }
        }

        *new_pos = best_pos;
        return 1;
    }

    case NODE_CONCAT: {
        size_t temp_pos = pos;
        if (!match_node(ctx, node->data.binary.left,
            temp_pos, &temp_pos)) {
            return 0;
        }
        if (!match_node(ctx, node->data.binary.right,
            temp_pos, &temp_pos)) {
            return 0;
        }
        *new_pos = temp_pos;
        return 1;
    }

    case NODE_ALT: {
        size_t temp_pos = pos;
        if (match_node(ctx, node->data.binary.left,
            temp_pos, &temp_pos)) {
            *new_pos = temp_pos;
            return 1;
        }
        temp_pos = pos;
        if (match_node(ctx, node->data.binary.right,
            temp_pos, &temp_pos)) {
            *new_pos = temp_pos;
            return 1;
        }
        return 0;
    }

    case NODE_BRACKET: {
        if (pos >= ctx->len) return 0;
        char c = ctx->string[pos];
        bool match = char_in_class(c, node, ctx->eflags & REG_ICASE);
        if (match) {
            *new_pos = pos + 1;
            return 1;
        }
        return 0;
    }

    case NODE_NEG_BRACKET: {
        if (pos >= ctx->len) return 0;
        char c = ctx->string[pos];
        bool match = char_in_class(c, node, ctx->eflags & REG_ICASE);
        if (!match) {
            *new_pos = pos + 1;
            return 1;
        }
        return 0;
    }

    case NODE_ANCHOR_START: {
        if (pos == 0) {
            *new_pos = pos;
            return 1;
        }
        return 0;
    }

    case NODE_ANCHOR_END: {
        if (pos == ctx->len ||
            (ctx->string[pos] == '\n' && (ctx->eflags & REG_NEWLINE))) {
            *new_pos = pos;
            return 1;
        }
        return 0;
    }

    case NODE_PAREN: {
        return match_node(ctx, node->data.quantifier.child, pos, new_pos);
    }

    case NODE_BACKREF: {
        /* Simplified backreference handling */
        int ref = node->data.backref_num;
        if (ref <= 0 || ref > ctx->nmatch) return 0;

        regmatch_t* pm = &ctx->pmatch[ref];
        if (pm->rm_so == -1 || pm->rm_eo == -1) return 0;

        size_t match_len = pm->rm_eo - pm->rm_so;
        if (pos + match_len > ctx->len) return 0;

        if (strncmp(ctx->string + pos,
            ctx->string + pm->rm_so,
            match_len) == 0) {
            *new_pos = pos + match_len;
            return 1;
        }
        return 0;
    }

    default:
        return 0;
    }
}

/* Main execution function */
int regexec(const regex_t* preg, const char* string, size_t nmatch,
    regmatch_t pmatch[], int eflags) {
    if (!preg || !string) return REG_BADPAT;

    Node* ast = (Node*)preg->re_data;
    if (!ast) return REG_BADPAT;

    ExecContext ctx;
    ctx.string = string;
    ctx.len = strlen(string);
    ctx.eflags = eflags | preg->re_cflags;  /* Combine flags */
    ctx.pmatch = pmatch;
    ctx.nmatch = nmatch;

    /* Initialize match positions */
    for (size_t i = 0; i < nmatch; i++) {
        pmatch[i].rm_so = -1;
        pmatch[i].rm_eo = -1;
    }

    /* Try to match at each position */
    for (size_t start = 0; start <= ctx.len; start++) {
        size_t end_pos = start;

        if (match_node(&ctx, ast, start, &end_pos)) {
            if (nmatch > 0) {
                pmatch[0].rm_so = start;
                pmatch[0].rm_eo = end_pos;
            }

            /* If we need submatches, we'd need to track them */
            /* Simplified: just return success */
            return 0;
        }

        /* Stop at newline if REG_NEWLINE is set */
        if ((eflags & REG_NEWLINE) && string[start] == '\n') {
            break;
        }
    }

    return REG_NOMATCH;
}

/* Error message function */
size_t regerror(int errcode, const regex_t* preg, char* errbuf,
    size_t errbuf_size) {
    const char* msg;
    (void)preg; /* Suppress unused parameter warning */

    switch (errcode) {
    case 0:
        msg = "Success";
        break;
    case REG_NOMATCH:
        msg = "No match";
        break;
    case REG_BADPAT:
        msg = "Invalid regular expression";
        break;
    case REG_ECOLLATE:
        msg = "Invalid collation element";
        break;
    case REG_ECTYPE:
        msg = "Invalid character class";
        break;
    case REG_EESCAPE:
        msg = "Trailing backslash";
        break;
    case REG_ESUBREG:
        msg = "Invalid back reference";
        break;
    case REG_EBRACK:
        msg = "Unmatched bracket";
        break;
    case REG_EPAREN:
        msg = "Unmatched parenthesis";
        break;
    case REG_EBRACE:
        msg = "Unmatched brace";
        break;
    case REG_BADBR:
        msg = "Invalid brace count";
        break;
    case REG_ERANGE:
        msg = "Invalid range";
        break;
    case REG_ESPACE:
        msg = "Out of memory";
        break;
    case REG_BADRPT:
        msg = "Invalid repetition";
        break;
    default:
        msg = "Unknown error";
        break;
    }

    size_t len = strlen(msg) + 1;
    if (errbuf && errbuf_size > 0) {
        strncpy(errbuf, msg, errbuf_size - 1);
        errbuf[errbuf_size - 1] = '\0';
    }

    return len;
}

/* Free regex resources */
void regfree(regex_t* preg) {
    if (preg && preg->re_data) {
        free_node((Node*)preg->re_data);
        preg->re_data = NULL;
        preg->re_nsub = 0;
    }
}

/* Example usage - only compiled when EXAMPLE is defined */
#ifdef EXAMPLE
int main() {
    regex_t regex;
    regmatch_t matches[10];
    int ret;
    char error_buf[100];

    printf("POSIX Regular Expression Library Example\n");
    printf("========================================\n\n");

    /* Test 1: Basic pattern matching */
    printf("Test 1: Basic pattern 'hello'\n");
    ret = regcomp(&regex, "hello", 0);
    if (ret != 0) {
        regerror(ret, &regex, error_buf, sizeof(error_buf));
        printf("  Compilation failed: %s\n", error_buf);
    }
    else {
        ret = regexec(&regex, "hello world", 10, matches, 0);
        if (ret == 0) {
            printf("  Match found at [%d, %d]\n",
                (int)matches[0].rm_so, (int)matches[0].rm_eo);
        }
        else {
            printf("  No match found\n");
        }
        regfree(&regex);
    }

    /* Test 2: Case insensitive matching */
    printf("\nTest 2: Case insensitive 'hello'\n");
    ret = regcomp(&regex, "hello", REG_ICASE);
    if (ret != 0) {
        regerror(ret, &regex, error_buf, sizeof(error_buf));
        printf("  Compilation failed: %s\n", error_buf);
    }
    else {
        ret = regexec(&regex, "HELLO WORLD", 10, matches, 0);
        if (ret == 0) {
            printf("  Match found at [%d, %d]\n",
                (int)matches[0].rm_so, (int)matches[0].rm_eo);
        }
        else {
            printf("  No match found\n");
        }
        regfree(&regex);
    }

    /* Test 3: Character class */
    printf("\nTest 3: Character class [0-9]+\n");
    ret = regcomp(&regex, "[0-9]+", REG_EXTENDED);
    if (ret != 0) {
        regerror(ret, &regex, error_buf, sizeof(error_buf));
        printf("  Compilation failed: %s\n", error_buf);
    }
    else {
        ret = regexec(&regex, "abc123def", 10, matches, 0);
        if (ret == 0) {
            printf("  Match found at [%d, %d]: '%.*s'\n",
                (int)matches[0].rm_so, (int)matches[0].rm_eo,
                (int)(matches[0].rm_eo - matches[0].rm_so),
                "abc123def" + matches[0].rm_so);
        }
        else {
            printf("  No match found\n");
        }
        regfree(&regex);
    }

    /* Test 4: Email pattern */
    printf("\nTest 4: Email pattern\n");
    ret = regcomp(&regex, "^[a-zA-Z0-9._%%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]{2,}$", REG_EXTENDED);
    if (ret != 0) {
        regerror(ret, &regex, error_buf, sizeof(error_buf));
        printf("  Compilation failed: %s\n", error_buf);
    }
    else {
        const char* emails[] = { "user@example.com", "invalid.email", NULL };
        for (int i = 0; emails[i] != NULL; i++) {
            ret = regexec(&regex, emails[i], 10, matches, 0);
            printf("  '%s': %s\n", emails[i], ret == 0 ? "valid" : "invalid");
        }
        regfree(&regex);
    }

    /* Test 5: Back reference */
    printf("\nTest 5: Back reference (BRE)\n");
    ret = regcomp(&regex, "\\(a\\)\\1", 0);
    if (ret != 0) {
        regerror(ret, &regex, error_buf, sizeof(error_buf));
        printf("  Compilation failed: %s\n", error_buf);
    }
    else {
        const char* strings[] = { "aa", "ab", NULL };
        for (int i = 0; strings[i] != NULL; i++) {
            ret = regexec(&regex, strings[i], 10, matches, 0);
            printf("  '%s': %s\n", strings[i], ret == 0 ? "matches" : "does not match");
        }
        regfree(&regex);
    }

    printf("\nExample completed.\n");
    return 0;
}
#endif /* EXAMPLE */