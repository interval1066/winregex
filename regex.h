#pragma once

#include <stddef.h>
#include <sys/types.h>

/* POSIX regex constants */
#define REG_EXTENDED    1
#define REG_ICASE       2
#define REG_NOSUB       4
#define REG_NEWLINE     8

/* Error codes */
#define REG_NOMATCH     1
#define REG_BADPAT      2
#define REG_ECOLLATE    3
#define REG_ECTYPE      4
#define REG_EESCAPE     5
#define REG_ESUBREG     6
#define REG_EBRACK      7
#define REG_EPAREN      8
#define REG_EBRACE      9
#define REG_BADBR       10
#define REG_ERANGE      11
#define REG_ESPACE      12
#define REG_BADRPT      13

// types
typedef off_t regoff_t;

// Regex structure
typedef struct {
    int re_magic;
    size_t re_nsub;
    void* re_data;
    int re_cflags;       // Compilation flags
} regex_t;

// Match structure
typedef struct {
    regoff_t rm_so;      // Start offset
    regoff_t rm_eo;      // End offset
} regmatch_t;

// Function declarations
int regcomp(regex_t* preg, const char* pattern, int cflags);
int regexec(const regex_t* preg, const char* string, size_t nmatch,
    regmatch_t pmatch[], int eflags);
size_t regerror(int errcode, const regex_t* preg, char* errbuf,
    size_t errbuf_size);
void regfree(regex_t* preg);
