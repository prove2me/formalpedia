-- Prove2me | Definitions.Def_CodedSorting_Records
-- name    : CodedSorting_Records
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:06:24.174635+00:00
-- url     : https://prove2.me/theorems/21134acf-2ad6-4e13-9daa-38ebd4a690e2
-- title:
--   Records of a constant number of words, lexicographic order and their disk layout
-- statement:
--   A **record** of $r$ words is a tuple $(a_0,\dots,a_{r-1})$ of $w$-bit words, compared lexicographically: $a\le b$ when $a=b$ or the first field where they differ is smaller in $a$.
--
--   An array of $n$ records is stored contiguously: record $i$ occupies disk words $ir,\dots,ir+r-1$, field $c$ in word $ir+c$, and every other disk word is $0$. The array is **sorted** on a disk when the $n$ records read back from words $0,\dots,nr-1$ form a permutation of the input records and are lexicographically nondecreasing.
--
--   This is the record notion of §7 ("A record may also consist of a constant number of integer fields compared lexicographically") used by the local sorting bound, Lemma 7.2.
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §7, p.26 (PDF 27)

import Mathlib
import Definitions.Def_CodedSorting_Machine

namespace CodedSorting

/-! # Records of a constant number of words

arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §7, p.26: "We call each element to be
sorted a record. … A record may also consist of a constant number of integer fields compared
lexicographically". -/

/-- A record of `r` words. -/
abbrev Record (r w : ℕ) := Fin r → Word w

/-- The lexicographic order on records: `a ≤ b` iff `a = b` or the word lists of `a` and `b` first
differ at a field where `a`'s word is smaller. -/
def RecLE {r w : ℕ} (a b : Record r w) : Prop :=
  a = b ∨ List.Lex (· < ·) (List.ofFn a) (List.ofFn b)

/-- The disk holding `n` records contiguously: record `i` occupies disk words `[i·r, i·r + r)`,
field `c` in word `i·r + c`; every other word is `0`. -/
def recordDisk {n r w : ℕ} (x : Fin n → Record r w) : Disk w :=
  fun a => if h : a / r < n ∧ a % r < r then x ⟨a / r, h.1⟩ ⟨a % r, h.2⟩ else 0

/-- The `n` records stored in the disk `d` at words `[i·r, i·r + r)`, `i < n`. -/
def readRecords {r w : ℕ} (n : ℕ) (d : Disk w) : Fin n → Record r w :=
  fun i c => d (i * r + c)

/-- The disk `d` holds the records of `x` sorted: the records read back from words `[0, n·r)` form a
permutation of the input records and are lexicographically nondecreasing. -/
def IsSortedRecords {n r w : ℕ} (x : Fin n → Record r w) (d : Disk w) : Prop :=
  (List.ofFn (readRecords n d)).Perm (List.ofFn x) ∧
    (List.ofFn (readRecords (r := r) n d)).Pairwise RecLE

end CodedSorting


