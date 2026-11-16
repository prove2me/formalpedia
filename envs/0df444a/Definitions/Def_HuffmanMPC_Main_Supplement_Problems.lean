-- Prove2me | Definitions.Def_HuffmanMPC_Main_Supplement_Problems
-- name    : HuffmanMPC_Main_Supplement_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:17:53.90056+00:00
-- url     : https://prove2.me/theorems/26be11d9-952f-4a83-93b2-f9a3130ebcdf
-- title:
--   Sorted-prefix Huffman input and stable merge with all prefix sums
-- statement:
--   A frequency list is a list of natural numbers, retaining repeated occurrences. For a list $A$ of length $s$, its stored prefix array contains the sums $\sum_{i=0}^{r-1}A_i$ for $1\le r\le s$; the empty prefix is implicitly zero.
--
--   The Huffman input consists only of the sorted-frequency prefix array and redundant length and total words. Admissible lists have at least two entries, all positive and sorted. The requested scalar is the published independent prefix-code optimum $\mu(A)$.
--
--   The merge input consists of an original count $m\ge2$, total $n\ge m$, two sorted nonnegative lists $L_1,L_2$, and both correct prefix arrays, with total length $s\le m$ and total sum at most $n$. Equal values are ordered by their occurrence positions in $L_1\mathbin{++}L_2$. The required output consists of all $s$ merged values, their stable occurrence identifiers, and all $s$ nonempty prefix sums:
--   $$M^+[r]=\sum_{i<r}M_i\quad(1\le r\le s).$$
--   These are output specifications; sorting and prefix summation in their definitions are not machine instructions. Neither list is required to be nonempty. Two empty lists have empty output. Allowing zero entries extends the Section 9 frequency setting without excluding any source instance.
-- source:
--   Masoud Seddighin, Saeed Seddighin, STOC 2027 submission #377 (October 2026), Massively Parallel Algorithms for Huffman Coding, pp. 41–43, 45 (PDF 42–44, 46), Section 9 input; Theorem 9.2; Lemma 9.4

import Definitions.Def_HuffmanMPC_Main_Coding
import Definitions.Def_HuffmanMPC_Main_Supplement_PRAM

set_option autoImplicit false

namespace HuffmanMPC.Main.Supplement

/-- Nonempty prefixes; the empty prefix is implicit zero and consumes no cell.
In particular two empty lists have an empty output and require zero work. -/
def prefixes (a : List ℕ) : List ℕ :=
  (List.range a.length).map (fun i => (a.take (i + 1)).sum)

/-- Only the sorted prefixes, not the frequencies or any optimum, are supplied.
The two header words are redundant length/total information. -/
def huffmanInput (a : List ℕ) : List ℕ :=
  [a.length, a.sum] ++ prefixes a

def HuffmanInstance (a : List ℕ) : Prop :=
  2 ≤ a.length ∧ Positive a ∧ a.Pairwise (· ≤ ·)

/-- The occurrence id is its position in L1 ++ L2. This fixed order resolves
all equal keys, with L1 preceding L2 and order preserved within each list. -/
def mergeOccurrences (a b : List ℕ) : List (ℕ × ℕ) :=
  ((a ++ b).zipIdx).mergeSort
    (fun x y => x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2))

def merged (a b : List ℕ) : List ℕ := (mergeOccurrences a b).map Prod.fst

/-- All occurrences, their stable identities, and every nonempty prefix sum.
The identity array makes stability a checkable part of the output relation. -/
def mergeOutput (a b : List ℕ) : List ℕ :=
  merged a b ++ (mergeOccurrences a b).map Prod.snd ++ prefixes (merged a b)

/-- m is the original frequency count, n its total. Both input arrays and both
correct prefix arrays are supplied; no later iteration's prefixes are supplied. -/
def mergeInput (m n : ℕ) (a b : List ℕ) : List ℕ :=
  [m,n,a.length,b.length] ++ a ++ b ++ prefixes a ++ prefixes b

/-- The original setting bounds total length and word size. The lists themselves
may be empty; zero values are allowed as a declared harmless generalization. -/
def MergeInstance (m n : ℕ) (a b : List ℕ) : Prop :=
  2 ≤ m ∧ m ≤ n ∧ a.length + b.length ≤ m ∧ (a ++ b).sum ≤ n ∧
    a.Pairwise (· ≤ ·) ∧ b.Pairwise (· ≤ ·)

end HuffmanMPC.Main.Supplement


