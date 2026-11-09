-- Prove2me | Definitions.Def_CentralStrQ_Strings
-- name    : CentralStrQ_Strings
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:20:51.014246+00:00
-- url     : https://prove2.me/theorems/b3c86c2f-d148-4b31-826b-a0c5f4cd9300
-- title:
--   Suffixes, LCE, suffix array, inverse suffix array, LCP and PLCP arrays
-- statement:
--   Let $T\in\Sigma^n$ be a string over a linearly ordered alphabet; positions are $1,\dots,n$. Write $T[i\,.\,.\,j)$ for the factor $T[i]\cdots T[j-1]$ and $T[j\,.\,.\,n]$ for the suffix starting at $j$. Strings are compared lexicographically: $U\preceq V$ if $U$ is a prefix of $V$ or $U$ is smaller at the first position where they differ. Let $\mathrm{lcp}(U,V)$ be the length of the longest common prefix.
--
--   1. $\mathrm{LCE}_T(i,j)=\mathrm{lcp}(T[i\,.\,.\,n],T[j\,.\,.\,n])$ (Definition 3.8).
--   2. $\mathrm{RangeBeg}(P,T)=|\{j\in[1\,.\,.\,n]: T[j\,.\,.\,n]\prec P\}|$ (Definition 3.1).
--   3. The inverse suffix array $\mathrm{SA}^{-1}_T[j]=1+\mathrm{RangeBeg}(T[j\,.\,.\,n],T)$, the lexicographic rank of the suffix at $j$ (Definition 3.12).
--   4. The suffix array $\mathrm{SA}_T[i]$ is the starting position of the $i$-th smallest nonempty suffix, that is, the $j$ with $\mathrm{SA}^{-1}_T[j]=i$ (Definition 3.11).
--   5. $\mathrm{LCP}_T[1]=0$ and $\mathrm{LCP}_T[i]=\mathrm{LCE}_T(\mathrm{SA}_T[i-1],\mathrm{SA}_T[i])$ for $i\in(1\,.\,.\,n]$; $\mathrm{PLCP}_T[j]=\mathrm{LCP}_T[\mathrm{SA}^{-1}_T[j]]$ (Definition 3.13).
--   6. $\mathrm{increase}_\delta(S)$ adds $\delta$ to every symbol of $S\in[0\,.\,.\,\sigma)^*$ (Definition 4.8).
--
--   $\mathrm{PLCP}_T[j]$ is thus the length of the longest common prefix of the suffix at $j$ and its lexicographic predecessor, and $0$ for the smallest suffix. These arrays are the central objects of the paper; the PLCP array is what the PLCP bitvector encodes.
--
--   **Formalization Note** Strings are lists over a type with a linear order; Lean's lexicographic order on lists is the order $\preceq$ above. Positions are 1-based. For $i\notin[1\,.\,.\,n]$ the suffix array returns $0$ and the other arrays junk values; no statement uses them there.
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Section 3.1 and Definition 3.1, p.13 (PDF p.14); Definition 3.8, p.15 (PDF p.16); Definitions 3.11–3.13, p.16 (PDF p.17); Definition 4.8, p.25 (PDF p.26)

import Mathlib

set_option autoImplicit false

namespace CentralStrQ

/-!
# Strings, suffix arrays, LCP and PLCP arrays (Sections 3.1, 3.4, 3.5; Definition 4.8)

Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*,
STOC 2027 submission (manuscript sha256 dea2f74f…c96f346): Section 3.1 and Definition 3.1,
p.13 (PDF p.14); Definition 3.8, p.15 (PDF p.16); Definitions 3.11–3.13, p.16 (PDF p.17);
Definition 4.8, p.25 (PDF p.26).

**Formalization Note.** A string over an ordered alphabet `Σ` is a `List α` with `[LinearOrder α]`.
Positions are **1-based** as in the paper: `T[i]` is entry `i − 1` of the list.
`factor T i j = T[i..j)` (empty if `j ≤ i`), `suffix T j = T[j..|T|]`. The order `≺` on `Σ*` is
Lean's lexicographic order on lists (`U ≺ V` iff `U` is a proper prefix of `V` or they first
differ at a smaller symbol), which is the order of p.13. `SA⁻¹_T[j] = 1 + RangeBeg(T[j..n], T)`
(Definition 3.12), and `SA_T[i]` is the `j ∈ [1..n]` with `SA⁻¹_T[j] = i` (`0` if none; for
`i ∈ [1..n]` there is exactly one since the suffixes are pairwise distinct). `LCP_T[1] = 0` and
`PLCP_T[j] = LCP_T[SA⁻¹_T[j]]`. Values outside `[1..n]` are junk and never used.
-/

variable {α : Type} [LinearOrder α]

/-- `T[i..j)` (1-based; empty when `j ≤ i`). -/
def factor (T : List α) (i j : ℕ) : List α := (T.drop (i - 1)).take (j - i)

/-- The suffix `T[j..|T|]` (1-based; `j = |T| + 1` gives the empty suffix). -/
def suffix (T : List α) (j : ℕ) : List α := T.drop (j - 1)

/-- `lcp(U, V)`, the length of the longest common prefix. -/
def lcp : List α → List α → ℕ
  | a :: as, b :: bs => if a = b then lcp as bs + 1 else 0
  | _, _ => 0

/-- `LCE_T(i, j) = lcp(T[i..|T|], T[j..|T|])` (Definition 3.8). -/
def LCE (T : List α) (i j : ℕ) : ℕ := lcp (suffix T i) (suffix T j)

/-- `RangeBeg(P, T) = |{j ∈ [1..|T|] : T[j..|T|] ≺ P}|` (Definition 3.1). -/
def rangeBeg (P T : List α) : ℕ :=
  ((Finset.Icc 1 T.length).filter fun j => suffix T j < P).card

/-- The inverse suffix array `SA⁻¹_T[j] = 1 + RangeBeg(T[j..n], T)` (Definition 3.12). -/
def ISA (T : List α) (j : ℕ) : ℕ := 1 + rangeBeg (suffix T j) T

/-- The suffix array: `SA_T[i]` is the starting position of the lexicographically `i`-th
nonempty suffix (Definition 3.11). -/
def SA (T : List α) (i : ℕ) : ℕ :=
  ((List.range' 1 T.length).find? fun j => ISA T j == i).getD 0

/-- `LCP_T[1] = 0`, `LCP_T[i] = LCE_T(SA_T[i−1], SA_T[i])` for `i ∈ (1..n]` (Definition 3.13). -/
def LCP (T : List α) (i : ℕ) : ℕ := if i ≤ 1 then 0 else LCE T (SA T (i - 1)) (SA T i)

/-- `PLCP_T[j] = LCP_T[SA⁻¹_T[j]]` (Definition 3.13). -/
def PLCP (T : List α) (j : ℕ) : ℕ := LCP T (ISA T j)

/-- `increase_δ(S)`: add `δ` to every symbol (Definition 4.8). -/
def increase (δ : ℕ) (S : List ℕ) : List ℕ := S.map (· + δ)

end CentralStrQ


