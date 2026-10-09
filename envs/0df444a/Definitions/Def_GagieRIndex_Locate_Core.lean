-- Prove2me | Definitions.Def_GagieRIndex_Locate_Core
-- name    : GagieRIndex_Locate_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:19:27.851077+00:00
-- url     : https://prove2.me/theorems/4b4d05ac-0ebc-48dc-bea3-625b33da53a9
-- title:
--   §2 and Definition 1, pp. 7–11 — text, suffix array, ISA, BWT, LF, runs and sampled positions
-- statement:
--   The paper works with a text $T[1..n]$ over the ordered alphabet $[1..\sigma]$. Its last symbol is the unique terminator $\$=1$, the alphabet's smallest symbol. The **suffix array** $SA[1..n]$ is a permutation of the starting positions $[1..n]$ that lists the suffixes $T[i..n]$ in strictly increasing lexicographic order, and the **inverse suffix array** $ISA$ sends a text position $i$ to the $p$ with $SA[p]=i$.
--
--   The **Burrows–Wheeler transform** records the symbol immediately before each sorted suffix, treating the predecessor of $T[1]$ as $T[n]$. The **LF mapping** is computed from symbol counts:
--   $$BWT[p]=\begin{cases}T[n],&SA[p]=1,\\T[SA[p]-1],&SA[p]>1,\end{cases}\qquad LF(p)=C[BWT[p]]+\operatorname{rank}[p].$$
--   Here $C[c]$ counts the BWT symbols smaller than $c$, and $\operatorname{rank}[p]$ counts the copies of $BWT[p]$ in $BWT[1..p]$.
--
--   A **BWT run** is a maximal block of consecutive equal symbols. A run start is a position $p$ with $p=1$ or $BWT[p]\ne BWT[p-1]$, a run end is a position $p$ with $p=n$ or $BWT[p+1]\ne BWT[p]$, and $r$ is the number of runs. A text position is **sampled** when its character is the first or last BWT character in its run (Definition 1). These objects are the shared combinatorial setting of the mission.
--
--   **Formalization Note** Positions are 1-based natural numbers. $T$ and $SA$ are functions read only on $[1..n]$; $SA$ is specified by a sorting and permutation predicate, not constructed. The symbol $\$=1$ is unique. At the wrapped predecessor, $T[0]$ means $T[n]$, so the text position of $BWT[p]$ is $SA[p]-1$, or $n$ when $SA[p]=1$. $ISA[i]$ is $0$ when no $p\in[1..n]$ has $SA[p]=i$. The sampled set follows the first sentence of Definition 1; its explanatory "That is" clause omits the last character of the final run. The same Core text is deliberately duplicated across the three missions of this paper for later consolidation.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, pp. 7–11, §2 and Definition 1

import Mathlib

namespace GagieRIndex.Locate

/-- The suffix `T[i..n]` of a text `T[1..n]`, as the list `[T i, T (i+1), …, T n]`
(arXiv:1809.02792v2, §2, p. 7). Positions are 1-based, as in the paper; `T` is read only on `[1..n]`. -/
def suffix (n : ℕ) (T : ℕ → ℕ) (i : ℕ) : List ℕ :=
  (List.range (n + 1 - i)).map (fun k => T (i + k))

/-- `T[1..n]` is a text over the alphabet `[1..σ]` terminated by the special symbol `$ = 1`, the
lexicographically smallest one, which appears only at `T[n]` (§2, p. 7). -/
def IsText (n σ : ℕ) (T : ℕ → ℕ) : Prop :=
  1 ≤ n ∧ (∀ i, 1 ≤ i → i ≤ n → 1 ≤ T i ∧ T i ≤ σ) ∧ T n = 1 ∧ ∀ i, 1 ≤ i → i < n → T i ≠ 1

/-- `SA[1..n]` is the suffix array of `T[1..n]`: a permutation of `[1..n]` such that for all
`1 ≤ p < n` the suffix `T[SA[p]..]` is lexicographically smaller than `T[SA[p+1]..]` (§2.1, p. 7). -/
def IsSuffixArray (n : ℕ) (T : ℕ → ℕ) (SA : ℕ → ℕ) : Prop :=
  (∀ p, 1 ≤ p → p ≤ n → 1 ≤ SA p ∧ SA p ≤ n) ∧ Set.InjOn SA (Set.Icc 1 n) ∧
  ∀ p, 1 ≤ p → p < n → suffix n T (SA p) < suffix n T (SA (p + 1))

/-- The inverse suffix array: `ISA[i]` is the `p ∈ [1..n]` with `SA[p] = i` (§2.1, p. 7);
`0` if there is none. -/
def ISA (n : ℕ) (SA : ℕ → ℕ) (i : ℕ) : ℕ :=
  ((List.range' 1 n).find? (fun p => SA p == i)).getD 0

/-- `BWT[p] = T[SA[p] − 1]` if `SA[p] > 1`, and `BWT[p] = T[n] = $` if `SA[p] = 1` (§2.3, p. 8). -/
def bwt (n : ℕ) (T SA : ℕ → ℕ) (p : ℕ) : ℕ :=
  if SA p = 1 then T n else T (SA p - 1)

/-- The text position of the character `BWT[p]`: `SA[p] − 1`, or `n` when `SA[p] = 1`
(§2.3, p. 8; Definition 1, p. 11). -/
def textPos (n : ℕ) (SA : ℕ → ℕ) (p : ℕ) : ℕ :=
  if SA p = 1 then n else SA p - 1

/-- `C[c]`, the number of occurrences of symbols less than `c` in `L = BWT` (§2.3, p. 8). -/
def Ccount (n : ℕ) (T SA : ℕ → ℕ) (c : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun p => bwt n T SA p < c)).card

/-- `rank[p]`, the number of occurrences of the symbol `L[p]` in `L[1..p]` (§2.3, p. 8). -/
def rank (n : ℕ) (T SA : ℕ → ℕ) (p : ℕ) : ℕ :=
  ((Finset.Icc 1 p).filter (fun p' => bwt n T SA p' = bwt n T SA p)).card

/-- The LF mapping `LF(p) = C[c] + rank[p]` with `c = L[p]` (§2.3, p. 8). -/
def LF (n : ℕ) (T SA : ℕ → ℕ) (p : ℕ) : ℕ :=
  Ccount n T SA (bwt n T SA p) + rank n T SA p

/-- `p ∈ [1..n]` is the first position of a run of `BWT`: `p = 1` or `BWT[p] ≠ BWT[p − 1]`
(the run heads `E` of §2.5, p. 9). -/
def IsRunStart (n : ℕ) (T SA : ℕ → ℕ) (p : ℕ) : Prop :=
  1 ≤ p ∧ p ≤ n ∧ (p = 1 ∨ bwt n T SA (p - 1) ≠ bwt n T SA p)

/-- `p ∈ [1..n]` is the last position of a run of `BWT`: `p = n` or `BWT[p + 1] ≠ BWT[p]`. -/
def IsRunEnd (n : ℕ) (T SA : ℕ → ℕ) (p : ℕ) : Prop :=
  1 ≤ p ∧ p ≤ n ∧ (p = n ∨ bwt n T SA (p + 1) ≠ bwt n T SA p)

instance (n : ℕ) (T SA : ℕ → ℕ) : DecidablePred (IsRunStart n T SA) := fun _ => by
  unfold IsRunStart; infer_instance

instance (n : ℕ) (T SA : ℕ → ℕ) : DecidablePred (IsRunEnd n T SA) := fun _ => by
  unfold IsRunEnd; infer_instance

/-- `r`, the number of runs (maximal substrings formed by a single symbol) of `BWT`
(§1.1, p. 3; §2.5, p. 9). -/
def runs (n : ℕ) (T SA : ℕ → ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (IsRunStart n T SA)).card

/-- The sampled text positions: `T[i]` is sampled iff it is the first or last character in its
BWT run (Definition 1, p. 11). -/
def sampled (n : ℕ) (T SA : ℕ → ℕ) : Finset ℕ :=
  ((Finset.Icc 1 n).filter (fun p => IsRunStart n T SA p ∨ IsRunEnd n T SA p)).image (textPos n SA)

end GagieRIndex.Locate


