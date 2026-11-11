-- Prove2me | Definitions.Def_UnequalHuffman_NPC_LocalConstruction
-- name    : UnequalHuffman_NPC_LocalConstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:43:35.70718+00:00
-- url     : https://prove2.me/theorems/e08f540f-1b44-4193-b41d-99855a5d79f6
-- title:
--   Local constructions on integer coordinate multisets: the child map E, sequences with prescribed leaf counts, sorted leaves, interval satisfaction, score
-- statement:
--   For a multiset $X$ of integer coordinates, $E(X)$ contains $z$ and $z+1$ for every occurrence of $z$ in $X$ (repetitions retained).
--
--   A $d$-level **local construction** (Appendix A.2) is given by leaf data (`LeafData`): for each level $j = 1,\dots,d$ the list of its leaves in sorted rank order, leaf $k$ carrying a permitted interval $[\ell_{j,k}, r_{j,k}]$ and a score coefficient $e_{j,k}$, coded as the triple $(\ell, r, e)$; the number of leaves at level $j$ is the length of the list.
--
--   A **sequence** from a starting multiset $X_0$ (`IsSeq D X0 X`, with `X : Fin (d+1) → Multiset ℤ`) satisfies $X_0 = $ the start, $X_j \subseteq E(X_{j-1})$ (multiset inclusion) and $|E(X_{j-1}) - X_j|$ equal to the prescribed number of leaves at level $j$; the final $X_d$ is unrestricted. Its leaves at level $j$ are $L_j = E(X_{j-1}) - X_j$ sorted nondecreasingly (`levelLeaves`). It **satisfies the intervals** if the $k$-th sorted leaf of $L_j$ lies in $[\ell_{j,k}, r_{j,k}]$ for all $j,k$; it is **feasible** (complete) if it has the prescribed counts and satisfies the intervals. Its **score** is $\sum_j\sum_k e_{j,k}\cdot(k\text{-th sorted leaf of } L_j)$. Coordinates are integers and may be negative.
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 8 (E(X)), p. 40, Appendix A.2 (local constructions)

import Mathlib

set_option autoImplicit false

namespace UnequalHuffman.NPC

/-- `E(X)`: the multiset containing `z` and `z + 1` for every occurrence of `z` in `X` (the
coordinates of the children of internal vertices with coordinates `X`). Coordinates are integers
(local constructions are described relative to a base and may use negative coordinates). -/
def E (X : Multiset ℤ) : Multiset ℤ := X + X.map (· + 1)

/-- The leaf data of a `d`-level local construction (Appendix A.2): for each level `j = 1, …, d`
(list index `j - 1`), the list of its leaves in sorted rank order, leaf `k` carrying its permitted
interval `[ℓ_{j,k}, r_{j,k}]` and its score coefficient `e_{j,k}` as the triple `(ℓ, r, e)`. The
number of leaves at level `j` is the length of its list. -/
abbrev LeafData : Type := List (List (ℤ × ℤ × ℤ))

namespace LeafData

/-- The leaf coordinates at level `j + 1` of a sequence `X₀, …, X_d` of coordinate multisets:
`L_{j+1} = E(X_j) - X_{j+1}`, sorted nondecreasingly with repetitions. -/
def levelLeaves (D : LeafData) (X : Fin (D.length + 1) → Multiset ℤ) (j : Fin D.length) :
    List ℤ :=
  Multiset.sort (E (X j.castSucc) - X j.succ)

/-- `X₀, …, X_d` is a sequence of coordinate multisets of the construction starting from `X0`
with its prescribed leaf counts: `X₀ = X0`, `X_j ⊆ E(X_{j-1})` (multiset inclusion), and
`|E(X_{j-1}) - X_j|` is the prescribed number of leaves at level `j`. The final `X_d` is
unrestricted. -/
def IsSeq (D : LeafData) (X0 : Multiset ℤ) (X : Fin (D.length + 1) → Multiset ℤ) : Prop :=
  X 0 = X0 ∧ ∀ j : Fin D.length,
    X j.succ ≤ E (X j.castSucc) ∧
    Multiset.card (E (X j.castSucc) - X j.succ) = (D.get j).length

/-- The sequence satisfies the leaf intervals: at every level the `k`-th sorted leaf lies in
`[ℓ_{j,k}, r_{j,k}]`. -/
def SatisfiesIntervals (D : LeafData) (X : Fin (D.length + 1) → Multiset ℤ) : Prop :=
  ∀ j : Fin D.length,
    List.Forall₂ (fun (p : ℤ × ℤ × ℤ) (z : ℤ) => p.1 ≤ z ∧ z ≤ p.2.1) (D.get j)
      (D.levelLeaves X j)

/-- A feasible (complete) sequence: prescribed leaf counts and leaf intervals. -/
def IsFeasibleSeq (D : LeafData) (X0 : Multiset ℤ) (X : Fin (D.length + 1) → Multiset ℤ) :
    Prop :=
  D.IsSeq X0 X ∧ D.SatisfiesIntervals X

/-- The score `∑_j ∑_k e_{j,k} · (k-th sorted leaf of L_j)` of a sequence. -/
def score (D : LeafData) (X : Fin (D.length + 1) → Multiset ℤ) : ℤ :=
  ∑ j : Fin D.length,
    (List.zipWith (fun (p : ℤ × ℤ × ℤ) (z : ℤ) => p.2.2 * z) (D.get j) (D.levelLeaves X j)).sum

end LeafData

end UnequalHuffman.NPC


