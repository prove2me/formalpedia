-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_coverSum
-- name    : CombOpt_MatroidIntersectionPolytope_coverSum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:39:52.099487+00:00
-- url     : https://prove2.me/theorems/9d7590d3-3ee7-4c26-8731-b254d695d6a9
-- title:
--   Coverage $\sum(y_A : A\subseteq S,\ e\in A)$ of an element
-- statement:
--   For a vector $y=(y_A)_{A\subseteq S}$ indexed by the subsets of $S$ and an element $e\in S$, this is the sum
--
--   $$
--   \sum\big(y_A : A\subseteq S,\ e\in A\big).
--   $$
--
--   It is the left-hand side of the constraint for $e$ in the dual programs (8.2) and (8.8), and it defines the first part $c^1_e=\sum(\bar y^1_A : e\in A)$ of the weight splitting in §8.5.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, (8.2), p. 279 (PDF p. 286); §8.5, p. 299 (PDF p. 306)

import Mathlib

namespace CombOpt.MatroidIntersectionPolytope

/-- **Coverage of an element by a dual vector**: for `y ∈ ℝ^{2^S}` (one entry `y_A` per subset
`A ⊆ S`) and `e ∈ S`, the sum `Σ(y_A : A ⊆ S, e ∈ A)`.
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, (8.2), p. 279 (PDF p. 286), and §8.5, p. 299 (PDF p. 306), where
`c¹_e = Σ(ȳ¹(A) : A ⊆ S, e ∈ A)`. -/
def coverSum {S : Type*} [Fintype S] [DecidableEq S] (y : Finset S → ℝ) (e : S) : ℝ :=
  ∑ A ∈ Finset.univ.filter (fun A : Finset S => e ∈ A), y A

end CombOpt.MatroidIntersectionPolytope


