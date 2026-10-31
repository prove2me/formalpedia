-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_dualFeasible88
-- name    : CombOpt_MatroidIntersectionPolytope_dualFeasible88
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:33.783199+00:00
-- url     : https://prove2.me/theorems/a82e18a1-2001-4f63-84a3-dfb1fc6e759c
-- title:
--   Feasible set of the dual (8.8) of the intersection program
-- statement:
--   The dual of maximizing $c^Tx$ subject to (8.7) is (8.8): minimize $\sum_{A\subseteq S}\big(r_1(A)y^1_A+r_2(A)y^2_A\big)$ subject to
--
--   $$
--   \sum\big(y^1_A+y^2_A : A\subseteq S,\ e\in A\big)\ge c_e\ \text{ for all } e\in S,\qquad y^1_A,\ y^2_A\ge0\ \text{ for all } A\subseteq S.
--   $$
--
--   This definition is the set of feasible pairs $(y^1,y^2)$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.5, (8.8), pp. 298–299 (PDF pp. 305–306)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_coverSum

namespace CombOpt.MatroidIntersectionPolytope

/-- **Feasible set of the dual (8.8) of the matroid intersection linear program.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.5, (8.8), pp. 298–299 (PDF pp. 305–306): "Minimize Σ(r₁(A) y¹_A + r₂(A) y²_A : A ⊆ S)
subject to Σ(y¹_A + y²_A : A ⊆ S, e ∈ A) ≥ c_e, for all e ∈ S; y¹_A, y²_A ≥ 0, for all A ⊆ S."

`dualFeasible88 c` is the set of pairs `(y¹, y²)` of vectors indexed by the subsets of `S` with
`y¹, y² ≥ 0` and `Σ_{A ∋ e} (y¹_A + y²_A) ≥ c_e` for every `e ∈ S`. -/
def dualFeasible88 {S : Type*} [Fintype S] [DecidableEq S] (c : S → ℝ) :
    Set ((Finset S → ℝ) × (Finset S → ℝ)) :=
  {y | (∀ A, 0 ≤ y.1 A) ∧ (∀ A, 0 ≤ y.2 A) ∧ ∀ e, c e ≤ coverSum y.1 e + coverSum y.2 e}

end CombOpt.MatroidIntersectionPolytope


