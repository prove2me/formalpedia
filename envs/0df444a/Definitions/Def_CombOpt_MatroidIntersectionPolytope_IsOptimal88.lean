-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsOptimal88
-- name    : CombOpt_MatroidIntersectionPolytope_IsOptimal88
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:41:44.896666+00:00
-- url     : https://prove2.me/theorems/95b97455-971d-43d1-a18f-04ec5944e1e3
-- title:
--   Optimal solution of (8.8)
-- statement:
--   A pair $(y^1,y^2)$ is **optimal for (8.8)** if it is feasible for (8.8) and
--
--   $$
--   \sum_{A\subseteq S}\big(r_1(A)y^1_A+r_2(A)y^2_A\big)\le\sum_{A\subseteq S}\big(r_1(A)y'^1_A+r_2(A)y'^2_A\big)
--   $$
--
--   for every feasible pair $(y'^1,y'^2)$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.5, (8.8), pp. 298–299 (PDF pp. 305–306)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_rank
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_dualFeasible88

namespace CombOpt.MatroidIntersectionPolytope

/-- **Optimal solution of (8.8).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.5, (8.8), pp. 298–299 (PDF pp. 305–306).

`IsOptimal88 M₁ M₂ c y` holds when `y = (y¹, y²)` is feasible for (8.8) and its objective
`Σ_A (r₁(A) y¹_A + r₂(A) y²_A)` is at most that of every feasible pair. -/
def IsOptimal88 {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : FinMatroid S) (c : S → ℝ)
    (y : (Finset S → ℝ) × (Finset S → ℝ)) : Prop :=
  y ∈ dualFeasible88 c ∧
    ∀ y' ∈ dualFeasible88 c,
      ∑ A, ((rank M₁ A : ℝ) * y.1 A + (rank M₂ A : ℝ) * y.2 A) ≤
        ∑ A, ((rank M₁ A : ℝ) * y'.1 A + (rank M₂ A : ℝ) * y'.2 A)

end CombOpt.MatroidIntersectionPolytope


