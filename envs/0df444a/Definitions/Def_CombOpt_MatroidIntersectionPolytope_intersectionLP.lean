-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_intersectionLP
-- name    : CombOpt_MatroidIntersectionPolytope_intersectionLP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:41:37.02148+00:00
-- url     : https://prove2.me/theorems/1820f56f-6140-4bd9-8a0e-336eff7b8512
-- title:
--   Feasible set of the matroid intersection system (8.7)
-- statement:
--   Let $M_1=(S,\mathcal I_1)$ and $M_2=(S,\mathcal I_2)$ be matroids on the same finite set $S$ with rank functions $r_1,r_2$. The system (8.7) is
--
--   $$
--   x(A)\le r_1(A),\quad x(A)\le r_2(A)\quad\text{for all } A\subseteq S,\qquad x_e\ge0\ \text{ for all } e\in S,
--   $$
--
--   with $x(A)=\sum_{e\in A}x_e$. This definition is its set of feasible solutions in $\mathbb R^S$. The characteristic vector of every common independent set is feasible, and Edmonds' theorem says these vectors span exactly this set.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.5, (8.7), pp. 297–298 (PDF pp. 304–305)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_rank

namespace CombOpt.MatroidIntersectionPolytope

/-- **Feasible set of the matroid intersection system (8.7).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.5, (8.7), pp. 297–298 (PDF pp. 304–305): for matroids `M₁ = (S, I₁)` and
`M₂ = (S, I₂)` with rank functions `r₁, r₂`,
"x(A) ≤ r₁(A), for all A ⊆ S; x(A) ≤ r₂(A), for all A ⊆ S; x_e ≥ 0, for all e ∈ S."

`intersectionLP M₁ M₂` is the set of `x ∈ ℝ^S` satisfying (8.7), with `x(A) = Σ_{e∈A} x_e`. -/
def intersectionLP {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : FinMatroid S) :
    Set (S → ℝ) :=
  {x | (∀ A : Finset S, ∑ e ∈ A, x e ≤ (rank M₁ A : ℝ)) ∧
       (∀ A : Finset S, ∑ e ∈ A, x e ≤ (rank M₂ A : ℝ)) ∧ ∀ e, 0 ≤ x e}

end CombOpt.MatroidIntersectionPolytope


