-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsOptimal82
-- name    : CombOpt_MatroidIntersectionPolytope_IsOptimal82
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:41:37.197726+00:00
-- url     : https://prove2.me/theorems/744275ac-4ff4-4849-b270-a4d5365718be
-- title:
--   Optimal solution of (8.2) for $(M,c)$
-- statement:
--   A vector $y\in\mathbb R^{2^S}$ is **optimal for (8.2)** for the matroid $M$ with rank function $r$ and weights $c$ if it is feasible for (8.2) and
--
--   $$
--   \sum_{A\subseteq S}r(A)y_A\le\sum_{A\subseteq S}r(A)y'_A
--   $$
--
--   for every feasible $y'$. In §8.5, "Problem $i$" is (8.2) with $M$ replaced by $M_i$ and $c$ by $c^i$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, (8.2), p. 279 (PDF p. 286); §8.5, p. 299 (PDF p. 306)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_rank
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_dualFeasible82

namespace CombOpt.MatroidIntersectionPolytope

/-- **Optimal solution of the dual matroid linear program (8.2)** for matroid `M` and weights `c`.
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, (8.2), p. 279 (PDF p. 286): minimize `Σ(r(A) y_A : A ⊆ S)` over the feasible set of
(8.2). "Problem i" of §8.5 (p. 299) is `IsOptimal82 M_i c^i`.

`IsOptimal82 M c y` holds when `y` is feasible for (8.2) and its objective
`Σ_A r(A) y_A` is at most that of every feasible `y'`. -/
def IsOptimal82 {S : Type*} [Fintype S] [DecidableEq S] (M : FinMatroid S) (c : S → ℝ)
    (y : Finset S → ℝ) : Prop :=
  y ∈ dualFeasible82 c ∧
    ∀ y' ∈ dualFeasible82 c, ∑ A, (rank M A : ℝ) * y A ≤ ∑ A, (rank M A : ℝ) * y' A

end CombOpt.MatroidIntersectionPolytope


