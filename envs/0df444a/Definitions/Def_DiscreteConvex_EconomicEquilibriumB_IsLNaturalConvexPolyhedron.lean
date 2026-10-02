-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsLNaturalConvexPolyhedron
-- name    : DiscreteConvex_EconomicEquilibriumB_IsLNaturalConvexPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:43:58.530621+00:00
-- url     : https://prove2.me/theorems/536acab4-658f-47f2-a72f-45e8af7aade2
-- title:
--   IsLNaturalConvexPolyhedron
-- statement:
--   $P\subseteq\mathbb R^K$ is an L$^\natural$-convex polyhedron.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.131, axiom (SBS$^\\natural$[R]), Eq. (5.20), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.131, axiom (SBS$^\\natural$[R]), Eq. (5.20), redeclared

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `P ⊆ Rᴷ` is an L♮-convex polyhedron (axiom (SBS♮[R]), Eq. (5.20)). -/
def IsLNaturalConvexPolyhedron (P : Set (K → ℝ)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ∀ alpha : ℝ, 0 ≤ alpha →
    (fun k => max (p k - alpha) (q k)) ∈ P ∧ (fun k => min (p k) (q k + alpha)) ∈ P

end DiscreteConvex.EconomicEquilibriumB


