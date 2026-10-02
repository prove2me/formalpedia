-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsMNaturalConvexSet
-- name    : DiscreteConvex_EconomicEquilibriumB_IsMNaturalConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:55:50.394164+00:00
-- url     : https://prove2.me/theorems/a788d05c-3d88-40a7-87ea-a93229a05b8b
-- title:
--   IsMNaturalConvexSet
-- statement:
--   $Q\subseteq\mathbb Z^K$ is an M$^\natural$-convex set: the projection along a new coordinate of an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.117, Eq. (4.35), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.117, Eq. (4.35), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ExchangeAxiomB

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `Q ⊆ Zᴷ` is an M♮-convex set: the projection along a new coordinate of an M-convex set. -/
def IsMNaturalConvexSet (Q : Set (K → ℤ)) : Prop :=
  ∃ B : Set (Option K → ℤ), ExchangeAxiomB B ∧
    Q = {x : K → ℤ | ∃ x0 : ℤ, (fun w : Option K => w.elim x0 x) ∈ B}

-- ===== Concave/convex closures and the derived continuous economy (§11.4) =====

end DiscreteConvex.EconomicEquilibriumB


