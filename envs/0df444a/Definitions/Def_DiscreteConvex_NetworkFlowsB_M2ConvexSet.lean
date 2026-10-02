-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_M2ConvexSet
-- name    : DiscreteConvex_NetworkFlowsB_M2ConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:25:25.79456+00:00
-- url     : https://prove2.me/theorems/4b712057-4ab6-4026-8f54-44c3306ac4ee
-- title:
--   M2ConvexSet
-- statement:
--   $D$ is M2-convex: the intersection of two M-convex sets.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_ExchangeAxiomB

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `D` is M2-convex: the intersection of two M-convex sets. -/
def M2ConvexSet (D : Set (V → ℤ)) : Prop :=
  ∃ D1 D2 : Set (V → ℤ), ExchangeAxiomB D1 ∧ ExchangeAxiomB D2 ∧ D = D1 ∩ D2

end DiscreteConvex.NetworkFlowsB


