-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_M2ConvexSet
-- name    : DiscreteConvex_ConjugacyDualityC_M2ConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:43:25.364195+00:00
-- url     : https://prove2.me/theorems/f9645fa4-84b7-46b3-b241-5051bb7741ef
-- title:
--   M2ConvexSet
-- statement:
--   $D$ is M2-convex: the intersection of two M-convex sets.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226, set analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226, set analogue

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ExchangeAxiomB

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `D` is M2-convex: the intersection of two M-convex sets. -/
def M2ConvexSet (D : Set (V → ℤ)) : Prop :=
  ∃ D1 D2 : Set (V → ℤ), ExchangeAxiomB D1 ∧ ExchangeAxiomB D2 ∧ D = D1 ∩ D2

end DiscreteConvex.ConjugacyDualityC


