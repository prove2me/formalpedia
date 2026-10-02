-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_M2ConvexSet
-- name    : DiscreteConvex_ConjugacyDualityB_M2ConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:33:23.139324+00:00
-- url     : https://prove2.me/theorems/f5b07658-8b46-4506-84d8-3f532380b1b8
-- title:
--   M2ConvexSet
-- statement:
--   $D$ is M2-convex: the intersection of two M-convex sets.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226, set analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226, set analogue

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ExchangeAxiomB

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `D` is M2-convex: the intersection of two M-convex sets. -/
def M2ConvexSet (D : Set (V → ℤ)) : Prop :=
  ∃ D1 D2 : Set (V → ℤ), ExchangeAxiomB D1 ∧ ExchangeAxiomB D2 ∧ D = D1 ∩ D2

end DiscreteConvex.ConjugacyDualityB


