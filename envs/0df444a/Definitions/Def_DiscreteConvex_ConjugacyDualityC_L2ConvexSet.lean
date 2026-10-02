-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2ConvexSet
-- name    : DiscreteConvex_ConjugacyDualityC_L2ConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:42:08.174664+00:00
-- url     : https://prove2.me/theorems/4137defb-55a6-499e-b732-9907c0de0b68
-- title:
--   L2ConvexSet
-- statement:
--   $D$ is L2-convex: the Minkowski sum of two L-convex sets.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229, set analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229, set analogue

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LConvexSet

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `D` is L2-convex: the Minkowski sum of two L-convex sets. -/
def L2ConvexSet (D : Set (V → ℤ)) : Prop :=
  ∃ D1 D2 : Set (V → ℤ), LConvexSet D1 ∧ LConvexSet D2 ∧ D = D1 + D2

end DiscreteConvex.ConjugacyDualityC


