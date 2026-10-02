-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2ConvexSet
-- name    : DiscreteConvex_ConjugacyDualityC_LNat2ConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:43:52.018754+00:00
-- url     : https://prove2.me/theorems/c70588e0-b161-499c-9cc3-456581ae4019
-- title:
--   LNat2ConvexSet
-- statement:
--   $D$ is L$^\natural_2$-convex: the Minkowski sum of two L$^\natural$-convex sets.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229, set analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.229, set analogue

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNatConvexSet

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `D` is L♮₂-convex: the Minkowski sum of two L♮-convex sets. -/
def LNat2ConvexSet (D : Set (V → ℤ)) : Prop :=
  ∃ D1 D2 : Set (V → ℤ), LNatConvexSet D1 ∧ LNatConvexSet D2 ∧ D = D1 + D2

end DiscreteConvex.ConjugacyDualityC


