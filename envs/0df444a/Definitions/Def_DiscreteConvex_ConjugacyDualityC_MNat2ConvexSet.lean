-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_MNat2ConvexSet
-- name    : DiscreteConvex_ConjugacyDualityC_MNat2ConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:44:59.342014+00:00
-- url     : https://prove2.me/theorems/62d985f0-0b6f-4c20-873c-730d3bd6586e
-- title:
--   MNat2ConvexSet
-- statement:
--   $D$ is M$^\natural_2$-convex: the intersection of two M$^\natural$-convex sets.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226, set analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226, set analogue

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_MNatConvexSet

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `D` is M♮₂-convex: the intersection of two M♮-convex sets. -/
def MNat2ConvexSet (D : Set (V → ℤ)) : Prop :=
  ∃ D1 D2 : Set (V → ℤ), MNatConvexSet D1 ∧ MNatConvexSet D2 ∧ D = D1 ∩ D2

end DiscreteConvex.ConjugacyDualityC


