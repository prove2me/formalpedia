-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNat2ConvexSet
-- name    : DiscreteConvex_ConjugacyDualityB_MNat2ConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:34:31.910993+00:00
-- url     : https://prove2.me/theorems/4ac1bb5d-4852-4718-b062-1d789ef4ea93
-- title:
--   MNat2ConvexSet
-- statement:
--   $D$ is M$^\natural_2$-convex: the intersection of two M$^\natural$-convex sets.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226, set analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.226, set analogue

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNatConvexSet

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `D` is M♮₂-convex: the intersection of two M♮-convex sets. -/
def MNat2ConvexSet (D : Set (V → ℤ)) : Prop :=
  ∃ D1 D2 : Set (V → ℤ), MNatConvexSet D1 ∧ MNatConvexSet D2 ∧ D = D1 ∩ D2

end DiscreteConvex.ConjugacyDualityB


