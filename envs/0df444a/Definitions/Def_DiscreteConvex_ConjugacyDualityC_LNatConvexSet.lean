-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNatConvexSet
-- name    : DiscreteConvex_ConjugacyDualityC_LNatConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:42:12.821594+00:00
-- url     : https://prove2.me/theorems/3a0f6556-a8dc-4d6c-a87b-540263912cd8
-- title:
--   LNatConvexSet
-- statement:
--   $D$ is L$^\natural$-convex: its lift is an L-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, set analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, set analogue

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LiftedSetL

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `D` is L♮-convex: its lift is an L-convex set. -/
def LNatConvexSet (D : Set (V → ℤ)) : Prop := LConvexSet (LiftedSetL D)

end DiscreteConvex.ConjugacyDualityC


