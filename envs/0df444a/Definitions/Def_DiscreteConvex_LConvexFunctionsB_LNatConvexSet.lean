-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNatConvexSet
-- name    : DiscreteConvex_LConvexFunctionsB_LNatConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:22:12.864986+00:00
-- url     : https://prove2.me/theorems/03a2745c-4520-440a-9ac5-2d0be001f666
-- title:
--   LNatConvexSet
-- statement:
--   $D$ is L$^\natural$-convex: its lift is an L-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, set analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, set analogue

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LiftedSetL

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `D` is L♮-convex: its lift is an L-convex set. -/
def LNatConvexSet (D : Set (V → ℤ)) : Prop := LConvexSet (LiftedSetL D)

end DiscreteConvex.LConvexFunctionsB


