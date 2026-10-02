-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNatConvexSet
-- name    : DiscreteConvex_LConvexFunctionsC_LNatConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:34:36.181901+00:00
-- url     : https://prove2.me/theorems/e9fdfa5f-a41e-4038-ac78-c2a2e1e15617
-- title:
--   LNatConvexSet
-- statement:
--   $D$ is L$^\natural$-convex: its lift is an L-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, set analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, set analogue

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LiftedSetL

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `D` is L♮-convex: its lift is an L-convex set. -/
def LNatConvexSet (D : Set (V → ℤ)) : Prop := LConvexSet (LiftedSetL D)

end DiscreteConvex.LConvexFunctionsC


