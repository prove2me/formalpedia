-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_MNaturalConvexR
-- name    : DiscreteConvex_MConvexFunctionsD_MNaturalConvexR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:52:28.867783+00:00
-- url     : https://prove2.me/theorems/55b83142-88bc-4cbb-95bf-ff46bc25d110
-- title:
--   MNaturalConvexR
-- statement:
--   $g$ is polyhedral M$^\natural$-convex via the lift.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_LiftedFunctionR

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def MNaturalConvexR (g : (V → ℝ) → WithTop ℝ) : Prop := MExchangeAxiomR (LiftedFunctionR g)

end DiscreteConvex.MConvexFunctionsD


