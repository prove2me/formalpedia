-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvexR
-- name    : DiscreteConvex_MConvexFunctionsC_MNaturalConvexR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:30:03.128285+00:00
-- url     : https://prove2.me/theorems/07b6b9f2-c9d1-4b6f-9f33-c5e10f2440de
-- title:
--   MNaturalConvexR
-- statement:
--   $g$ is polyhedral M$^\natural$-convex via the lift: its lift satisfies (M-EXC[R]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.162

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_LiftedFunctionR

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def MNaturalConvexR (g : (V → ℝ) → WithTop ℝ) : Prop := MExchangeAxiomR (LiftedFunctionR g)

end DiscreteConvex.MConvexFunctionsC


