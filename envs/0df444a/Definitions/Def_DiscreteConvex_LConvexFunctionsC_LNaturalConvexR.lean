-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNaturalConvexR
-- name    : DiscreteConvex_LConvexFunctionsC_LNaturalConvexR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:34:40.210491+00:00
-- url     : https://prove2.me/theorems/4ae53222-921f-457d-aa9e-dc52b65c7024
-- title:
--   LNaturalConvexR
-- statement:
--   $g$ is polyhedral L$^\natural$-convex: its lift is polyhedral L-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LiftedFunctionLR

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is polyhedral L♮-convex: its lift is polyhedral L-convex. -/
def LNaturalConvexR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  SBFR (LiftedFunctionLR g) ∧ TRFR (LiftedFunctionLR g)

end DiscreteConvex.LConvexFunctionsC


