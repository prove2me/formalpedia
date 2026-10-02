-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNaturalConvex
-- name    : DiscreteConvex_LConvexFunctionsC_LNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:34:10.158992+00:00
-- url     : https://prove2.me/theorems/058d3a35-578b-49ef-b26e-a3944158102d
-- title:
--   LNaturalConvex
-- statement:
--   $g$ is L$^\natural$-convex: its lift $\tilde g$ is L-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LiftedFunctionL

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is L♮-convex: its lift `g̃` is L-convex. -/
def LNaturalConvex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  SBF (LiftedFunctionL g) ∧ TRF (LiftedFunctionL g)

end DiscreteConvex.LConvexFunctionsC


