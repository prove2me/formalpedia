-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_LNaturalConvex
-- name    : DiscreteConvex_AlgorithmsC_LNaturalConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:24:52.871596+00:00
-- url     : https://prove2.me/theorems/546dd6ff-4083-486a-ad94-8c84626f1813
-- title:
--   LNaturalConvex
-- statement:
--   $g$ is L$^\natural$-convex: its lift is L-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_SBF
import Definitions.Def_DiscreteConvex_AlgorithmsC_TRF
import Definitions.Def_DiscreteConvex_AlgorithmsC_LiftedFunctionL

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is L♮-convex: its lift is L-convex. -/
def LNaturalConvex (g : (V → ℤ) → WithTop ℝ) : Prop :=
  SBF (LiftedFunctionL g) ∧ TRF (LiftedFunctionL g)

end DiscreteConvex.AlgorithmsC


