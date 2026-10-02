-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_LNaturalConvexR
-- name    : DiscreteConvex_NetworkFlowsC_LNaturalConvexR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:12.784022+00:00
-- url     : https://prove2.me/theorems/b7c6950a-e152-4281-987a-dd2c23b96a6d
-- title:
--   LNaturalConvexR
-- statement:
--   $g$ is L$^\natural$-convex (real domain): its lift is L-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, redeclared, real version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.178, redeclared, real version

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SBFR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_TRFR
import Definitions.Def_DiscreteConvex_NetworkFlowsC_LiftedFunctionRL

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def LNaturalConvexR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  SBFR (LiftedFunctionRL g) ∧ TRFR (LiftedFunctionRL g)

end DiscreteConvex.NetworkFlowsC


