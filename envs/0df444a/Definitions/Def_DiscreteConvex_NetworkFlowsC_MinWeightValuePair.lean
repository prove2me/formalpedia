-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_MinWeightValuePair
-- name    : DiscreteConvex_NetworkFlowsC_MinWeightValuePair
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:03:28.738912+00:00
-- url     : https://prove2.me/theorems/5c9ebed9-56be-437c-9610-58123c9104b2
-- title:
--   MinWeightValuePair
-- statement:
--   $\check f(x,y)$, the minimum weight of a perfect matching in $G(x,y)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, notation $\\check f(x,y)$.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.266, notation $\\check f(x,y)$

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppPos
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SuppNeg
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MinWeightValue
import Definitions.Def_DiscreteConvex_NetworkFlowsC_UMWeight

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `ˇf(x,y)`, the minimum weight of a perfect matching in `G(x,y)`. -/
noncomputable def MinWeightValuePair (f : (V → ℤ) → WithTop ℝ) (x y : V → ℤ) : WithTop ℝ :=
  MinWeightValue (SuppPos x y) (SuppNeg x y) (UMWeight f x)

-- ===== Auxiliary networks and negative cycles (§9.5.1, redeclared from a sibling chunk) =====

end DiscreteConvex.NetworkFlowsC


