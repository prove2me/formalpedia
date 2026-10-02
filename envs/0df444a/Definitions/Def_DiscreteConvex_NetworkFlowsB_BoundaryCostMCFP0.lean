-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryCostMCFP0
-- name    : DiscreteConvex_NetworkFlowsB_BoundaryCostMCFP0
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:25.203387+00:00
-- url     : https://prove2.me/theorems/bc72c731-0f30-4ae8-8ab8-98c4cbcda767
-- title:
--   BoundaryCostMCFP0
-- statement:
--   The singleton-indicator boundary cost of Eq. (9.11): $f=\delta_{\{x\}}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247, Eq. (9.11).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247, Eq. (9.11)

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The singleton-indicator boundary cost of Eq. (9.11): `f = δ_{x}`. -/
noncomputable def BoundaryCostMCFP0 (x : V → ℝ) (y : V → ℝ) : WithTop ℝ := if y = x then 0 else ⊤

end DiscreteConvex.NetworkFlowsB


