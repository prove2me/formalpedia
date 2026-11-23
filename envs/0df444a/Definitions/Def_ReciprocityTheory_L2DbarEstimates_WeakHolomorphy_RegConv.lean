-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
-- name    : ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:30.781805+00:00
-- url     : https://prove2.me/theorems/80cc6155-d062-484f-b5df-94ed690b596f
-- title:
--   Reg Conv
-- statement:
--   Definitions and structural lemmas for Reg Conv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegConv.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable def smulFlip : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip
end ReciprocityTheory.L2DbarEstimates.C


