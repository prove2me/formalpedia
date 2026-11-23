-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_AddLogPosOfThreeQuartersLe
-- name    : ReciprocityTheory_L2DbarEstimates_LeviForms_AddLogPosOfThreeQuartersLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:51.620963+00:00
-- url     : https://prove2.me/theorems/fcf1c6cd-1548-4402-98de-47f0adde07c5
-- title:
--   Add Log Pos Of Three Quarters Le
-- statement:
--   Definitions and structural lemmas for Add Log Pos Of Three Quarters Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/AddLogPosOfThreeQuartersLe.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
universe u
noncomputable section
def dualSig (s : ℝ) : ℝ := 3 / 4 + (s - 3 / 4) * Real.smoothTransition ((s - 3 / 4) * 8)
def dualK (c t : ℝ) : ℝ := -Real.log (dualSig (c - t) + Real.log (dualSig (c - t)))
end
end ReciprocityTheory.L2DbarEstimates.I


