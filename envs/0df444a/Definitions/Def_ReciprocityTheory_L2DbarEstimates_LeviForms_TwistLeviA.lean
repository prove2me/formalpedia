-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA
-- name    : ReciprocityTheory_L2DbarEstimates_LeviForms_TwistLeviA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:08.103798+00:00
-- url     : https://prove2.me/theorems/d86657b2-f32f-4fbd-8a2e-211a929c4220
-- title:
--   Twist Levi A
-- statement:
--   Definitions and structural lemmas for Twist Levi A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/TwistLeviA.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
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
noncomputable section
def tlFlr (a b s : ℝ) : ℝ := s + Real.smoothTransition ((a - s) / (a - b)) * (a - s)
def tlK (c t : ℝ) : ℝ :=
  -Real.log (tlFlr (19 / 20) (9 / 10) (c - t) + Real.log (tlFlr (19 / 20) (9 / 10) (c - t)))
open Filter Topology
def tlKp (c t : ℝ) : ℝ := (1 + 1 / (c - t)) / ((c - t) + Real.log (c - t))
def tlKpp (c t : ℝ) : ℝ :=
  1 / ((c - t) ^ 2 * ((c - t) + Real.log (c - t))) + ((1 + 1 / (c - t)) / ((c - t) + Real.log (c - t))) ^ 2
end
end ReciprocityTheory.L2DbarEstimates.I


