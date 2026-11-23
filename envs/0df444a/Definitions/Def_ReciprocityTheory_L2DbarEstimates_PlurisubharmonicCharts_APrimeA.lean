-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeA
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:51.939142+00:00
-- url     : https://prove2.me/theorems/f02d5ca7-d886-4c7f-b2ef-e60e17daa718
-- title:
--   APrime A
-- statement:
--   Definitions and structural lemmas for APrime A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/APrimeA.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal
noncomputable section
def apraW (d : ℕ) (ε τ : ℝ) (t : ℝ) : ℝ≥0∞ :=
  if t < ε then ENNReal.ofReal ((max (t ^ 2) τ) ^ (-(d : ℝ))) else 0
end
end ReciprocityTheory.L2DbarEstimates.Y


