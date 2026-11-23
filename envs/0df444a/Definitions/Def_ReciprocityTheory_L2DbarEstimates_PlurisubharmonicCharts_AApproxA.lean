-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:35.161025+00:00
-- url     : https://prove2.me/theorems/376715dc-96b8-4036-bb3f-05971e32f92e
-- title:
--   AApprox A
-- statement:
--   Definitions and structural lemmas for AApprox A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/AApproxA.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal ComplexConjugate
noncomputable section
def dbv {n : ℕ} (D : V n →L[ℝ] ℂ) (ζ : V n) : ℂ := (D ζ + I * D (I • ζ)) / 2
def dv {n : ℕ} (D : V n →L[ℝ] ℂ) (ζ : V n) : ℂ := (D ζ - I * D (I • ζ)) / 2
end
end ReciprocityTheory.L2DbarEstimates.Y


