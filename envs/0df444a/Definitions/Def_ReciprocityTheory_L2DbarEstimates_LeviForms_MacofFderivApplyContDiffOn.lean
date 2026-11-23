-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_MacofFderivApplyContDiffOn
-- name    : ReciprocityTheory_L2DbarEstimates_LeviForms_MacofFderivApplyContDiffOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:40.297784+00:00
-- url     : https://prove2.me/theorems/ed227ae2-a85e-4d9b-ab73-baee948518f3
-- title:
--   Macof Fderiv Apply Cont Diff On
-- statement:
--   Definitions and structural lemmas for Macof Fderiv Apply Cont Diff On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/MacofFderivApplyContDiffOn.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
noncomputable section
def macofDet (n : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℂ) ℂ where
  toMultilinearMap :=
    ((Matrix.detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ).toMultilinearMap).restrictScalars ℝ
  cont := by
    show Continuous fun v : Fin n → Fin n → ℂ => Matrix.det (Matrix.of v)
    exact continuous_id.matrix_det
def macofRow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  (Matrix.detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ).toMultilinearMap.toLinearMap M i
end
end ReciprocityTheory.L2DbarEstimates.I


