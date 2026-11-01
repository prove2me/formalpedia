-- Prove2me | Definitions.Def_OAIQ091C018
-- name    : OAIQ091C018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T17:28:29.344642+00:00
-- url     : https://prove2.me/theorems/e6eb6920-7485-4f58-b392-e62fe07586ef
-- title:
--   Definitions bundle OAIQ091C018 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 289 declarations of OpenAI's Lean: 93 definitions, 3 inductive types or structures, 1 instance and 192 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.compressionEnergyField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.coupledIntegrand`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.cubicEntryField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.deficitField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.energyDerivativeField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.energyLaplacianField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.gradientEnergyField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.gradientMap`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.hessianCostField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.hessianIdentityField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.hessianMap`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.hessianMatrixField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.hessianMinusField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.hessianPlusField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.hessianTraceField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.invariantHessianField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.jointEnergyLaplacian`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.jointHessianEnergy`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.jointMatrixEnergy`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.jointScalarNorm`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.jointTraceEnergy`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.laplacianNormField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.matrixEnergyField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.minusMatrixMap`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.minusNormField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.onReflectedMeasure`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.onSymmetricMeasure`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.oppositeEnergyDerivativeField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.oppositeEnergyField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.oppositeEnergyLaplacianField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusMatrixMap`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusNormField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.preVarianceIntegrand`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.radialEnergyField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.reflectedFlow`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.regularizedNormField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.regularizedRadialField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.regularizedSecondField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.scalarNormField`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.squareEnergyField` and 56 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `EinsteinFour_BianchiSlices`, `EinsteinFour_CurvatureForm`, `EinsteinFour_CurvatureTensors02`, `EinsteinFour_FrameAverages`, `EinsteinFour_FrameEnergy`, `EinsteinFour_FrameFlow`, `EinsteinFour_FrameOrientation`, `EinsteinFour_FrameRegularity`, `EinsteinFour_HeatKernels10`, `EinsteinFour_HessianTraceEquation`, `EinsteinFour_HighestMinusCoordinates`, `EinsteinFour_HodgeTheory08`, `EinsteinFour_MetricBianchi`, `EinsteinFour_MetricCurvatureGreen`, `EinsteinFour_MetricHessian`, `EinsteinFour_MetricMatrixGreen`, `EinsteinFour_MetricMinusGreen`, `EinsteinFour_WeylEstimates01`, `EinsteinFour_WeylEstimates03`, `EinsteinFour_WeylMatrixEquation`, `EinsteinFour_WeylNormal`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C013`, `OAIQ091C014` and `OAIQ091C015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C019`, `OAIQ091C020`, `OAIQ091C021` and `OAIQ091C022`; the statements `OAI.PositiveEinsteinFour.Geometry.FrameReflectionData.jointEnergyCancellation`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.localWeightedHessian`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.matrixGreen`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.minusHVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.minusNormVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.normDifferenceVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.one_block_zero_of_variance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusCurvatureGreen`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusHVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusNormVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.preVarianceGreen_oriented`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.regularizedHessianGreen`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.traceGreen` and `OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced`; the proofs of `OAI.PositiveEinsteinFour.Geometry.FrameReflectionData.jointEnergyCancellation`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.localWeightedHessian`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.matrixGreen`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.minusHVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.minusNormVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.normDifferenceVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.one_block_zero_of_variance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusCurvatureGreen`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusHVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusNormVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.preVarianceGreen_oriented`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.regularizedHessianGreen`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.traceGreen`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_highestProjection`, `OAI.PositiveEinsteinFour.HighestHessian.general_weighted_trace_subtraction`, `OAI.PositiveEinsteinFour.HighestHessian.innerAction_casimir_of_condition`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_energy_of_condition`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_0_3_2`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_2_0`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_2_1`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_2_2`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_2_3`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_0`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_1`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_2`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_entry_2_3_3`, `OAI.PositiveEinsteinFour.HighestHessian.totalMinus_highest` and `OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C013
import Definitions.Def_OAIQ091C014
import Definitions.Def_OAIQ091C015

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestMinusCoordinates
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate action of the three total minus rotations. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

@[simp] theorem minusCoordinates_2_7 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 7 = -2 * c 2 := rfl

@[simp] theorem minusCoordinates_2_8 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 8 = 2 * c 7 + 2 * c 15 := rfl

@[simp] theorem minusCoordinates_2_9 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 9 = 2 * c 10 - 2 * c 11 - 2 * c 12 := rfl

@[simp] theorem minusCoordinates_2_10 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 10 = -2 * c 3 := rfl

@[simp] theorem minusCoordinates_2_11 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 11 = c 9 + c 19 := rfl

@[simp] theorem minusCoordinates_2_12 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 12 = -c 3 - c 4 + c 13 := rfl

@[simp] theorem minusCoordinates_2_13 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 13 = c 10 + c 20 := rfl

@[simp] theorem minusCoordinates_2_14 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 14 = -c 6 - c 7 - c 16 - c 17 := rfl

@[simp] theorem minusCoordinates_2_15 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 15 = c 2 - c 5 - c 8 := rfl

@[simp] theorem minusCoordinates_2_16 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 16 = 2 * c 14 - 2 * c 18 := rfl

@[simp] theorem minusCoordinates_2_17 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 17 = -2 * c 5 + 2 * c 18 := rfl

@[simp] theorem minusCoordinates_2_18 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 18 = 2 * c 15 - 2 * c 17 := rfl

@[simp] theorem minusCoordinates_2_19 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 19 = -2 * c 11 - 2 * c 12 - 2 * c 20 := rfl

@[simp] theorem minusCoordinates_2_20 (c : Fin 21 → ℝ) :
    minusCoordinates 2 c 20 = 2 * c 4 - 2 * c 13 := rfl


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_BianchiSlices
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix _root_.OAI.PositiveEinsteinFour.HighestHessian.coupledOperator_coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual gradient slices of a four-slot Hessian. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem innerSlice_matrix (X : Hessian) (i : Fin 4)
    (hs : ∀ j, symmetric (X i j)) (a b : Fin 3) :
    (innerSlice X i).matrix a b = WithLp.toLp 2 (fun j => X i j a b) := by
  ext j
  fin_cases a <;> fin_cases b <;> simp [innerSlice, Tensor.matrix, next, previous]
  all_goals exact hs j _ _

theorem innerSlice_bianchi (X : Hessian) (i : Fin 4)
    (hs : ∀ j, symmetric (X i j)) (hb : ∀ r, divergence X i r = 0) :
    (innerSlice X i).bianchi := by
  intro r
  rw [Tensor.divergence_eq_sum]
  simp_rw [innerSlice_matrix X i hs]
  exact hb r

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylNormal
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instNonemptyOrthonormalFrame _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Link the normal-tensor calculation to the concrete metric. The classical
curvature decomposition is displayed as an explicit local hypothesis here;
the angular mean identities themselves are proved, not postulated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem normalCurvatureDerivative_mean_square
    (h : FollandMoments) (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (hTs : ∀ a, (plusWeylGradient g c e a)ᵀ = plusWeylGradient g c e a)
    (hTt : ∀ a, (plusWeylGradient g c e a).trace = 0) :
    (∫ q, squareNorm (normalCurvatureDerivative g c e q) ∂sphereMeasure) =
      (gradientSquareNorm (plusWeylGradient g c e) +
        gradientSquareNorm (minusWeylGradient g c e)) / 16 := by
  exact integral_normalDerivative_squareNorm_exact h _ _ hTs hTt

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureForm
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationFrameClass_proj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coordinate curvature is a four-linear form. This supplies
the multilinearity used to change normal frames without an independent
curvature-transformation assumption. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem OrthonormalFrame.turn_vector {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (q : Angular.Directions) (j : Fin 4) :
    (e.turn q).vector j = ∑ a, directionFrameMatrix q a j • e.vector a := by
  ext i
  simp [OrthonormalFrame.vector, OrthonormalFrame.turn, Matrix.mul_apply, mul_comm]

theorem frameCurvature_turn (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (q : Angular.Directions) (i j k l : Fin 4) :
    frameCurvature g c (e.turn q) i j k l =
      ∑ a, ∑ b, ∑ p, ∑ r,
        (directionFrameMatrix q a i * directionFrameMatrix q b j *
          directionFrameMatrix q p k * directionFrameMatrix q r l) *
            frameCurvature g c e a b p r := by
  have h := multilinear_combinations (curvatureForm g c)
    (directionFrameMatrix q) e.vector ![i, j, k, l]
  have he : (fun s : Fin 4 => ∑ a, directionFrameMatrix q a (![i, j, k, l] s) •
      e.vector a) = ![(e.turn q).vector i, (e.turn q).vector j,
        (e.turn q).vector k, (e.turn q).vector l] := by
    funext s
    fin_cases s <;> simp [OrthonormalFrame.turn_vector]
  rw [he] at h
  simpa [← frameCurvature_eq_form] using h

theorem frameCurvatureField_turn (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (q : Angular.Directions) :
    frameCurvatureField g (frameTurn e q) = normalCurvatureDeviation g c e q := by
  ext i j
  rw [frameCurvatureField_apply]
  change frameCurvature g c (e.turn q) i.succ 0 0 j.succ -
    (if i = j then 1 else 0) = _
  rw [frameCurvature_turn]
  simp only [directionFrameMatrix_zero, directionFrameMatrix_succ]
  change (∑ a, ∑ b, ∑ p, ∑ r,
    (Angular.normalVector q i a * q.val b * q.val p * Angular.normalVector q j r) *
      frameCurvature g c e a b p r) - (if i = j then 1 else 0) =
    (∑ a, ∑ b, ∑ p, ∑ r, frameCurvature g c e a b p r *
      Angular.normalVector q i a * q.val b * q.val p * Angular.normalVector q j r) -
        (if i = j then 1 else 0)
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  ring

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameAverages
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spherical disintegration of the actual frame-curvature energies.

The explicit published input `BrinKarcherAveraging` is the specialization of
the Riemannian-base times Stiefel probability measure in Brin--Karcher (1984),
Section 1, p.275, to functions depending only on the first frame direction.
It is a generic integration statement and contains no curvature estimate.
The angular curvature identities used below are proved separately. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat3_1
/-- The same disintegration yields the exact derivative energy. The gradient
sum is a base scalar; its independence of orthonormal frame is explicit. -/
theorem frameCurvatureDerivative_mean_square
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)} (hμ : BrinKarcherAveraging g μ)
    (h : FollandMoments) (E : M → ℝ)
    (hHi : Integrable (fun e => ‖frameCurvatureDerivative g e‖ ^ 2) μ)
    (hEi : Integrable E (normalizedVolume g))
    (hInv : DirectionInvariant (fun e => ‖frameCurvatureDerivative g e‖ ^ 2))
    (hturn : ∀ c (e : OrthonormalFrame g c) q,
      frameCurvatureDerivative g (frameTurn e q) = normalCurvatureDerivative g c e q)
    (hsym : ∀ c (e : OrthonormalFrame g c) a,
      (plusWeylGradient g c e a)ᵀ = plusWeylGradient g c e a)
    (htr : ∀ c (e : OrthonormalFrame g c) a, (plusWeylGradient g c e a).trace = 0)
    (hE : ∀ c (e : OrthonormalFrame g c),
      gradientSquareNorm (plusWeylGradient g c e) +
        gradientSquareNorm (minusWeylGradient g c e) = E c) :
    (∫ e, ‖frameCurvatureDerivative g e‖ ^ 2 ∂μ) =
      (∫ c, E c ∂normalizedVolume g) / 16 := by
  rw [hμ.fiberFormula _ (fun c => E c / 16) hHi (hEi.div_const _) hInv]
  · exact integral_div _ _
  · intro c e
    simp_rw [hturn, ← squareNorm_eq_frobenius_norm_sq]
    rw [normalCurvatureDerivative_mean_square h g c e (hsym c e) (htr c e), hE]

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameOrientation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An orientation is a continuous choice of one of the two orientation
classes in every orthonormal frame fiber. This separates the individual
Weyl norms used by the scalar argument from the orientation-independent sum
used in radial averaging. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem plusNorm_nonneg {g : SmoothMetric M} (o : FrameOrientation g) (c : M) :
    0 ≤ plusNorm o c := normalizedBlockNorm_nonneg _

theorem plusNorm_eq_zero_iff {g : SmoothMetric M} (o : FrameOrientation g) (c : M) :
    plusNorm o c = 0 ↔ plusWeyl g c (o.frame c) = 0 :=
  normalizedBlockNorm_eq_zero_iff _

theorem minusNorm_eq_zero_iff {g : SmoothMetric M} (o : FrameOrientation g) (c : M) :
    minusNorm o c = 0 ↔ minusWeyl g c (o.frame c) = 0 :=
  normalizedBlockNorm_eq_zero_iff _

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameFlow
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The frame-flow action on the actual normal-curvature fields. The
measure-preserving continuous action is the precise part of Brin--Karcher,
Section 1, used here; no ergodicity or curvature-energy bound is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat3_2
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instNormedSpaceRealMat3
def curvatureCurve {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (φ : FrameFlow g μ) (hC : Continuous (frameCurvatureField g))
    (t : ℝ) : C(FrameBundle g, Mat3) :=
  ⟨fun e => frameCurvatureField g (φ.map t e), hC.comp (φ.continuous_slice t)⟩

def curvatureDerivativeCurve {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (φ : FrameFlow g μ) (hH : Continuous (frameCurvatureDerivative g))
    (t : ℝ) : C(FrameBundle g, Mat3) :=
  ⟨fun e => frameCurvatureDerivative g (φ.map t e), hH.comp (φ.continuous_slice t)⟩

/-- The ordinary derivative along each parallel frame implies the derivative
of the full continuous field used in the radial averaging theorem. -/
theorem curvatureCurve_hasDerivAt {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] (φ : FrameFlow g μ)
    (hC : Continuous (frameCurvatureField g))
    (hH : Continuous (frameCurvatureDerivative g))
    (hpoint : ∀ t e, HasDerivAt
      (fun s => frameCurvatureField g (φ.map s e))
      (frameCurvatureDerivative g (φ.map t e)) t) (t : ℝ) :
    HasDerivAt (curvatureCurve φ hC) (curvatureDerivativeCurve φ hH t) t := by
  apply Averages.continuousField_hasDerivAt_of_joint
  · exact hH.comp φ.continuous
  · exact hpoint

theorem curvatureCurve_stationary {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (φ : FrameFlow g μ) (hC : Continuous (frameCurvatureField g)) (t : ℝ) :
    (∫ e, ‖curvatureCurve φ hC t e‖ ^ 2 ∂μ) =
      ∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂μ := by
  exact (φ.preserves t).integral_comp' (fun e => ‖frameCurvatureField g e‖ ^ 2)

theorem curvatureDerivativeCurve_stationary {g : SmoothMetric M}
    {μ : Measure (FrameBundle g)} (φ : FrameFlow g μ)
    (hH : Continuous (frameCurvatureDerivative g)) (t : ℝ) :
    (∫ e, ‖curvatureDerivativeCurve φ hH t e‖ ^ 2 ∂μ) =
      ∫ e, ‖frameCurvatureDerivative g e‖ ^ 2 ∂μ := by
  exact (φ.preserves t).integral_comp' (fun e => ‖frameCurvatureDerivative g e‖ ^ 2)

theorem curvatureCurve_energy {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (φ : FrameFlow g μ) (hC : Continuous (frameCurvatureField g)) {s : ℝ}
    (hs : (∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂μ) = (3 / 2) * s) :
    ∀ t, (∫ e, ‖curvatureCurve φ hC t e‖ ^ 2 ∂μ) = (3 / 2) * s := by
  intro t
  rw [curvatureCurve_stationary, hs]

theorem curvatureDerivativeCurve_energy {g : SmoothMetric M}
    {μ : Measure (FrameBundle g)} (φ : FrameFlow g μ)
    (hH : Continuous (frameCurvatureDerivative g)) {s : ℝ}
    (hs : (∫ e, ‖frameCurvatureDerivative g e‖ ^ 2 ∂μ) ≤ (9 / 4) * s) :
    ∀ t, (∫ e, ‖curvatureDerivativeCurve φ hH t e‖ ^ 2 ∂μ) ≤
      (3 / 2) * ((3 / 2) * s) := by
  intro t
  rw [curvatureDerivativeCurve_stationary]
  linarith

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricBianchi
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instNonemptyOrthonormalFrame _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Weyl gradient, with its derivative index treated as a tangent
vector. These changes of coordinate retain every component: neither the
Bianchi equation nor a differential estimate is built into the definition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular Bianchi TraceHessian
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The concrete tensor to which the finite Bianchi estimates apply. -/
def plusGradientTensor (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c) :
    Tensor := gradientTensor (plusWeylGradient g c e)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricHessian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted rough-Laplacian identity for the metric's actual Weyl
gradient. Differentiation takes place in the coordinate connection before
the parallel frame is applied. The integration identity follows from
frame-flow invariance, rather than an assumed Hessian integral formula. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular TraceHessian
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameGradientVector (g : SmoothMetric M) (e : FrameBundle g) : GradientVector :=
  gradientVector (plusWeylGradient g e.base e.frame)

def frameHessianVector (g : SmoothMetric M) (i : Fin 4) (e : FrameBundle g) :
    GradientVector := gradientVector (plusWeylHessian g e.base e.frame i)

def frameThirdVector (g : SmoothMetric M) (i j : Fin 4) (e : FrameBundle g) :
    GradientVector := gradientVector (plusWeylThirdDerivative g e.base e.frame i j)

/-- The actual rough Laplacian of the Weyl gradient, in the same frame. -/
def frameGradientLaplacian (g : SmoothMetric M) (e : FrameBundle g) : GradientVector :=
  ∑ i, frameThirdVector g i i e

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HessianTraceEquation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix _root_.OAI.PositiveEinsteinFour.Geometry.matrixSlot_apply _root_.OAI.PositiveEinsteinFour.HighestHessian.coupledOperator_coordinates _root_.OAI.PositiveEinsteinFour.QuaternionFrame.frameMatrix_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derive the Weyl Hessian trace from Bianchi and the curvature commutator.
This removes a separate tensor Laplacian premise from the local weighted
square. All contractions use the same concrete quaternion coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem rotation_innerSlice_component (X : Hessian)
    (hs : ∀ i j, symmetric (X i j)) (s : Fin 3) (i k : Fin 4) (a b : Fin 3) :
    matrixRotation s (innerSlice X i) a b k = matrixAction s (X i k) a b := by
  simp only [matrixRotation, innerSlice_matrix X i (hs i), matrixAction]
  simp [Fin.sum_univ_three]
  ring

theorem coupling_innerSlice_component (X : Hessian)
    (hs : ∀ i j, symmetric (X i j))
    (hb : ∀ i r, divergence X i r = 0) (i j : Fin 4) (a b : Fin 3) :
    (∑ s, ∑ k, quaternionMatrix s j k * matrixAction s (X i k) a b) =
      -4 * X i j a b := by
  have h := congrArg (fun v : Vec => v j)
    (gradientCoupling_eq (innerSlice X i) (innerSlice_bianchi X i (hs i) (hb i)) a b)
  simp only [gradientCoupling, WithLp.ofLp_sum, Finset.sum_apply] at h
  simp_rw [← quaternionMatrix_apply, rotation_innerSlice_component X hs] at h
  simpa only [innerSlice_matrix X i (hs i), PiLp.smul_apply, smul_eq_mul] using h

/-- A derivative-symmetric Bianchi Hessian has zero trace. -/
theorem symmetric_bianchi_trace_zero (X : Hessian)
    (hderiv : ∀ i j, X i j = X j i)
    (hs : ∀ i j, symmetric (X i j))
    (hb : ∀ i r, divergence X i r = 0) : hessianTrace X = 0 := by
  ext a b
  have hskew (s : Fin 3) :
      (∑ i, ∑ k, quaternionMatrix s i k * matrixAction s (X i k) a b) = 0 := by
    have he :
        (∑ i, ∑ k, quaternionMatrix s i k * matrixAction s (X i k) a b) =
        -(∑ i, ∑ k, quaternionMatrix s i k * matrixAction s (X i k) a b) := by
      calc
        _ = ∑ k, ∑ i, quaternionMatrix s i k * matrixAction s (X i k) a b :=
          Finset.sum_comm
        _ = _ := by
          simp only [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          rw [quaternionMatrix_skew s k i, hderiv k i]
          ring
    linarith
  have he : (∑ i, ∑ s, ∑ k,
      quaternionMatrix s i k * matrixAction s (X i k) a b) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [hskew]
    simp
  simp_rw [coupling_innerSlice_component X hs hb] at he
  simp only [← Finset.mul_sum] at he
  change (∑ i, X i i a b) = 0
  linarith

end

end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricCurvatureGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Derivative-slot integration for the actual metric Weyl Hessian. The
coefficient and its derivative are both the concrete quaternion curvature
block. The only differential premises are parallel differentiation and
the classical divergence and skew identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory TraceHessian Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameGradientSlice (g : SmoothMetric M) (j : Fin 4) (e : FrameBundle g) : MatrixVector :=
  matrixVector (plusWeylGradient g e.base e.frame j)

def frameHessianSlice (g : SmoothMetric M) (i j : Fin 4) (e : FrameBundle g) : MatrixVector :=
  matrixVector (plusWeylHessian g e.base e.frame i j)

def frameThirdSlice (g : SmoothMetric M) (i k j : Fin 4) (e : FrameBundle g) : MatrixVector :=
  matrixVector (plusWeylThirdDerivative g e.base e.frame i k j)

def framePlusCoefficientDerivative (g : SmoothMetric M) (p : Averages.CurvatureIndex)
    (e : FrameBundle g) : ℝ :=
  blockTensor (plusWeylGradient g e.base e.frame p.1.2)
    quaternionMatrix p.1.1 p.1.2 p.2.2 p.2.1

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricMatrixGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The varying-coefficient Green identity for the actual Weyl matrix slot. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory TraceHessian
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local instance instNormedAddCommGroupMat_1_r0ded1c_1 : NormedAddCommGroup Mat := Matrix.frobeniusNormedAddCommGroup
local instance instNormedSpaceRealMat_1_r0ded1c_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
def frameWeylGradientMatrix (g : SmoothMetric M) (i : Fin 4) (e : FrameBundle g) : Mat :=
  plusWeylGradient g e.base e.frame i

def frameWeylHessianMatrix (g : SmoothMetric M) (i j : Fin 4) (e : FrameBundle g) : Mat :=
  plusWeylHessian g e.base e.frame i j

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricMinusGreen
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The opposite curvature block acting on the plus Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory TraceHessian Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameMinusCoefficientDerivative (g : SmoothMetric M) (p : Averages.CurvatureIndex)
    (e : FrameBundle g) : ℝ :=
  blockTensor (minusWeylGradient g e.base e.frame p.1.2)
    oppositeMatrix p.1.1 p.1.2 p.2.2 p.2.1


end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylMatrixEquation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Weyl matrix equation in an arbitrary orthonormal frame. This
derivation uses the actual Bianchi Hessian and curvature commutator, so
no eigenframe is differentiated. -/

namespace PositiveEinsteinFour.TraceHessian

open scoped BigOperators
open Matrix
open HighestHessian

noncomputable section

/-- The full matrix Weyl equation is forced by differential Bianchi and
the classical curvature commutator. It holds in an arbitrary frame. -/
theorem weyl_trace_eq_of_bianchi_commutator (M : Mat) (hs : symmetric M) (ht : traceFree M)
    (X : Hessian) (hm : ∀ i j, symmetric (X i j) ∧ traceFree (X i j))
    (hb : ∀ i r, divergence X i r = 0)
    (hc : ∀ i j a b, X i j a b - X j i a b = bundleCurvatureAction M i j M a b) :
    hessianTrace X = weylLaplacian M := by
  have hsB := weylLaplacian_symmetric M hs
  have htB := weylLaplacian_traceFree M ht
  have hY := HighestHessian.symmetric_bianchi_trace_zero (X - traceComponent (weylLaplacian M))
    (fun i j => by
      ext a b
      change X i j a b - traceComponent (weylLaplacian M) i j a b =
        X j i a b - traceComponent (weylLaplacian M) j i a b
      have h := hc i j a b
      have hk := traceComponent_weylLaplacian_skew M hs ht i j a b
      linarith)
    (fun i j a b => by
      change X i j a b - traceComponent (weylLaplacian M) i j a b =
        X i j b a - traceComponent (weylLaplacian M) i j b a
      rw [(hm i j).1 a b, traceComponent_symmetric _ hsB htB i j a b])
    (fun i r => by
      rw [divergence_sub, hb, traceComponent_divergence _ hsB htB, sub_self])
  unfold hessianTrace at hY
  change (∑ i, (X i i - traceComponent (weylLaplacian M) i i)) = 0 at hY
  rw [Finset.sum_sub_distrib] at hY
  change hessianTrace X - hessianTrace (traceComponent (weylLaplacian M)) = 0 at hY
  rw [trace_traceComponent] at hY
  exact sub_eq_zero.mp hY

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationFrameClass_proj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Realize the invariant Weyl equation and its derivative on the actual
metric tensors. The inputs are the pointwise covariant Bianchi and Ricci
identities (Petersen, third edition, Section 3.1.1) and ordinary parallel
frame differentiation. No Weyl Laplacian equation is an input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local instance metricWeylNormedRing_r0ded1c_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance metricWeylNormedSpace_r0ded1c_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance metricWeylNormedAlgebra_r0ded1c_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem metric_weyl_trace (g : SmoothMetric M) (h : WeylCovariantIdentities g)
    (e : FrameBundle g) :
    hessianTrace (plusWeylHessian g e.base e.frame) =
      weylLaplacian (plusWeyl g e.base e.frame) :=
  weyl_trace_eq_of_bianchi_commutator _ (h.symmetric e) (h.traceFree e)
    _ (h.hessianMatrix e) (h.hessianBianchi e) (h.hessianCommutator e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiate the actual Hessian constraints to show that its rough
Laplacian remains a symmetric trace-free Bianchi gradient. -/

namespace PositiveEinsteinFour.Geometry

open Matrix TraceHessian EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameLaplacianMatrix (g : SmoothMetric M) (e : FrameBundle g) : Angular.Gradient :=
  fun j => ∑ i, plusWeylThirdDerivative g e.base e.frame i i j

end
end PositiveEinsteinFour.Geometry
end


section

/-! The raw classical parallel-frame calculus used by the weighted Green
argument. Every field refers to the actual metric tensors. No compressed
Ricci equation or integral estimate is a field of this structure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

/-- Matrix symmetry and trace constraints on the first derivative are
consequences of parallel differentiation of the actual Weyl block. -/
theorem gradientConstraints (d : MetricGreenData g μ) (e : FrameBundle g) :
    (∀ i, symmetric (plusWeylGradient g e.base e.frame i)) ∧
    (∀ i, traceFree (plusWeylGradient g e.base e.frame i)) := by
  have hi (i : Fin 4) : symmetric (plusWeylGradient g e.base e.frame i) ∧
      traceFree (plusWeylGradient g e.base e.frame i) := by
    obtain ⟨e₀, he⟩ := ((d.flow i).map 0).surjective e
    change (d.flow i).map 0 e₀ = e at he
    have hs := symmetric_of_hasDerivAt (d.derivativeWeyl i 0 e₀)
      (fun t => d.weyl.symmetric ((d.flow i).map t e₀))
    have ht := traceFree_of_hasDerivAt (d.derivativeWeyl i 0 e₀)
      (fun t => d.weyl.traceFree ((d.flow i).map t e₀))
    rw [he] at hs ht
    exact ⟨hs, ht⟩
  exact ⟨fun i => (hi i).1, fun i => (hi i).2⟩

end MetricGreenData

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.greenDataNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.greenDataNormedSpace
local instance greenDataNormedAlgebra_r0ded1c_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem continuousGradientVector (d : MetricGreenData g μ) :
    Continuous (frameGradientVector g) :=
  gradientVectorMap.continuous.comp (continuous_pi d.continuousGradient)

theorem continuousHessianVector (d : MetricGreenData g μ) (i : Fin 4) :
    Continuous (frameHessianVector g i) :=
  gradientVectorMap.continuous.comp (continuous_pi (d.continuousHessian i))

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Supply the smooth weights used by the metric Green identities from
the actual two Weyl blocks and their actual first covariant derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TraceHessian
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameRegularizedWeightDerivative (g : SmoothMetric M) (ε : ℝ) (hε : 0 < ε)
    (hT : Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame))
    (hU : Continuous (fun e : FrameBundle g => minusWeyl g e.base e.frame))
    (hZ : ∀ i, Continuous (fun e : FrameBundle g => plusWeylGradient g e.base e.frame i))
    (hV : ∀ i, Continuous (fun e : FrameBundle g => minusWeylGradient g e.base e.frame i))
    (i : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedWeylWeightDerivative ε (plusWeyl g e.base e.frame)
      (minusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame i)
      (minusWeylGradient g e.base e.frame i),
    continuous_regularizedWeylWeightDerivative ε hε _ _ _ _ hT hU (hZ i) (hV i)⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual scalar derivatives in the same coordinate connection and frame
flow as the Weyl tensors. The data below contain only parallel differentiation,
Hessian symmetry and the ordinary covector Ricci commutator (Petersen,
Riemannian Geometry, §3.1.1 and Proposition 2.2.8). -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarGradientVector (g : SmoothMetric M) (a : M → ℝ) (e : FrameBundle g) : Bianchi.Vec :=
  WithLp.toLp 2 (scalarGradient g a e)

def scalarTraceFreeHessian (g : SmoothMetric M) (a : M → ℝ) (e : FrameBundle g) : Mat4 :=
  fun i j => scalarHessian g a e i j - if i = j then scalarLaplacian g a e / 4 else 0

namespace ScalarCovariantData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)} {d : MetricGreenData g μ}
  {a : M → ℝ} (s : ScalarCovariantData d a)

include s

theorem continuousLaplacian : Continuous (scalarLaplacian g a) :=
  continuous_finsetSum _ (fun i _ => s.continuousHessian i i)

theorem derivativeLaplacian (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun r => scalarLaplacian g a ((d.flow i).map r e))
      (∑ j, scalarThird g a ((d.flow i).map t e) i j j) t :=
  HasDerivAt.fun_sum (fun j _ => s.derivativeHessian i j j t e)

theorem third_symmetric (e : FrameBundle g) (i j k : Fin 4) :
    scalarThird g a e i j k = scalarThird g a e i k j := by
  obtain ⟨e₀, he⟩ := ((d.flow i).map 0).surjective e
  have h₁ := s.derivativeHessian i j k 0 e₀
  have h₂ := s.derivativeHessian i k j 0 e₀
  have hf : (fun t => scalarHessian g a ((d.flow i).map t e₀) j k) =
      (fun t => scalarHessian g a ((d.flow i).map t e₀) k j) :=
    funext (fun t => s.hessianSymmetric _ _ _)
  rw [hf] at h₁
  have h := h₁.unique h₂
  simpa only [he] using h

theorem laplacianGradient_commute (e : FrameBundle g) (j : Fin 4) :
    (∑ i, scalarThird g a e i i j) =
      (∑ i, scalarThird g a e j i i) + 3 * scalarGradient g a e j := by
  have hi (i : Fin 4) : scalarThird g a e i i j = scalarThird g a e j i i +
      ∑ l, frameCurvature g e.base e.frame i j l i * scalarGradient g a e l := by
    have hc := s.commutator e i j i
    rw [s.third_symmetric e i i j]
    linarith only [hc]
  simp_rw [hi, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, d.ricci]
  simp

end ScalarCovariantData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar Green formulas obtained by differentiating the invariant frame
integral. All fields are the actual covariant derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

namespace ScalarCovariantData

variable {a b : M → ℝ} (s : ScalarCovariantData d a)

def thirdField (i j k : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => scalarThird g a e i j k, s.continuousThird i j k⟩

def laplacianField : C(FrameBundle g, ℝ) := ⟨scalarLaplacian g a, s.continuousLaplacian⟩

def laplacianDerivativeField (i : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => ∑ j, scalarThird g a e i j j,
    continuous_finsetSum _ (fun j _ => s.continuousThird i j j)⟩

end ScalarCovariantData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The quadratic and radial scalar contractions are unchanged by the
pointwise spectral frame. These are identities on finite arrays. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

def slotLinear (A : Mat) : Mat →ₗ[ℝ] Mat where
  toFun := matrixSlotAction A
  map_add' B C := by
    simp only [matrixSlotAction_eq, Matrix.mul_add, Matrix.add_mul,
      Matrix.trace_add, add_div, add_smul]
    module
  map_smul' c B := by
    simp only [matrixSlotAction_eq, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul, smul_add, smul_sub, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The small classical smooth-bundle input needed to use scalar Poisson
solutions on one oriented frame component. Smoothness of the squared norm
and invariance under oriented orthonormal frames are the ordinary metric
bundle calculus of Petersen §2.2 and §3.1.1. The scalar gradient identities
below are derived from parallel differentiation; no variance estimate is
included in the input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

structure PetersenOrientedNormInput (orientation : FrameOrientation g) : Prop where
  plusSquareSmooth : ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun c => plusNorm orientation c ^ 2)
  minusSquareSmooth : ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun c => minusNorm orientation c ^ 2)
  plusFrame : ∀ e ∈ orientation.positive,
    plusNorm orientation e.base = normalizedBlockNorm (plusWeyl g e.base e.frame)
  minusFrame : ∀ e ∈ orientation.positive,
    minusNorm orientation e.base = normalizedBlockNorm (minusWeyl g e.base e.frame)

def OrientationPreservingFlow (d : MetricGreenData g μ) (orientation : FrameOrientation g) : Prop :=
  ∀ i t e, (d.flow i).map t e ∈ orientation.positive ↔ e ∈ orientation.positive

theorem scalarGradient_eq_of_frame_derivative {d : MetricGreenData g μ}
    {a : M → ℝ} (s : ScalarCovariantData d a) (orientation : FrameOrientation g)
    (hflow : OrientationPreservingFlow d orientation)
    (F : FrameBundle g → ℝ) (Q : Fin 4 → FrameBundle g → ℝ)
    (hvalue : ∀ e ∈ orientation.positive, a e.base = F e)
    (hderiv : ∀ i t e, HasDerivAt (fun r => F ((d.flow i).map r e))
      (Q i ((d.flow i).map t e)) t)
    (e : FrameBundle g) (he : e ∈ orientation.positive) (i : Fin 4) :
    scalarGradient g a e i = Q i e := by
  obtain ⟨e₀, he₀⟩ := ((d.flow i).map 0).surjective e
  change (d.flow i).map 0 e₀ = e at he₀
  have hp : e₀ ∈ orientation.positive := (hflow i 0 e₀).mp (he₀.symm ▸ he)
  have hf : (fun r => a ((d.flow i).map r e₀).base) =
      fun r => F ((d.flow i).map r e₀) :=
    funext (fun r => hvalue _ ((hflow i r e₀).mpr hp))
  have hs := s.derivativeValue i 0 e₀
  rw [hf] at hs
  have hu := hs.unique (hderiv i 0 e₀)
  simpa only [he₀] using hu

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrated scalar Bochner identity derived from the actual Ricci
commutator and the frame-flow Green formulas. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ}
  {a : M → ℝ} (s : ScalarCovariantData d a)

include s

omit s in
theorem scalarTraceFreeHessian_trace (e : FrameBundle g) :
    Matrix.trace (scalarTraceFreeHessian g a e) = 0 := by
  simp only [Matrix.trace, Matrix.diag, scalarTraceFreeHessian, ite_true, if_true,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, scalarLaplacian]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Weighted integration by parts for the trace-free scalar Hessian.
This is the four-dimensional identity used in the nonlinear proof of
the sharp positive-Ricci scalar inequality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} {a w : M → ℝ}

namespace ScalarCovariantData

def traceFreeHessianField (s : ScalarCovariantData d a) (i j : Fin 4) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => scalarTraceFreeHessian g a e i j, by
    have hH := s.continuousHessian i j
    have hL := s.continuousLaplacian
    unfold scalarTraceFreeHessian
    split_ifs <;> fun_prop⟩

def traceFreeHessianDerivativeField (s : ScalarCovariantData d a)
    (k i j : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => scalarThird g a e k i j -
    if i = j then (∑ l, scalarThird g a e k l l) / 4 else 0, by
    have hT := s.continuousThird k i j
    have hL := continuous_finsetSum Finset.univ (fun l _ => s.continuousThird k l l)
    split_ifs <;> fun_prop⟩

theorem derivativeTraceFreeHessian (s : ScalarCovariantData d a)
    (k i j : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun r => scalarTraceFreeHessian g a ((d.flow k).map r e) i j)
      (s.traceFreeHessianDerivativeField k i j ((d.flow k).map t e)) t := by
  dsimp only [traceFreeHessianDerivativeField, ContinuousMap.coe_mk,
    scalarTraceFreeHessian]
  split_ifs
  · exact (s.derivativeHessian k i j t e).sub
      ((s.derivativeLaplacian k t e).div_const 4)
  · simpa only [sub_zero] using s.derivativeHessian k i j t e

theorem traceFreeHessian_divergence (s : ScalarCovariantData d a)
    (e : FrameBundle g) (j : Fin 4) :
    (∑ i, s.traceFreeHessianDerivativeField i i j e) =
      (3 / 4 : ℝ) * ((∑ i, scalarThird g a e j i i) +
        4 * scalarGradient g a e j) := by
  simp only [traceFreeHessianDerivativeField, ContinuousMap.coe_mk,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [s.laplacianGradient_commute]
  ring

end ScalarCovariantData

theorem scalarTraceFreeHessian_pairing (e : FrameBundle g) :
    (∑ i, ∑ j, scalarTraceFreeHessian g a e i j * scalarHessian g a e i j) =
      ∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2 := by
  have ht := scalarTraceFreeHessian_trace (g := g) (a := a) e
  have hpoint (i j : Fin 4) :
      scalarTraceFreeHessian g a e i j * scalarHessian g a e i j =
        scalarTraceFreeHessian g a e i j ^ 2 +
          if i = j then scalarTraceFreeHessian g a e i i * scalarLaplacian g a e / 4
          else 0 := by
    by_cases h : i = j
    · subst j
      simp only [scalarTraceFreeHessian, ite_true, if_true]
      ring
    · simp only [scalarTraceFreeHessian, h, ite_false, if_false, sub_zero, add_zero]
      ring
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  rw [← Finset.sum_div, ← Finset.sum_mul]
  change _ + Matrix.trace (scalarTraceFreeHessian g a e) * scalarLaplacian g a e / 4 = _
  rw [ht, zero_mul, zero_div, add_zero]

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem ScalarCovariantData.weighted_traceFree_green
    (s : ScalarCovariantData d a) (v : ScalarCovariantData d w) :
    (∫ e, w e.base * (∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2) ∂μ) =
      -(∫ e, ∑ j, scalarGradient g a e j *
        ((∑ i, scalarGradient g w e i * scalarTraceFreeHessian g a e i j) +
          (3 / 4 : ℝ) * w e.base *
            ((∑ i, scalarThird g a e j i i) + 4 * scalarGradient g a e j)) ∂μ) := by
  let f (i j : Fin 4) : C(FrameBundle g, ℝ) :=
    v.valueField * s.traceFreeHessianField i j
  let df (i j : Fin 4) : C(FrameBundle g, ℝ) :=
    v.gradientField i * s.traceFreeHessianField i j +
      v.valueField * s.traceFreeHessianDerivativeField i i j
  have hd (i j : Fin 4) (t : ℝ) (e : FrameBundle g) :
      HasDerivAt (fun r => f i j ((d.flow i).map r e))
        (df i j ((d.flow i).map t e)) t :=
    (v.derivativeValue i t e).mul (s.derivativeTraceFreeHessian i i j t e)
  have hg (i j : Fin 4) := scalar_flow_green (d := d) i (f i j) (df i j)
    (s.gradientField j) (s.hessianField i j) (hd i j) (s.derivativeGradient i j)
  have hi (i j : Fin 4) : Integrable
      (fun e => df i j e * scalarGradient g a e j) μ :=
    ((df i j).continuous.mul (s.continuousGradient j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj (i j : Fin 4) : Integrable
      (fun e => f i j e * scalarHessian g a e i j) μ :=
    ((f i j).continuous.mul (s.continuousHessian i j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he := congrArg (fun z : Fin 4 → Fin 4 → ℝ => ∑ j, ∑ i, z i j)
    (funext fun i => funext fun j => hg i j)
  simp only [ScalarCovariantData.gradientField, ScalarCovariantData.hessianField,
    ContinuousMap.coe_mk, Finset.sum_neg_distrib] at he
  simp_rw [← integral_finsetSum _ (fun i _ => hi i _),
    ← integral_finsetSum _ (fun i _ => hj i _)] at he
  rw [← integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hi i j)),
    ← integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hj i j))] at he
  have hleft (e : FrameBundle g) :
      (∑ j, ∑ i, df i j e * scalarGradient g a e j) =
        ∑ j, scalarGradient g a e j *
          ((∑ i, scalarGradient g w e i * scalarTraceFreeHessian g a e i j) +
            (3 / 4 : ℝ) * w e.base *
              ((∑ i, scalarThird g a e j i i) + 4 * scalarGradient g a e j)) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [df, ContinuousMap.coe_add, ContinuousMap.coe_mul, Pi.add_apply,
      Pi.mul_apply, ScalarCovariantData.gradientField, ScalarCovariantData.valueField,
      ScalarCovariantData.traceFreeHessianField, ContinuousMap.coe_mk,
      add_mul, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum,
      s.traceFreeHessian_divergence]
    ring
  have hright (e : FrameBundle g) :
      (∑ j, ∑ i, f i j e * scalarHessian g a e i j) =
        w e.base * (∑ i, ∑ j, scalarTraceFreeHessian g a e i j ^ 2) := by
    simp only [f, ContinuousMap.coe_mul, Pi.mul_apply,
      ScalarCovariantData.valueField, ScalarCovariantData.traceFreeHessianField,
      ContinuousMap.coe_mk, mul_assoc]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_comm, scalarTraceFreeHessian_pairing]
  have hl := integral_congr_ae (μ := μ) (Filter.Eventually.of_forall hleft)
  have hr := integral_congr_ae (μ := μ) (Filter.Eventually.of_forall hright)
  linarith only [he, hl, hr]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The elementary Grassmannian calculation needed for the sectional
criterion. Two arbitrary unit coefficient vectors in the positive and
negative quaternion triples are realized by a genuine two-plane. -/

namespace PositiveEinsteinFour.SectionalPlane

open EinsteinFour Matrix Bianchi TraceHessian QuaternionFrame Angular
open scoped BigOperators

noncomputable section

/-- Every pair of unit imaginary quaternions admits a common vector on
which their actions are opposite. The trace-zero product makes its positive
projection nonzero. -/
theorem exists_common_vector (s t : Fin 3 → ℝ)
    (hs : ∑ i, s i ^ 2 = 1) (ht : ∑ i, t i ^ 2 = 1) :
    ∃ v : Vec4, ‖v‖ = 1 ∧
      act (imaginaryCombination quaternionMatrix s) v =
        -act (imaginaryCombination oppositeMatrix t) v := by
  let L := imaginaryCombination quaternionMatrix s
  let R := imaginaryCombination oppositeMatrix t
  have hL : L * L = -1 := by
    simpa only [L, hs, neg_one_smul] using
      imaginaryCombination_square quaternionMatrix quaternionMatrix_anticommutator s
  have hR : R * R = -1 := by
    simpa only [R, ht, neg_one_smul] using
      imaginaryCombination_square oppositeMatrix oppositeMatrix_anticommutator t
  have hcomm : R * L = L * R := by
    change R * (∑ i, s i • quaternionMatrix i) =
      (∑ i, s i • quaternionMatrix i) * R
    rw [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact congrArg (fun A : Geometry.Mat4 => s i • A)
      (imaginaryRight_commutes_positive t i)
  have htracePair (i j : Fin 3) : Matrix.trace (quaternionMatrix i * oppositeMatrix j) = 0 := by
    have hh := mixingCoefficient_trace i j
    rw [mixingCoefficient, quaternionMatrix_transpose, Matrix.neg_mul,
      Matrix.trace_neg] at hh
    linarith
  have htrace : Matrix.trace (L * R) = 0 := by
    simp only [L, R, imaginaryCombination, Matrix.sum_mul, Matrix.mul_sum,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
      Matrix.trace_smul, htracePair, smul_zero, Finset.sum_const_zero]
  let K : Geometry.Mat4 := 1 + L * R
  have hK : K ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.trace hz
    simp only [K, Matrix.trace_add, htrace, add_zero, Matrix.trace_one,
      Fintype.card_fin, Nat.cast_ofNat, Matrix.trace_zero] at hh
    norm_num at hh
  have hker : (L + R) * K = 0 := by
    calc
      _ = L + R + (L * L) * R + (R * L) * R := by dsimp [K]; noncomm_ring
      _ = L + R + (L * L) * R + L * (R * R) := by rw [hcomm]; noncomm_ring
      _ = 0 := by rw [hL, hR]; simp
  have hex : ∃ j : Fin 4, ∃ i : Fin 4, K i j ≠ 0 := by
    by_contra! hh
    apply hK
    ext i j
    exact hh j i
  obtain ⟨j, i, hij⟩ := hex
  let w : Vec4 := act K (WithLp.toLp 2 (Pi.single j 1))
  have hw : w ≠ 0 := by
    intro hz
    have hi := congrArg (fun v : Vec4 => v i) hz
    apply hij
    simpa [w, act] using hi
  let v : Vec4 := (‖w‖⁻¹ : ℝ) • w
  have hv : ‖v‖ = 1 := norm_smul_inv_norm hw
  refine ⟨v, hv, ?_⟩
  have hk : act (L + R) v = 0 := by
    change act (L + R) ((‖w‖⁻¹ : ℝ) • w) = 0
    rw [act_smul_vector]
    change ‖w‖⁻¹ • act (L + R) (act K (WithLp.toLp 2 (Pi.single j 1))) = 0
    rw [← act_mul, hker, act_zero, smul_zero]
  rw [act_add] at hk
  exact eq_neg_of_add_eq_zero_left hk

theorem exists_two_plane (s t : Fin 3 → ℝ)
    (hs : ∑ i, s i ^ 2 = 1) (ht : ∑ i, t i ^ 2 = 1) :
    ∃ u v : Vec4, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ u v = 0 ∧
      (∀ i, coefficient (quaternionMatrix i) u v = s i) ∧
      (∀ i, coefficient (oppositeMatrix i) u v = -t i) := by
  obtain ⟨v, hv, hpair⟩ := exists_common_vector s t hs ht
  let L := imaginaryCombination quaternionMatrix s
  let u := act L v
  have hLorth : Lᵀ * L = 1 :=
    imaginaryCombination_orthogonal quaternionMatrix quaternionMatrix_anticommutator
      quaternionMatrix_transpose s hs
  refine ⟨u, v, (act_norm L hLorth v).trans hv, hv, ?_, ?_, ?_⟩
  · exact act_skew_self L (imaginaryCombination_transpose quaternionMatrix
      quaternionMatrix_transpose s) v
  · intro i
    simpa only [u, L, hv, one_pow, mul_one] using
      coefficient_combination quaternionMatrix quaternion_gram s v i
  · intro i
    change coefficient (oppositeMatrix i) (act L v) v = -t i
    rw [hpair]
    simp only [coefficient, inner_neg_right]
    have hh := coefficient_combination oppositeMatrix opposite_gram t v i
    simpa only [coefficient, hv, one_pow, mul_one] using congrArg Neg.neg hh

end
end PositiveEinsteinFour.SectionalPlane
end


section

/-! Continuity of the actual weighted-Hessian integrands. The orthogonal
projection is the already constructed projection, not a chosen eigenframe. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem continuousFullHessian (d : MetricGreenData g μ) :
    Continuous (fun e : FrameBundle g => plusWeylHessian g e.base e.frame) :=
  continuous_pi (fun i => continuous_pi (d.continuousHessian i))

local instance hessianContinuityNormedRing_r0ded1c_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianContinuityNormedSpace_r0ded1c_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianContinuityNormedAlgebra_r0ded1c_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem continuousWeightTensor (d : MetricGreenData g μ)
    (dm : Fin 4 → C(FrameBundle g, ℝ)) :
    Continuous (fun e => weightTensor (WithLp.toLp 2 (fun i => dm i e))
      (plusGradientTensor g e.base e.frame)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  change Continuous (fun e => dm i e *
    (gradientTensor (plusWeylGradient g e.base e.frame)).matrix a b j)
  simp_rw [gradientTensor_matrix _ (d.gradientConstraints _).1]
  exact (dm i).continuous.mul
    ((continuous_apply b).comp ((continuous_apply a).comp (d.continuousGradient j)))

theorem continuousProjectionCost (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (m : C(FrameBundle g, ℝ)) (hm : ∀ e, 0 < m e)
    (dm : Fin 4 → C(FrameBundle g, ℝ)) :
    Continuous (fun e =>
      generalCurvaturePairing (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
        (highestProjection (weightTensor (WithLp.toLp 2 (fun i => dm i e))
          (plusGradientTensor g e.base e.frame)))
        (highestProjection (weightTensor (WithLp.toLp 2 (fun i => dm i e))
          (plusGradientTensor g e.base e.frame))) / (24 * m e)) := by
  have hP := continuous_highestProjection.comp (d.continuousWeightTensor dm)
  exact (continuous_generalCurvaturePairing d.continuousWeyl o.continuousWeyl hP hP).div
    (continuous_const.mul m.continuous) (fun e => mul_ne_zero (by norm_num) (ne_of_gt (hm e)))

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The nine commuting-quaternion products are an actual orthogonal
basis for symmetric trace-free scalar Hessians in four dimensions. -/

namespace PositiveEinsteinFour.ScalarHessian

open scoped BigOperators
open Matrix TraceHessian Angular HighestHessian

noncomputable section

def scalarNormSq (S : Matrix4) : ℝ := scalarPairing S S

end
end PositiveEinsteinFour.ScalarHessian
end


section

/-! All five Green integrals for the actual Weyl Hessian. The result has
only first derivatives and the constructed orthogonal-projection cost. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian CurvatureContraction MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

local instance hessianAssemblyNormedRing_r0ded1c_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance hessianAssemblyNormedSpace_r0ded1c_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance hessianAssemblyNormedAlgebra_r0ded1c_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def plusMatrixMap (d : MetricGreenData g μ) : C(FrameBundle g, Mat) :=
  ⟨fun e => plusWeyl g e.base e.frame, d.continuousWeyl⟩

def minusMatrixMap (d : MetricGreenData g μ) (o : OppositeWeylData d) : C(FrameBundle g, Mat) :=
  ⟨fun e => minusWeyl g e.base e.frame, o.continuousWeyl⟩

def gradientMap (d : MetricGreenData g μ) : C(FrameBundle g, Fin 4 → Mat) :=
  ⟨fun e => plusWeylGradient g e.base e.frame, continuous_pi d.continuousGradient⟩

def hessianMap (d : MetricGreenData g μ) : C(FrameBundle g, Hessian) :=
  ⟨fun e => plusWeylHessian g e.base e.frame, d.continuousFullHessian⟩

def weightTensorMap (d : MetricGreenData g μ) (dm : Fin 4 → C(FrameBundle g, ℝ)) :
    C(FrameBundle g, Hessian) :=
  ⟨fun e => weightTensor (WithLp.toLp 2 (fun i => dm i e)) (plusGradientTensor g e.base e.frame),
    d.continuousWeightTensor dm⟩

def hessianIdentityField (d : MetricGreenData g μ) (m : C(FrameBundle g, ℝ))
    (dm : Fin 4 → C(FrameBundle g, ℝ)) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weightedQuadratic hessianNormSq (m e) (d.hessianMap e) (d.weightTensorMap dm e),
    continuous_weightedQuadratic (fun W hW => by
      simpa only [hessianPairing_self] using continuous_hessianPairing hW hW)
      m.continuous (d.hessianMap.continuous) (d.weightTensorMap dm).continuous⟩

def hessianPlusField (d : MetricGreenData g μ) (m : C(FrameBundle g, ℝ))
    (dm : Fin 4 → C(FrameBundle g, ℝ)) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weightedQuadratic
    (fun W => derivativePairing (generalCoefficient quaternionMatrix (d.plusMatrixMap e)) W W)
    (m e) (d.hessianMap e) (d.weightTensorMap dm e),
    continuous_weightedQuadratic
      (q := fun e W => derivativePairing (generalCoefficient quaternionMatrix (d.plusMatrixMap e)) W W)
      (m := m) (X := d.hessianMap) (L := d.weightTensorMap dm)
      (fun W hW => continuous_derivativePairing (X := W) (Y := W)
        (continuous_generalCoefficient quaternionMatrix d.plusMatrixMap.continuous) hW hW)
      m.continuous d.hessianMap.continuous (d.weightTensorMap dm).continuous⟩

def hessianMatrixField (d : MetricGreenData g μ) (m : C(FrameBundle g, ℝ))
    (dm : Fin 4 → C(FrameBundle g, ℝ)) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weightedQuadratic (fun W => matrixHessianPairing (d.plusMatrixMap e) W W)
    (m e) (d.hessianMap e) (d.weightTensorMap dm e),
    continuous_weightedQuadratic
      (q := fun e W => matrixHessianPairing (d.plusMatrixMap e) W W)
      (m := m) (X := d.hessianMap) (L := d.weightTensorMap dm)
      (fun W hW => continuous_matrixHessianPairing (X := W) (Y := W)
        d.plusMatrixMap.continuous hW hW)
      m.continuous d.hessianMap.continuous (d.weightTensorMap dm).continuous⟩

def hessianMinusField (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ)) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weightedQuadratic
    (fun W => derivativePairing (generalCoefficient Angular.oppositeMatrix (d.minusMatrixMap o e)) W W)
    (m e) (d.hessianMap e) (d.weightTensorMap dm e),
    continuous_weightedQuadratic
      (q := fun e W => derivativePairing (generalCoefficient Angular.oppositeMatrix (d.minusMatrixMap o e)) W W)
      (m := m) (X := d.hessianMap) (L := d.weightTensorMap dm)
      (fun W hW => continuous_derivativePairing (X := W) (Y := W)
        (continuous_generalCoefficient Angular.oppositeMatrix (d.minusMatrixMap o).continuous) hW hW)
      m.continuous d.hessianMap.continuous (d.weightTensorMap dm).continuous⟩

def traceComponentMap (d : MetricGreenData g μ) : C(FrameBundle g, Hessian) :=
  ⟨fun e => traceComponent (weylLaplacian (d.plusMatrixMap e)),
    continuous_traceComponent.comp (continuous_weylLaplacian.comp d.plusMatrixMap.continuous)⟩

def hessianTraceField (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ)) : C(FrameBundle g, ℝ) :=
  ⟨fun e => generalTraceCorrection (d.plusMatrixMap e) (d.minusMatrixMap o e)
    (weylLaplacian (d.plusMatrixMap e)) (m e) (d.weightTensorMap dm e),
    (((m.continuous.mul (continuous_generalCurvaturePairing d.plusMatrixMap.continuous
      (d.minusMatrixMap o).continuous d.traceComponentMap.continuous d.traceComponentMap.continuous)).add
      (continuous_generalCurvaturePairing d.plusMatrixMap.continuous (d.minusMatrixMap o).continuous
        d.traceComponentMap.continuous (d.weightTensorMap dm).continuous)).neg).div_const 6⟩

def hessianCostField (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (m : C(FrameBundle g, ℝ)) (hm : ∀ e, 0 < m e) (dm : Fin 4 → C(FrameBundle g, ℝ)) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => generalCurvaturePairing (d.plusMatrixMap e) (d.minusMatrixMap o e)
      (highestProjection (d.weightTensorMap dm e)) (highestProjection (d.weightTensorMap dm e)) /
        (24 * m e), d.continuousProjectionCost o m hm dm⟩

def gradientEnergyField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weylGradientEnergy (d.gradientMap e), continuous_weylGradientEnergy d.gradientMap.continuous⟩

def matrixEnergyField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weylMatrixEnergy (d.plusMatrixMap e) (d.gradientMap e),
    continuous_weylMatrixEnergy d.plusMatrixMap.continuous d.gradientMap.continuous⟩

def squareEnergyField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weylMatrixEnergy (traceFreeSquare (d.plusMatrixMap e)) (d.gradientMap e),
    continuous_weylMatrixEnergy (continuous_traceFreeSquare.comp d.plusMatrixMap.continuous)
      d.gradientMap.continuous⟩

def compressionEnergyField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weylCompressionEnergy (d.plusMatrixMap e) (d.gradientMap e),
    continuous_weylCompressionEnergy d.plusMatrixMap.continuous d.gradientMap.continuous
      (fun e => (d.gradientConstraints e).1)⟩

def radialEnergyField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => weylRadialSquare (d.plusMatrixMap e) (d.gradientMap e),
    continuous_weylRadialSquare d.plusMatrixMap.continuous d.gradientMap.continuous⟩

def plusNormField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => normalizedBlockNorm (d.plusMatrixMap e),
    continuous_normalizedBlockNorm.comp d.plusMatrixMap.continuous⟩

def minusNormField (d : MetricGreenData g μ) (o : OppositeWeylData d) : C(FrameBundle g, ℝ) :=
  ⟨fun e => normalizedBlockNorm (d.minusMatrixMap o e),
    continuous_normalizedBlockNorm.comp (d.minusMatrixMap o).continuous⟩

def weightCubicField (d : MetricGreenData g μ) (dm : Fin 4 → C(FrameBundle g, ℝ)) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => ∑ i, dm i e * Matrix.trace (d.gradientMap e i *
    (∑ j, d.gradientMap e j * d.gradientMap e j)), by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sum_apply]
      fun_prop⟩

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual projection term in the metric Hessian estimate converges
under norm regularization, including at zeros of either Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def regularizedProjectionCost (g : SmoothMetric M) (ε : ℝ) (e : FrameBundle g) : ℝ :=
  let A := plusWeyl g e.base e.frame
  let U := minusWeyl g e.base e.frame
  let Z := plusWeylGradient g e.base e.frame
  let V := minusWeylGradient g e.base e.frame
  let a : Vec := WithLp.toLp 2 (fun i => regularizedWeylWeightDerivative ε A U (Z i) (V i))
  let L := weightTensor a (gradientTensor Z)
  generalCurvaturePairing A U (highestProjection L) (highestProjection L) /
    (24 * regularizedWeylWeight ε A U)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine smooth norm weights in the actual metric Hessian estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def regularizedHessianIntegrand (g : SmoothMetric M) (ε : ℝ) (e : FrameBundle g) : ℝ :=
  let A := plusWeyl g e.base e.frame
  let U := minusWeyl g e.base e.frame
  let Z := plusWeylGradient g e.base e.frame
  let V := minusWeylGradient g e.base e.frame
  let m := regularizedWeylWeight ε A U
  let a : Vec := WithLp.toLp 2 (fun i => regularizedWeylWeightDerivative ε A U (Z i) (V i))
  let L := weightTensor a (gradientTensor Z)
  m * invariantHessianForm A U Z -
    (5 / 36 : ℝ) * (∑ i, a i * Matrix.trace (Z i * (∑ j, Z j * Z j))) +
    generalCurvaturePairing A U (highestProjection L) (highestProjection L) / (24 * m)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sectional criterion from actual two-planes. The quaternionic
Grassmann calculation and the minimum-eigenvalue argument connect sectional
positivity with the Riemann curvature decomposition and symmetry identities. -/

namespace PositiveEinsteinFour.SectionalPlane

open EinsteinFour Matrix Bianchi TraceHessian QuaternionFrame Angular
open scoped BigOperators Manifold ContDiff

noncomputable section

/-- Positivity on actual two-planes bounds every pair of unit block
Rayleigh quotients; both blocks can be minimized independently. -/
theorem rayleigh_sum_pos (A B : Geometry.Mat3)
    (hp : ∀ u v : Vec4, LinearIndependent ℝ ![u, v] →
      0 < sectionalValue (einsteinCurvatureTensor A B) u v)
    (s t : EuclideanSpace ℝ (Fin 3)) (hs : ‖s‖ = 1) (ht : ‖t‖ = 1) :
    0 < 2 + quadratic A s + quadratic B t := by
  have hs2 : ∑ i, s i ^ 2 = 1 := by
    simpa only [hs, one_pow] using (EuclideanSpace.real_norm_sq_eq s).symm
  have ht2 : ∑ i, t i ^ 2 = 1 := by
    simpa only [ht, one_pow] using (EuclideanSpace.real_norm_sq_eq t).symm
  obtain ⟨u, v, hu, hv, huv, hplus, hminus⟩ := exists_two_plane s t hs2 ht2
  have hpos := hp u v (plane_independent hu hv huv)
  have hform : sectionalValue (einsteinCurvatureTensor A B) u v =
      (2 + quadratic A s + quadratic B t) / 2 := by
    rw [einsteinCurvatureTensor, sectionalValue_add, sectionalValue_blockTensor,
      sectionalValue_blockTensor]
    simp_rw [hplus, hminus]
    have hnA : quadratic (1 + A) s = quadratic A s + 1 := by
      rw [add_comm (1 : Geometry.Mat3) A]
      simpa only [one_smul, hs, one_pow, mul_one] using quadratic_add_scalar A 1 s
    have hnB : quadratic (1 + B) t = quadratic B t + 1 := by
      rw [add_comm (1 : Geometry.Mat3) B]
      simpa only [one_smul, ht, one_pow, mul_one] using quadratic_add_scalar B 1 t
    dsimp [quadratic] at hnA hnB ⊢
    simp only [mul_neg, neg_mul, neg_neg]
    linarith
  rw [hform] at hpos
  linarith

/-- The published sectional criterion follows from the proved plane
realization and elementary extrema on two unit spheres. -/
theorem shifts_of_positive_planes (A B : Geometry.Mat3)
    (hA : symmetric A) (hB : symmetric B)
    (hp : ∀ u v : Vec4, LinearIndependent ℝ ![u, v] →
      0 < sectionalValue (einsteinCurvatureTensor A B) u v) :
    ∃ x y : ℝ, (A + x • (1 : Geometry.Mat3)).PosSemidef ∧
      (B + y • (1 : Geometry.Mat3)).PosSemidef ∧ x + y < 2 := by
  obtain ⟨s, hs, hAs⟩ := exists_minimum_shift A hA
  obtain ⟨t, ht, hBt⟩ := exists_minimum_shift B hB
  have hpos := rayleigh_sum_pos A B hp s t hs ht
  exact ⟨-quadratic A s, -quadratic B t, hAs, hBt, by linarith⟩

end
end PositiveEinsteinFour.SectionalPlane
namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix SectionalPlane
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The pointwise sectional threshold follows from
ordinary curvature-block symmetry/decomposition and actual positive
sectional curvature. No eigenvalue/sectional estimate is a premise. -/
theorem sectionalInput_of_curvature_decomposition (g : SmoothMetric M)
    (hdecomp : RicciThree g → ∀ c (e : OrthonormalFrame g c), frameCurvature g c e =
      Angular.einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e))
    (hplus : ∀ e : FrameBundle g, TraceHessian.symmetric (plusWeyl g e.base e.frame))
    (hminus : ∀ e : FrameBundle g, TraceHessian.symmetric (minusWeyl g e.base e.frame)) :
    GurskyLeBrunSectionalInput g := by
  intro hRic hsec e
  apply shifts_of_positive_planes _ _ (hplus e) (hminus e)
  intro u v huv
  rw [← hdecomp hRic e.base e.frame, sectionalValue_frame]
  exact e.frame.sectional_pos hsec u v huv

end
end PositiveEinsteinFour.Geometry
end


section

/-! The refined Kato bound in an arbitrary orthonormal frame, including
the zero Weyl block. The pointwise spectral frame is constructed, and the
Bianchi condition is transported by its actual quaternion lift. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

/-- Refined Kato for the actual radial derivative of a symmetric
trace-free block. No nonvanishing or eigenframe premise is required. -/
theorem blockRadialGradient_refined_kato (A : Mat) (Z : Angular.Gradient)
    (hA : symmetric A) (htA : traceFree A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) :
    (5 / 3 : ℝ) * ‖blockRadialGradient A Z‖ ^ 2 ≤ weylGradientEnergy Z := by
  by_cases hv : normalizedBlockNorm A = 0
  · have hp : blockRadialGradient A Z = 0 := by
      ext i
      simp [blockRadialGradient, regularizedRadialDerivative,
        regularizedBlockNorm_zero, hv]
    rw [hp, norm_zero, zero_pow (by decide), mul_zero]
    unfold weylGradientEnergy matrixPairing
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => mul_self_nonneg (Z i a b)
  have hvp : 0 < normalizedBlockNorm A :=
    lt_of_le_of_ne (normalizedBlockNorm_nonneg A) (Ne.symm hv)
  obtain ⟨R, hR, ⟨P⟩, S, hS⟩ := exists_lifted_spectral_shape A hA htA hvp
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  let W := turnGradient R P.matrix Z
  have hsW : ∀ i, symmetric (W i) := turnGradient_symmetric R P.matrix Z hs
  have htW : ∀ i, traceFree (W i) := turnGradient_traceFree R hR' P.matrix Z ht
  have hbW : ∀ r i, gradientDivergence W r i = 0 := turnGradient_bianchi R hR' P Z hb
  have hnorm : normalizedBlockNorm (Matrix.diagonal (fun i => normalizedBlockNorm A * S.s i)) =
      normalizedBlockNorm A := by
    rw [← hS]
    exact conjugateMatrix_norm R hR' A
  have hp : blockRadialGradient (conjugateMatrix R A) W =
      radialCoordinate S (gradientTensor W) := by
    rw [show conjugateMatrix R A = _ from hS,
      blockRadialGradient_diagonal S (normalizedBlockNorm A) W,
      hnorm, div_self hv, one_smul]
  have hk := refined_kato S (gradientTensor W)
    (gradientTensor_traceFree W htW) (gradientTensor_bianchi W hsW hbW)
  rw [gradientTensor_energy W hsW, ← hp] at hk
  have hnormeq : ‖blockRadialGradient (conjugateMatrix R A) W‖ ^ 2 =
      ‖blockRadialGradient A Z‖ ^ 2 := by
    rw [blockRadialGradient_turn R hR' P.matrix A Z,
      turnVector_norm P.matrix P.mul_transpose]
  rw [hnormeq, weylGradientEnergy_turn R hR' P.matrix P.mul_transpose] at hk
  exact hk

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The actual global Hessian inequality for the nonsmooth norm weight.
The limit is proved on the original Weyl tensors, including their zeros. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def invariantHessianField (d : MetricGreenData g μ) (o : OppositeWeylData d) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => invariantHessianForm (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
    (plusWeylGradient g e.base e.frame), by
      change Continuous (fun e =>
        (-42 - 3 * d.minusNormField o e ^ 2 - (10 / 3 : ℝ) * d.plusNormField e ^ 2) *
          d.gradientEnergyField e + 75 * d.matrixEnergyField e +
          (25 / 3 : ℝ) * d.squareEnergyField e -
          (100 / 3 : ℝ) * d.compressionEnergyField e + 5 * d.radialEnergyField e)
      fun_prop⟩

def cubicEntryField (d : MetricGreenData g μ) (i : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => -(5 / 36 : ℝ) * Matrix.trace (d.gradientMap e i *
    (∑ j, d.gradientMap e j * d.gradientMap e j)), by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sum_apply]
      fun_prop⟩

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The regularized scalar Weyl equation follows from ordinary derivatives
of the actual block and its proved matrix Laplacian. Test functions are
arbitrary smooth flow weights, ready for the polynomial coupling test. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normEquationNormedRing
local instance normEquationNormedSpace_r0ded1c_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normEquationNormedAlgebra
def regularizedNormField (d : MetricGreenData g μ) (ε : ℝ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedBlockNorm ε (plusWeyl g e.base e.frame),
    (continuous_regularizedBlockNorm ε).comp d.continuousWeyl⟩

def regularizedRadialField (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε) (i : Fin 4) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedRadialDerivative ε (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i),
    continuous_regularizedRadialDerivative ε hε _ _ d.continuousWeyl (d.continuousGradient i)⟩

def regularizedSecondField (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε) (i : Fin 4) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedRadialSecond ε (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (plusWeylHessian g e.base e.frame i i),
    continuous_regularizedRadialSecond ε hε _ _ _ d.continuousWeyl
      (d.continuousGradient i) (d.continuousHessian i i)⟩

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The integrated scalar-Hessian curvature identity. The only
differential inputs are the raw scalar and Weyl parallel-frame derivatives
and Ricci commutator. Coefficient divergence and the exact contraction are
proved from the Bianchi equation and the finite-dimensional calculations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Bianchi CurvatureContraction ScalarHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
  {a : M → ℝ}

def scalarWeylHessianForm (g : SmoothMetric M) (a : M → ℝ) (e : FrameBundle g) : ℝ :=
  blockQuadratic quaternionMatrix (plusWeyl g e.base e.frame) (scalarHessian g a e) +
    blockQuadratic Angular.oppositeMatrix (minusWeyl g e.base e.frame) (scalarHessian g a e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite curvature reconstruction for the orthonormal-frame tensor, using
metric skew-adjointness of the curvature operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem sectionalInput_of_lastSkew
    (hl : ∀ c (e : OrthonormalFrame g c),
      AlgebraicCurvature.LastSkew (frameCurvature g c e)) :
    GurskyLeBrunSectionalInput g := by
  apply sectionalInput_of_curvature_decomposition g
  · intro hRic c e
    exact frame_einstein_decomposition_of_lastSkew e (hl c e) hRic
  · intro e
    exact (frame_weyl_symmetric_of_lastSkew e.frame (hl e.base e.frame)).1
  · intro e
    exact (frame_weyl_symmetric_of_lastSkew e.frame (hl e.base e.frame)).2

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationFrameClass_proj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual smooth metric supplies the algebraic curvature identities.
No curvature decomposition or sectional criterion is a premise here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem actual_sectionalInput (g : SmoothMetric M) : GurskyLeBrunSectionalInput g :=
  sectionalInput_of_lastSkew (fun _ e => frame_algebraic_lastSkew e)

/-- Strict pointwise pinching of the normalized Weyl norms follows from
positive sectional curvature and the actual algebraic curvature identities. -/
theorem actual_norm_pinching (hRic : RicciThree g)
    (hsec : HasPositiveSectionalCurvature g) (e : FrameBundle g) :
    normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2 := by
  obtain ⟨x, y, hx, hy, hxy⟩ := actual_sectionalInput g hRic hsec e
  have hs := actual_weyl_symmetric e.frame
  have ht := actual_weyl_traceFree e.frame hRic
  have hp := QuaternionFrame.normalizedBlockNorm_le_shift _ hs.1 ht.1 x hx
  have hm := QuaternionFrame.normalizedBlockNorm_le_shift _ hs.2 ht.2 y hy
  linarith only [hp, hm, hxy]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The fixed reflection is continuous in the actual tangent-bundle
topology, and hence defines a measurable involution of the frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameReflectionEquiv (g : SmoothMetric M) : FrameBundle g ≃ᵐ FrameBundle g where
  toFun := frameReflection
  invFun := frameReflection
  left_inv := frameReflection_involutive g
  right_inv := frameReflection_involutive g
  measurable_toFun := (continuous_frameReflection g).measurable
  measurable_invFun := (continuous_frameReflection g).measurable

end
end PositiveEinsteinFour.Geometry
end


section

/-! The singular Weyl energy quotient is integrable. The refined Kato
inequality is kept as a local intermediate input, to be supplied by the
pointwise Bianchi parametrization; no weak norm equation is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

local instance normIntegrabilityNormedRing_r0ded1c_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance normIntegrabilityNormedSpace_r0ded1c_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance normIntegrabilityNormedAlgebra_r0ded1c_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
def laplacianNormField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => normalizedBlockNorm (weylLaplacian (plusWeyl g e.base e.frame)),
    continuous_normalizedBlockNorm.comp (continuous_weylLaplacian.comp d.continuousWeyl)⟩

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive sectional curvature makes the actual normal Jacobi curvature
matrix positive semidefinite. No separate matrix-positivity input is needed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix SectionalPlane
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem frameJacobiMatrix_quadratic (e : FrameBundle g) (v : Fin 3 → ℝ) :
    star v ⬝ᵥ ((1 + frameCurvatureField g e) *ᵥ v) =
      sectionalValue (frameCurvature g e.base e.frame)
        (normalCoordinates v) (coordinateVector 0) := by
  have hs : sectionalValue (frameCurvature g e.base e.frame)
      (normalCoordinates v) (coordinateVector 0) =
      ∑ i, ∑ j, frameCurvature g e.base e.frame i.succ 0 0 j.succ * v i * v j := by
    simp [sectionalValue, normalCoordinates, coordinateVector,
      Fin.sum_univ_four, Fin.sum_univ_three]
    rfl
  rw [hs]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
    Finset.mul_sum, frameJacobiMatrix_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positivity of sectional curvatures implies the actual radial matrix
is positive semidefinite, including its zero-vector quadratic value. -/
theorem actual_jacobi_posSemidef (hsec : HasPositiveSectionalCurvature g)
    (e : FrameBundle g) : (1 + frameCurvatureField g e).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr (frameJacobiMatrix_symmetric e)
  · intro v
    rw [frameJacobiMatrix_quadratic]
    by_cases hv : v = 0
    · have hn : normalCoordinates v = 0 := by
        subst v
        ext i
        fin_cases i <;> rfl
      simp [hn, sectionalValue]
    · have hu : normalCoordinates v ≠ 0 := normalCoordinates_ne_zero hv
      have hz : coordinateVector (0 : Fin 4) ≠ 0 := by
        intro he
        have h := congrArg (fun w : FourSpace => w 0) he
        norm_num [coordinateVector] at h
      have hlin : LinearIndependent ℝ ![normalCoordinates v, coordinateVector 0] := by
        apply linearIndependent_of_ne_zero_of_inner_eq_zero
        · intro i
          fin_cases i
          · exact hu
          · exact hz
        · intro i j hij
          fin_cases i <;> fin_cases j
          · exact False.elim (hij rfl)
          · exact normalCoordinates_orthogonal v
          · change inner ℝ (coordinateVector 0) (normalCoordinates v) = 0
            rw [real_inner_comm]
            exact normalCoordinates_orthogonal v
          · exact False.elim (hij rfl)
      rw [sectionalValue_frame]
      exact (e.frame.sectional_pos hsec _ _ hlin).le

end
end PositiveEinsteinFour.Geometry
end


section

/-! Pass the actual weak norm equation through bounded smooth test
approximations, including their first derivatives. This is the limit used
for the polynomial multiplier in the two-block coupling. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped BigOperators _root_.Topology Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def scalarNormField (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => scalarNormExpression ε (plusWeyl g e.base e.frame)
    (plusWeylGradient g e.base e.frame), by
    have hP : Continuous (fun e => ∑ i, (d.regularizedRadialField ε hε i e) ^ 2) := by
      fun_prop
    exact ((d.gradientEnergyField.continuous.sub hP).div (d.regularizedNormField ε).continuous
      (fun e => (regularizedBlockNorm_pos ε hε _).ne')).add
        (continuous_regularizedRadialDerivative ε hε _ _ d.continuousWeyl
          (continuous_weylLaplacian.comp d.continuousWeyl))⟩

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weak Bochner equation for the actual Weyl derivative energy.
This is the identity used to prove the sign of equation (16). -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def energyDerivativeField (d : MetricGreenData g μ) (i : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => inner ℝ (frameGradientVector g e) (frameHessianVector g i e) / 3,
    (d.continuousGradientVector.inner (d.continuousHessianVector i)).div_const 3⟩

def energyLaplacianField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => hessianNormSq (plusWeylHessian g e.base e.frame) / 3 +
      26 * weylGradientEnergy (plusWeylGradient g e.base e.frame) -
      40 * weylMatrixEnergy (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame), by
    have hX : Continuous (fun e : FrameBundle g => hessianNormSq (plusWeylHessian g e.base e.frame)) := by
      simpa only [hessianPairing_self, hessianMap, ContinuousMap.coe_mk] using
        continuous_hessianPairing d.hessianMap.continuous d.hessianMap.continuous
    exact ((hX.div_const 3).add (continuous_const.mul d.gradientEnergyField.continuous)).sub
      (continuous_const.mul d.matrixEnergyField.continuous)⟩

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The cube root of the positive regularized Weyl norm satisfies the
scalar differential inequality forced by the Weyl equation and refined Kato. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance rootKatoNormedRing_r0ded1c_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance rootKatoNormedSpace_r0ded1c_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance rootKatoNormedAlgebra_r0ded1c_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
theorem regularized_radial_refined_kato (ε : ℝ) (hε : 0 < ε)
    (A : Mat) (Z : Fin 4 → Mat) (hA : symmetric A) (htA : traceFree A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) :
    (5 / 3 : ℝ) * (∑ i, regularizedRadialDerivative ε A (Z i) ^ 2) ≤
      weylGradientEnergy Z := by
  have hk := QuaternionFrame.blockRadialGradient_refined_kato A Z hA htA hs ht hb
  have hr := regularized_radial_energy_le ε hε A Z
  linarith

theorem regularizedWeylRootSecond_trace_lower (ε : ℝ) (hε : 0 < ε)
    (A : Mat) (Z : Fin 4 → Mat) (X : Hessian)
    (hA : symmetric A) (htA : traceFree A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0)
    (hX : hessianTrace X = weylLaplacian A) :
    Matrix.trace (A * weylLaplacian A) /
        (18 * regularizedBlockNorm ε A ^ (5 / 3 : ℝ)) ≤
      ∑ i, regularizedWeylRootSecond ε A (Z i) (X i i) := by
  rw [regularizedWeylRootSecond_sum ε hε A Z X hs hX]
  have hk := regularized_radial_refined_kato ε hε A Z hA htA hs ht hb
  have hn := regularizedBlockNorm_pos ε hε A
  have hh := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (Real.rpow_nonneg hn.le (-5 / 3 : ℝ)))
    (sub_nonneg.mpr hk)
  have hexp : regularizedBlockNorm ε A ^ (-5 / 3 : ℝ) =
      (regularizedBlockNorm ε A ^ (5 / 3 : ℝ))⁻¹ := by
    simpa only [neg_div] using Real.rpow_neg hn.le (5 / 3 : ℝ)
  have heq : Matrix.trace (A * weylLaplacian A) /
      (18 * regularizedBlockNorm ε A ^ (5 / 3 : ℝ)) =
      (1 / 3 : ℝ) * regularizedBlockNorm ε A ^ (-5 / 3 : ℝ) *
        (Matrix.trace (A * weylLaplacian A) / 6) := by
    rw [hexp]
    ring
  rw [heq]
  nlinarith only [hh]

/-- The pointwise differential inequality for
`(normalizedBlockNorm A ^ 2 + ε ^ 2) ^ (1/6)`. -/
theorem regularizedWeylRootSecond_lower (ε : ℝ) (hε : 0 < ε)
    (A : Mat) (Z : Fin 4 → Mat) (X : Hessian)
    (hA : symmetric A) (htA : traceFree A)
    (hs : ∀ i, symmetric (Z i)) (ht : ∀ i, traceFree (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0)
    (hX : hessianTrace X = weylLaplacian A) :
    2 * normalizedBlockNorm A ^ 2 * (1 - normalizedBlockNorm A) /
        regularizedBlockNorm ε A ^ (5 / 3 : ℝ) ≤
      ∑ i, regularizedWeylRootSecond ε A (Z i) (X i i) := by
  refine le_trans ?_ (regularizedWeylRootSecond_trace_lower ε hε A Z X
    hA htA hs ht hb hX)
  have hn := regularizedBlockNorm_pos ε hε A
  have h := div_le_div_of_nonneg_right (weylLaplacian_trace_lower A hA htA)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) (Real.rpow_nonneg hn.le (5 / 3 : ℝ)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace MetricGreenData

variable {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem regularizedWeylRoot_derivative (d : MetricGreenData g μ)
    (ε : ℝ) (hε : 0 < ε) (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => regularizedWeylRoot ε
      (plusWeyl g ((d.flow i).map s e).base ((d.flow i).map s e).frame))
      (regularizedWeylRootFirst ε
        (plusWeyl g ((d.flow i).map t e).base ((d.flow i).map t e).frame)
        (plusWeylGradient g ((d.flow i).map t e).base ((d.flow i).map t e).frame i)) t :=
  hasDerivAt_regularizedWeylRoot (d.derivativeWeyl i t e)
    (fun s => d.weyl.symmetric ((d.flow i).map s e)) hε

theorem regularizedWeylRootFirst_derivative (d : MetricGreenData g μ)
    (ε : ℝ) (hε : 0 < ε) (i : Fin 4) (t : ℝ) (e : FrameBundle g) :
    HasDerivAt (fun s => regularizedWeylRootFirst ε
      (plusWeyl g ((d.flow i).map s e).base ((d.flow i).map s e).frame)
      (plusWeylGradient g ((d.flow i).map s e).base ((d.flow i).map s e).frame i))
      (regularizedWeylRootSecond ε
        (plusWeyl g ((d.flow i).map t e).base ((d.flow i).map t e).frame)
        (plusWeylGradient g ((d.flow i).map t e).base ((d.flow i).map t e).frame i)
        (plusWeylHessian g ((d.flow i).map t e).base ((d.flow i).map t e).frame i i)) t :=
  hasDerivAt_regularizedWeylRootFirst (d.derivativeWeyl i t e)
    (d.derivativeGradient i i t e) (fun s => d.weyl.symmetric ((d.flow i).map s e)) hε

/-- The actual metric flow has the regularized lower Laplacian bound;
all algebraic gradient and Weyl-equation hypotheses come from its proved data. -/
theorem regularizedWeylRoot_lower (d : MetricGreenData g μ)
    (ε : ℝ) (hε : 0 < ε) (e : FrameBundle g) :
    2 * normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 *
        (1 - normalizedBlockNorm (plusWeyl g e.base e.frame)) /
        regularizedBlockNorm ε (plusWeyl g e.base e.frame) ^ (5 / 3 : ℝ) ≤
      ∑ i, regularizedWeylRootSecond ε (plusWeyl g e.base e.frame)
        (plusWeylGradient g e.base e.frame i) (plusWeylHessian g e.base e.frame i i) :=
  regularizedWeylRootSecond_lower ε hε _ _ _ (d.weyl.symmetric e) (d.weyl.traceFree e)
    (d.gradientConstraints e).1 (d.gradientConstraints e).2 (d.gradientBianchi e)
    (metric_weyl_trace g d.weyl e)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariant differentiation and framing preserve the algebraic first
Bianchi identity as well as the pair and alternating symmetries. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frame_normalizedWeyl_derivative_firstBianchi (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (d : Fin 4) :
    AlgebraicCurvature.FirstBianchi (curvatureDerivativeArray (frameTensor e.matrix
      (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))) d) := by
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  rw [covariantDerivative_normalizedWeyl g c (chartAt FourSpace c c) hz (chartMetric_posDef g c).det_pos.ne']
  exact frameTensor_firstBianchi e.matrix
    (covariantDerivative g c (curvatureCoordinates g c) (chartAt FourSpace c c))
    (curvatureDerivative_firstBianchi g c (chartAt FourSpace c c) hz
      (chartMetric_posDef g c).det_pos.ne') d

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrating the positive regularized cube root gives an energy
bound with an error tending to zero, without singular gradient limits. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

def weylRootField (d : MetricGreenData g μ) (ε : ℝ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedWeylRoot ε (plusWeyl g e.base e.frame),
    (continuous_regularizedWeylRoot ε).comp d.continuousWeyl⟩

def weylRootFirstField (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε) (i : Fin 4) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedWeylRootFirst ε (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i),
    continuous_regularizedWeylRootFirst ε hε _ _ d.continuousWeyl (d.continuousGradient i)⟩

def weylRootSecondField (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε) (i : Fin 4) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedWeylRootSecond ε (plusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame i) (plusWeylHessian g e.base e.frame i i),
    continuous_regularizedWeylRootSecond ε hε _ _ _ d.continuousWeyl
      (d.continuousGradient i) (d.continuousHessian i i)⟩

theorem weylRoot_error_le (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε)
    (e : FrameBundle g) :
    2 * d.weylRootField ε e ^ 2 -
        2 * normalizedBlockNorm (plusWeyl g e.base e.frame) * d.weylRootField ε e ^ 2 -
        d.weylRootField ε e * (∑ i, d.weylRootSecondField ε hε i e) ≤
      2 * ε ^ (2 / 3 : ℝ) := by
  let A := plusWeyl g e.base e.frame
  let u := regularizedBlockNorm ε A
  have hu : 0 < u := regularizedBlockNorm_pos ε hε A
  have hs : u ^ 2 = normalizedBlockNorm A ^ 2 + ε ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hb := cubeRoot_regularization_error_le (normalizedBlockNorm A) ε u
    (normalizedBlockNorm_nonneg A) hε hu hs
  have hl := mul_le_mul_of_nonneg_left (d.regularizedWeylRoot_lower ε hε e)
    (Real.rpow_nonneg hu.le (1 / 3 : ℝ))
  change 2 * (u ^ (1 / 3 : ℝ)) ^ 2 -
      2 * normalizedBlockNorm A * (u ^ (1 / 3 : ℝ)) ^ 2 -
      u ^ (1 / 3 : ℝ) * (∑ i, d.weylRootSecondField ε hε i e) ≤ _
  change u ^ (1 / 3 : ℝ) *
      (2 * normalizedBlockNorm A ^ 2 * (1 - normalizedBlockNorm A) /
        u ^ (5 / 3 : ℝ)) ≤
      u ^ (1 / 3 : ℝ) * (∑ i, d.weylRootSecondField ε hε i e) at hl
  linarith

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem weylRoot_energy_eq (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε) :
    (∫ e, ∑ i, d.weylRootFirstField ε hε i e ^ 2 ∂μ) =
      -(∫ e, d.weylRootField ε e * (∑ i, d.weylRootSecondField ε hε i e) ∂μ) := by
  have hi (i : Fin 4) := scalar_flow_green (d := d) i (d.weylRootField ε)
    (d.weylRootFirstField ε hε i) (d.weylRootFirstField ε hε i)
    (d.weylRootSecondField ε hε i) (d.regularizedWeylRoot_derivative ε hε i)
    (d.regularizedWeylRootFirst_derivative ε hε i)
  have hfirst (i : Fin 4) : Integrable (fun e => d.weylRootFirstField ε hε i e ^ 2) μ :=
    ((d.weylRootFirstField ε hε i).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsecond (i : Fin 4) : Integrable
      (fun e => d.weylRootField ε e * d.weylRootSecondField ε hε i e) μ :=
    ((d.weylRootField ε).continuous.mul (d.weylRootSecondField ε hε i).continuous)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [← pow_two] at hi
  rw [integral_finsetSum _ (fun i _ => hfirst i)]
  simp_rw [hi]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hsecond i)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with e
  exact (Finset.mul_sum _ _ _).symm

/-- The regularized gap energy estimate has a uniform vanishing error,
and needs no limiting statement about the singular norm gradient. -/
theorem weylRoot_energy_le (d : MetricGreenData g μ) (ε : ℝ) (hε : 0 < ε) :
    (∫ e, (∑ i, d.weylRootFirstField ε hε i e ^ 2) +
        2 * d.weylRootField ε e ^ 2 ∂μ) ≤
      2 * (∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) *
        d.weylRootField ε e ^ 2 ∂μ) + 2 * ε ^ (2 / 3 : ℝ) * μ.real univ := by
  let F := d.weylRootField ε
  let G := d.weylRootFirstField ε hε
  let H := d.weylRootSecondField ε hε
  let V : C(FrameBundle g, ℝ) := ⟨fun e => normalizedBlockNorm (plusWeyl g e.base e.frame),
    continuous_normalizedBlockNorm.comp d.continuousWeyl⟩
  have hF : Integrable (fun e => F e ^ 2) μ :=
    (F.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hV : Integrable (fun e => V e * F e ^ 2) μ :=
    (V.continuous.mul (F.continuous.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hH : Integrable (fun e => F e * ∑ i, H i e) μ :=
    (F.continuous.mul (continuous_finsetSum _ (fun i _ => (H i).continuous)))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hG : Integrable (fun e => ∑ i, G i e ^ 2) μ :=
    (continuous_finsetSum _ (fun i _ => (G i).continuous.pow 2))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbound : (∫ e, 2 * F e ^ 2 - 2 * (V e * F e ^ 2) -
      F e * (∑ i, H i e) ∂μ) ≤ ∫ _e : FrameBundle g, 2 * ε ^ (2 / 3 : ℝ) ∂μ := by
    apply integral_mono (((hF.const_mul 2).sub (hV.const_mul 2)).sub hH)
      (integrable_const (2 * ε ^ (2 / 3 : ℝ)))
    intro e
    have h := d.weylRoot_error_le ε hε e
    change 2 * F e ^ 2 - 2 * V e * F e ^ 2 - F e * (∑ i, H i e) ≤ _ at h
    change 2 * F e ^ 2 - 2 * (V e * F e ^ 2) - F e * (∑ i, H i e) ≤ _
    nlinarith only [h]
  have hsplit : (∫ e, 2 * F e ^ 2 - 2 * (V e * F e ^ 2) ∂μ) =
      2 * (∫ e, F e ^ 2 ∂μ) - 2 * (∫ e, V e * F e ^ 2 ∂μ) := by
    calc
      _ = (∫ e, 2 * F e ^ 2 ∂μ) - (∫ e, 2 * (V e * F e ^ 2) ∂μ) :=
        integral_sub (hF.const_mul 2) (hV.const_mul 2)
      _ = _ := by rw [integral_const_mul, integral_const_mul]
  have hsplit' : (∫ e, 2 * F e ^ 2 - 2 * (V e * F e ^ 2) -
      F e * (∑ i, H i e) ∂μ) =
      2 * (∫ e, F e ^ 2 ∂μ) - 2 * (∫ e, V e * F e ^ 2 ∂μ) -
        (∫ e, F e * (∑ i, H i e) ∂μ) := by
    calc
      _ = (∫ e, 2 * F e ^ 2 - 2 * (V e * F e ^ 2) ∂μ) -
          (∫ e, F e * (∑ i, H i e) ∂μ) :=
        integral_sub ((hF.const_mul 2).sub (hV.const_mul 2)) hH
      _ = _ := by rw [hsplit]
  rw [hsplit', integral_const] at hbound
  have he := d.weylRoot_energy_eq ε hε
  change (∫ e, ∑ i, G i e ^ 2 ∂μ) = -(∫ e, F e * ∑ i, H i e ∂μ) at he
  change (∫ e, (∑ i, G i e ^ 2) + 2 * F e ^ 2 ∂μ) ≤
    2 * (∫ e, V e * F e ^ 2 ∂μ) + _
  rw [integral_add hG (hF.const_mul 2), integral_const_mul]
  simp only [smul_eq_mul] at hbound
  nlinarith only [hbound, he]

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Weyl gradient satisfies the finite Bianchi constraints as
soon as the actual fixed-chart Ricci field is covariantly constant. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

/-- Both block derivatives are symmetric and trace-free, obtained directly
from the five-tensor identities rather than a moving eigenframe. -/
theorem weylGradient_constraints_of_ricci_parallel (e : OrthonormalFrame g c)
    (hRic : covariantDerivative g c (ricciTensorCoordinates g c)
      (chartAt FourSpace c c) = 0) :
    (∀ i, TraceHessian.symmetric (plusWeylGradient g c e i) ∧
      TraceHessian.traceFree (plusWeylGradient g c e i)) ∧
    (∀ i, TraceHessian.symmetric (minusWeylGradient g c e i) ∧
      TraceHessian.traceFree (minusWeylGradient g c e i)) := by
  let T := frameTensor e.matrix
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))
  have hs := frame_normalizedWeyl_derivative_symmetries g c e
  have hb := frame_normalizedWeyl_derivative_firstBianchi g c e
  have hR (a j k : Fin 4) : (∑ l, T ![a, l, j, k, l]) = 0 := by
    dsimp only [T]
    have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
    rw [covariantDerivative_normalizedWeyl g c (chartAt FourSpace c c) hz (chartMetric_posDef g c).det_pos.ne']
    exact frame_curvature_derivative_trace_zero e hRic a j k
  have ht (i : Fin 4) := AlgebraicCurvature.ricci_zero_blocks_traceFree
    (curvatureDerivativeArray T i) (hs i).1 (hs i).2.1 (hb i)
    (fun j => hR i j j)
  have hsym (i : Fin 4) (Q : Fin 3 → Mat4) :
      TraceHessian.symmetric (gradientBlock T Q i) := by
    have hh := curvatureBlock_symmetric
      (AlgebraicCurvature.curvaturePairing_symmetric
        (curvatureDerivativeArray T i) (hs i).1 (hs i).2.1 (hs i).2.2) Q
    intro a b
    exact congrArg (fun A : Mat3 => A b a) hh
  exact ⟨fun i => ⟨hsym i _, (ht i).1⟩, fun i => ⟨hsym i _, (ht i).2⟩⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normalized Einstein Weyl gradients satisfy the algebraic
and differential constraints used by the energy argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem actual_weylGradient_constraints (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    (∀ i, TraceHessian.symmetric (plusWeylGradient g c e i) ∧
      TraceHessian.traceFree (plusWeylGradient g c e i)) ∧
    (∀ i, TraceHessian.symmetric (minusWeylGradient g c e i) ∧
      TraceHessian.traceFree (minusWeylGradient g c e i)) :=
  weylGradient_constraints_of_ricci_parallel e (actual_ricci_parallel_at_center g hRic c)

theorem actual_plusWeylGradient_symmetric (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (i : Fin 4) :
    (plusWeylGradient g c e i)ᵀ = plusWeylGradient g c e i := by
  ext a b
  exact ((actual_weylGradient_constraints e hRic).1 i).1 b a

theorem actual_plusWeylGradient_trace (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (i : Fin 4) :
    (plusWeylGradient g c e i).trace = 0 :=
  ((actual_weylGradient_constraints e hRic).1 i).2

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transport the weak energy equation through the actual reflected
frame. The reflected energy is the energy of the opposite Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

def oppositeEnergyField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  d.gradientEnergyField.comp ⟨frameReflection, continuous_frameReflection g⟩

def oppositeEnergyDerivativeField (d : MetricGreenData g μ) (i : Fin 4) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => orientationSign i * d.energyDerivativeField i (frameReflection e),
    continuous_const.mul ((d.energyDerivativeField i).continuous.comp (continuous_frameReflection g))⟩

def oppositeEnergyLaplacianField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  d.energyLaplacianField.comp ⟨frameReflection, continuous_frameReflection g⟩

def totalEnergyField (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  d.gradientEnergyField + d.oppositeEnergyField

def totalEnergyDerivativeField (d : MetricGreenData g μ) (i : Fin 4) : C(FrameBundle g, ℝ) :=
  d.energyDerivativeField i + d.oppositeEnergyDerivativeField i

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Norm-only forms of the cubic and true projection estimates. These are
unchanged by reflecting the opposite block's covector coordinates. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian HighestHessian PositiveEinsteinFour.Geometry CurvatureContraction
open Energy QuarticEnergy Quadratic Potential

noncomputable section

/-- The part of one actual normalized Hessian Green integrand containing
its invariant quadratic form, distinguished cubic trace and projected cost. -/
def arrayHessianTerm (A U : Mat) (Z : Angular.Gradient) (a : Vec) : ℝ :=
  weight (normalizedBlockNorm A) (normalizedBlockNorm U) * invariantHessianForm A U Z -
    (5 / 36 : ℝ) * weightedCubicField a Z +
    generalCurvaturePairing A U
      (highestProjection (weightTensor a (gradientTensor Z)))
      (highestProjection (weightTensor a (gradientTensor Z))) /
      (24 * weight (normalizedBlockNorm A) (normalizedBlockNorm U))

def arrayCoupledIntegrand (A U : Mat) (Z V : Angular.Gradient) (a ab p q : Vec) : ℝ :=
  arrayHessianTerm A U Z a + arrayHessianTerm U A V ab +
    scalarCouplingTerm (normalizedBlockNorm A) (normalizedBlockNorm U)
      (weylGradientEnergy Z) (weylGradientEnergy V)
      (weylMatrixEnergy A Z) (weylMatrixEnergy U V)
      (scalarNormExpression 0 A Z) (scalarNormExpression 0 U V)
      (traceEnergy A) (traceEnergy U) p q

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! Symmetrize an oriented frame measure only for the reflection-invariant
Green integral. Scalar variance and Weyl gaps still use the original
oriented measure. Reflection invariance of that original measure is not
assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem MetricGreenData.flow_preserves_reflected (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d) (i : Fin 4) (t : ℝ) :
    MeasurePreserving ((d.flow i).map t) (μ.map frameReflection) (μ.map frameReflection) := by
  have hF : MeasurePreserving (frameReflection : FrameBundle g → FrameBundle g)
      μ (μ.map frameReflection) := (frameReflectionEquiv g).measurable.measurePreserving μ
  apply hF.of_semiconj ((d.flow i).preserves (orientationSign i * t))
  · intro e
    have ht : orientationSign i * (orientationSign i * t) = t := by
      rw [← mul_assoc, ← pow_two, orientationSign_sq, one_mul]
    simpa only [ht] using hparallel i (orientationSign i * t) e
  · exact ((d.flow i).map t).measurable

def MetricGreenData.symmetricFlow (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d) (i : Fin 4) :
    FrameFlow g (symmetricFrameMeasure g μ) where
  map := (d.flow i).map
  continuous := (d.flow i).continuous
  preserves t := ((d.flow i).preserves t).add_measure (d.flow_preserves_reflected hparallel i t)

def MetricGreenData.onSymmetricMeasure (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d) : MetricGreenData g (symmetricFrameMeasure g μ) where
  flow := d.symmetricFlow hparallel
  weyl := d.weyl
  continuousWeyl := d.continuousWeyl
  continuousGradient := d.continuousGradient
  continuousHessian := d.continuousHessian
  continuousThird := d.continuousThird
  derivativeWeyl := d.derivativeWeyl
  derivativeGradient := d.derivativeGradient
  derivativeHessian := d.derivativeHessian
  gradientBianchi := d.gradientBianchi
  innerCommutator := d.innerCommutator
  outerCommutator := d.outerCommutator
  ricci := d.ricci

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite square-root energy inequality on the original measure.
Only parallel-flow compatibility with reflection is used: the plus equation
is applied to the reflected measure and then pulled back. The original
oriented measure is never required to be reflection invariant. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem integral_reflectedMeasure (f : FrameBundle g → ℝ) :
    (∫ e, f e ∂μ.map frameReflection) = ∫ e, f (frameReflection e) ∂μ :=
  (frameReflectionEquiv g).measurableEmbedding.integral_map f

namespace MetricGreenData

def reflectedFlow (d : MetricGreenData g μ) (hparallel : ParallelReflection d) (i : Fin 4) :
    FrameFlow g (μ.map frameReflection) where
  map := (d.flow i).map
  continuous := (d.flow i).continuous
  preserves t := d.flow_preserves_reflected hparallel i t

def onReflectedMeasure (d : MetricGreenData g μ) (hparallel : ParallelReflection d) :
    MetricGreenData g (μ.map frameReflection) where
  flow := d.reflectedFlow hparallel
  weyl := d.weyl
  continuousWeyl := d.continuousWeyl
  continuousGradient := d.continuousGradient
  continuousHessian := d.continuousHessian
  continuousThird := d.continuousThird
  derivativeWeyl := d.derivativeWeyl
  derivativeGradient := d.derivativeGradient
  derivativeHessian := d.derivativeHessian
  gradientBianchi := d.gradientBianchi
  innerCommutator := d.innerCommutator
  outerCommutator := d.outerCommutator
  ricci := d.ricci

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! A pointwise spectral witness retains exactly the data used by the
coupled estimate. The witness is constructed from the actual matrices
and Bianchi gradient; it never requires a measurable spectral frame. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry
open Energy QuarticEnergy Quadratic Potential

noncomputable section

structure PointwiseSpectrum (A U : Mat) (Z : Angular.Gradient) (p : Vec) where
  frame : Mat
  orthogonal : frameᵀ * frame = 1
  shape : Shape
  diagonal : conjugateMatrix frame A =
    Matrix.diagonal (fun i => normalizedBlockNorm A * shape.s i)
  minimum : ℝ
  minimum_lower : 1 ≤ minimum
  minimum_upper : minimum ≤ 2
  cubic : shape.sigma = (3 * minimum - minimum ^ 3) / 2
  spectrum_lower : ∀ i, -minimum ≤ shape.s i
  spectrum_minimum : ∃ i, shape.s i = -minimum
  radial : Vec
  second : Vec
  third : Vec
  energy : (parameters shape radial second third).squaredNorm / 6 = weylGradientEnergy Z
  radial_norm : ‖radial‖ ^ 2 = ‖p‖ ^ 2
  original_radial_norm : ‖blockRadialGradient A Z‖ ^ 2 = ‖p‖ ^ 2
  matrix_energy : weylMatrixEnergy A Z =
    curvatureContraction shape (normalizedBlockNorm A) (parameters shape radial second third)
  hessian : invariantHessianForm A U Z ≤
    hessianTensorForm shape (normalizedBlockNorm A) (normalizedBlockNorm U) radial second third

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The exact cancellation of the two weak norm equations with the
deficit-weighted energy equation. All fields are the actual Weyl fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

def deficitField (d : MetricGreenData g μ) (o : OppositeWeylData d) : C(FrameBundle g, ℝ) :=
  ⟨fun e => regularizedDeficit 0 (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame),
    (continuous_const.sub ((continuous_regularizedBlockNorm 0).comp d.continuousWeyl)).sub
      ((continuous_regularizedBlockNorm 0).comp o.continuousWeyl)⟩

def jointScalarNorm (_d : MetricGreenData g μ) (e : FrameBundle g) : ℝ :=
  scalarNormExpression 0 (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame) +
  scalarNormExpression 0 (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)

def jointEnergyLaplacian (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  d.energyLaplacianField + d.oppositeEnergyLaplacianField

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal curvature and its covariant derivative depend on the first
frame direction through their Frobenius norms, not on the normal basis. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.curvatureInvariantFrobenius
theorem frameCurvatureField_normalRestriction (e : OrthonormalFrame g c) :
    frameCurvatureField g ⟨c, e⟩ = normalRestriction e.matrix
      (directionalCurvatureMatrix (curvatureCoordinates g c (chartAt FourSpace c c))
        (fun a => e.matrix a 0)) - 1 := by
  ext i j
  rw [frameCurvatureField_apply]
  change frameCurvature g c e i.succ 0 0 j.succ - (if i = j then 1 else 0) = _
  rw [← frameTensor_curvatureCoordinates, frameTensor_normal_matrix]
  rfl

theorem frameCurvatureField_norm_same_direction (e f : OrthonormalFrame g c)
    (hfirst : e.vector 0 = f.vector 0) :
    ‖frameCurvatureField g ⟨c, e⟩‖ ^ 2 = ‖frameCurvatureField g ⟨c, f⟩‖ ^ 2 := by
  have hw : (fun a => e.matrix a 0) = (fun a => f.matrix a 0) := by
    funext a
    exact congrArg (fun v : FourSpace => v a) hfirst
  rw [frameCurvatureField_normalRestriction, frameCurvatureField_normalRestriction, ← hw]
  exact normalRestriction_sub_one_norm_sq_same_direction e f hfirst _

/-- Each actual first derivative of the normalized Weyl tensor has only its
positive and negative Weyl blocks; its Ricci contraction is zero. -/
theorem actual_weyl_derivative_decomposition (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (d : Fin 4) :
    curvatureDerivativeArray (frameTensor e.matrix
      (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))) d =
      blockTensor (plusWeylGradient g c e d) quaternionMatrix +
        blockTensor (minusWeylGradient g c e d) oppositeMatrix := by
  let T := frameTensor e.matrix
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))
  have hs := frame_normalizedWeyl_derivative_symmetries g c e d
  have hR (j k : Fin 4) : (∑ l, T ![d, l, j, k, l]) = 0 := by
    dsimp only [T]
    have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
    rw [covariantDerivative_normalizedWeyl g c (chartAt FourSpace c c) hz
      (chartMetric_posDef g c).det_pos.ne']
    exact frame_curvature_derivative_trace_zero e
      (actual_ricci_parallel_at_center g hRic c) d j k
  exact AlgebraicCurvature.ricci_zero_decomposition _ hs.1 hs.2.1 hs.2.2 hR

theorem normalEvaluation_pureBlocks (A B : Mat3) (q : Directions) (i j : Fin 3) :
    normalEvaluation q i j (blockTensor A quaternionMatrix + blockTensor B oppositeMatrix) =
      normalDeviation A B q i j := by
  have hh := normalEvaluation_einstein A B q i j
  have hzero := normalEvaluation_einstein (0 : Mat3) (0 : Mat3) q i j
  rw [einsteinCurvatureTensor, blockTensor_add, blockTensor_add,
    map_add, map_add, map_add] at hh
  simp only [einsteinCurvatureTensor, add_zero, map_add] at hzero
  have hz : normalDeviation (0 : Mat3) (0 : Mat3) q = 0 := by
    simp [normalDeviation, rotated]
  rw [hz, add_zero] at hzero
  simp only [Matrix.add_apply] at hh
  rw [map_add]
  linarith only [hh, hzero]

theorem frameCurvatureDerivative_actual (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (i j : Fin 3) :
    frameCurvatureDerivative g ⟨c, e⟩ i j = frameTensor e.matrix
      (covariantDerivative g c (normalizedWeylCoordinates g c)
        (chartAt FourSpace c c)) ![0, i.succ, 0, 0, j.succ] := by
  have hd := congrArg (fun R : CurvatureArray => normalEvaluation firstDirection i j R)
    (actual_weyl_derivative_decomposition e hRic 0)
  rw [frameCurvatureDerivative_eq]
  rw [← normalEvaluation_pureBlocks]
  rw [← hd]
  simp only [normalEvaluation, firstDirection_normal, firstDirection_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rfl

theorem frameCurvatureDerivative_normalRestriction (e : OrthonormalFrame g c)
    (hRic : RicciThree g) :
    frameCurvatureDerivative g ⟨c, e⟩ = normalRestriction e.matrix
      (directionalCurvatureMatrix
        (directionalDerivativeTensor
          (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))
          (fun a => e.matrix a 0)) (fun a => e.matrix a 0)) := by
  ext i j
  rw [frameCurvatureDerivative_actual e hRic]
  let E : Mat4 := e.matrix
  let T : CovariantCoordinates 5 :=
    covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c)
  change frameTensor E T (Fin.cons (0 : Fin 4) (![i.succ, 0, 0, j.succ] : Fin 4 → Fin 4)) =
    normalRestriction E (directionalCurvatureMatrix
      (directionalDerivativeTensor T (fun a : Fin 4 => E a 0))
      (fun a : Fin 4 => E a 0)) i j
  rw [frameTensor_directionalDerivative, frameTensor_normal_matrix]
  rfl

theorem frameCurvatureDerivative_norm_same_direction (e f : OrthonormalFrame g c)
    (hRic : RicciThree g) (hfirst : e.vector 0 = f.vector 0) :
    ‖frameCurvatureDerivative g ⟨c, e⟩‖ ^ 2 =
      ‖frameCurvatureDerivative g ⟨c, f⟩‖ ^ 2 := by
  have hw : (fun a => e.matrix a 0) = (fun a => f.matrix a 0) := by
    funext a
    exact congrArg (fun v : FourSpace => v a) hfirst
  rw [frameCurvatureDerivative_normalRestriction e hRic,
    frameCurvatureDerivative_normalRestriction f hRic, ← hw]
  exact normalRestriction_norm_sq_same_direction e f hfirst _

theorem frameCurvatureField_directionInvariant (g : SmoothMetric M) :
    DirectionInvariant (fun e => ‖frameCurvatureField g e‖ ^ 2) := by
  rintro ⟨c, e⟩ ⟨d, f⟩ hbase hfirst
  dsimp only at hbase
  subst d
  exact frameCurvatureField_norm_same_direction e f hfirst

theorem frameCurvatureDerivative_directionInvariant (g : SmoothMetric M)
    (hRic : RicciThree g) :
    DirectionInvariant (fun e => ‖frameCurvatureDerivative g e‖ ^ 2) := by
  rintro ⟨c, e⟩ ⟨d, f⟩ hbase hfirst
  dsimp only at hbase
  subst d
  exact frameCurvatureDerivative_norm_same_direction e f hRic hfirst

end
end PositiveEinsteinFour.Geometry
end


section

/-! Equation (16), before its positive constant factor: the integrated
trace-subtracted energy is nonnegative. The proof combines the actual
weak equations and the full prescribed trace subtraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

def jointMatrixEnergy (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  d.matrixEnergyField + d.matrixEnergyField.comp ⟨frameReflection, continuous_frameReflection g⟩

def jointTraceEnergy (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => traceEnergy (plusWeyl g e.base e.frame) +
    traceEnergy (plusWeyl g (frameReflection e).base (frameReflection e).frame),
    (continuous_traceEnergy.comp d.continuousWeyl).add
      ((continuous_traceEnergy.comp d.continuousWeyl).comp (continuous_frameReflection g))⟩

def jointHessianEnergy (d : MetricGreenData g μ) : C(FrameBundle g, ℝ) :=
  ⟨fun e => d.jointEnergyLaplacian e - 26 * d.totalEnergyField e + 40 * d.jointMatrixEnergy e,
    (d.jointEnergyLaplacian.continuous.sub
      (continuous_const.mul d.totalEnergyField.continuous)).add
        (continuous_const.mul d.jointMatrixEnergy.continuous)⟩

def traceDeficitIntegrand (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (e : FrameBundle g) : ℝ :=
  -(d.totalEnergyField e * d.jointScalarNorm e) -
    26 * d.deficitField o e * d.totalEnergyField e +
    40 * d.deficitField o e * d.jointMatrixEnergy e - d.deficitField o e * d.jointTraceEnergy e

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Rotation of the actual first curvature derivative, including its
covector direction, before either Weyl block is contracted. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem turn_normalEvaluation_pureBlocks (A B : Mat3) (q : Directions) (i j : Fin 3) :
    normalEvaluation q i j (blockTensor A quaternionMatrix + blockTensor B oppositeMatrix) =
      normalDeviation A B q i j := by
  have hh := normalEvaluation_einstein A B q i j
  have hzero := normalEvaluation_einstein (0 : Mat3) (0 : Mat3) q i j
  rw [einsteinCurvatureTensor, turn_blockTensor_add, turn_blockTensor_add,
    map_add, map_add, map_add] at hh
  simp only [einsteinCurvatureTensor, add_zero, map_add] at hzero
  have hz : normalDeviation (0 : Mat3) (0 : Mat3) q = 0 := by
    simp [normalDeviation, rotated]
  rw [hz, add_zero] at hzero
  simp only [Matrix.add_apply] at hh
  rw [map_add]
  linarith only [hh, hzero]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

/-- The quaternionic completion rotates the derivative direction and all
four curvature slots of the actual tensor at once. -/
theorem frameCurvatureDerivative_turn (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (q : Directions) :
    frameCurvatureDerivative g (frameTurn e q) = normalCurvatureDerivative g c e q := by
  let T : CovariantCoordinates 5 := covariantDerivative g c
    (normalizedWeylCoordinates g c) (chartAt FourSpace c c)
  let Z : Gradient := plusWeylGradient g c e
  let W : Gradient := minusWeylGradient g c e
  have hd (d : Fin 4) : curvatureDerivativeArray (frameTensor e.matrix T) d =
      blockTensor (Z d) quaternionMatrix + blockTensor (W d) oppositeMatrix :=
    actual_weyl_derivative_decomposition e hRic d
  ext i j
  change frameCurvatureDerivative g (⟨c, e.turn q⟩ : FrameBundle g) i j =
    normalCurvatureDerivative g c e q i j
  rw [frameCurvatureDerivative_actual (e.turn q) hRic]
  change frameTensor (e.matrix * directionFrameMatrix q) T
    ![0, i.succ, 0, 0, j.succ] = _
  rw [frameTensor_mul, frameTensor_directionFrame_normal]
  change (∑ d, q.val d * normalEvaluation q i j
    (curvatureDerivativeArray (frameTensor e.matrix T) d)) =
      normalDeviation (directional Z q) (directional W q) q i j
  calc
    _ = ∑ d, q.val d * normalDeviation (Z d) (W d) q i j := by
      apply Finset.sum_congr rfl
      intro d _
      rw [hd, turn_normalEvaluation_pureBlocks]
    _ = _ := by
      rw [directional, directional, normalDeviation_sum_smul]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sum of the two Hessian inequalities, the trace-deficit inequality,
and both polynomial norm tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

def preVarianceIntegrand (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (e : FrameBundle g) : ℝ :=
  regularizedHessianIntegrand g 0 e + regularizedHessianIntegrand g 0 (frameReflection e) +
    (17 / 10 : ℝ) * d.traceDeficitIntegrand o e +
    kappaNormIntegrand (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
      (plusWeylGradient g e.base e.frame) (minusWeylGradient g e.base e.frame) +
    kappaNormIntegrand (minusWeyl g e.base e.frame) (plusWeyl g e.base e.frame)
      (minusWeylGradient g e.base e.frame) (plusWeylGradient g e.base e.frame)

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two total Weyl energies are base scalars, proved from the actual
orthonormal-frame tensor norm and the quaternionic normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frame_curvature_norm_energy (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    frameTensorSquareNorm (frameTensor e.matrix
      (curvatureCoordinates g c (chartAt FourSpace c c))) =
      24 + 24 * (normalizedBlockNorm (plusWeyl g c e) ^ 2 +
        normalizedBlockNorm (minusWeyl g c e) ^ 2) := by
  let R := frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c))
  have hR : R = blockTensorCoordinates (1 + plusWeyl g c e) quaternionMatrix +
      blockTensorCoordinates (1 + minusWeyl g c e) oppositeMatrix := by
    funext a
    have ha : a = ![a 0, a 1, a 2, a 3] := by
      funext i
      fin_cases i <;> rfl
    dsimp only [R]
    rw [ha, frameTensor_curvatureCoordinates, actual_einstein_decomposition e hRic]
    rfl
  have hA : blockCoordinates R quaternionMatrix = 1 + plusWeyl g c e := by
    dsimp only [R]
    rw [curvature_blockCoordinates]
    unfold plusWeyl
    abel
  have hB : blockCoordinates R oppositeMatrix = 1 + minusWeyl g c e := by
    dsimp only [R]
    rw [curvature_blockCoordinates]
    unfold minusWeyl
    abel
  have h := frameTensorSquareNorm_of_blocks R _ _ hR hA hB
  have ht := actual_weyl_traceFree e hRic
  rw [squareNorm_one_add (plusWeyl g c e) ht.1,
    squareNorm_one_add (minusWeyl g c e) ht.2] at h
  have hpa := normalizedBlockNorm_sq (plusWeyl g c e)
  have hpb := normalizedBlockNorm_sq (minusWeyl g c e)
  change normalizedBlockNorm (plusWeyl g c e) ^ 2 = squareNorm (plusWeyl g c e) / 6 at hpa
  change normalizedBlockNorm (minusWeyl g c e) ^ 2 = squareNorm (minusWeyl g c e) / 6 at hpb
  change frameTensorSquareNorm R = _
  linarith only [h, hpa, hpb]

theorem frame_weyl_norm_sum_same_base (e f : OrthonormalFrame g c) (hRic : RicciThree g) :
    normalizedBlockNorm (plusWeyl g c e) ^ 2 + normalizedBlockNorm (minusWeyl g c e) ^ 2 =
      normalizedBlockNorm (plusWeyl g c f) ^ 2 + normalizedBlockNorm (minusWeyl g c f) ^ 2 := by
  have he := frame_curvature_norm_energy e hRic
  have hf := frame_curvature_norm_energy f hRic
  have hnorm := frameTensor_norm_same_base e f
    (curvatureCoordinates g c (chartAt FourSpace c c))
  linarith only [he, hf, hnorm]

theorem frame_weyl_gradient_norm_energy (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    frameTensorSquareNorm (frameTensor e.matrix
      (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))) =
      4 * (gradientSquareNorm (plusWeylGradient g c e) +
        gradientSquareNorm (minusWeylGradient g c e)) := by
  let T := frameTensor e.matrix
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))
  have hs (d : Fin 4) : frameTensorSquareNorm (fun a => T (Fin.cons d a)) =
      4 * (squareNorm (plusWeylGradient g c e d) + squareNorm (minusWeylGradient g c e d)) := by
    apply frameTensorSquareNorm_of_blocks
    · funext a
      have ha : a = ![a 0, a 1, a 2, a 3] := by
        funext i
        fin_cases i <;> rfl
      rw [ha]
      exact congrFun (congrFun (congrFun (congrFun
        (actual_weyl_derivative_decomposition e hRic d) (a 0)) (a 1)) (a 2)) (a 3)
    · rfl
    · rfl
  change (∑ a, T a * T a) = _
  rw [sum_tensor_indices_cons]
  change (∑ d, frameTensorSquareNorm (fun a => T (Fin.cons d a))) = _
  simp only [hs, Finset.sum_add_distrib, ← Finset.mul_sum, gradientSquareNorm]

theorem frame_weyl_gradient_sum_same_base (e f : OrthonormalFrame g c)
    (hRic : RicciThree g) :
    gradientSquareNorm (plusWeylGradient g c e) + gradientSquareNorm (minusWeylGradient g c e) =
      gradientSquareNorm (plusWeylGradient g c f) + gradientSquareNorm (minusWeylGradient g c f) := by
  have he := frame_weyl_gradient_norm_energy e hRic
  have hf := frame_weyl_gradient_norm_energy f hRic
  have hnorm := frameTensor_norm_same_base e f
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))
  linarith only [he, hf, hnorm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full finite-array integrand is the actual metric integral from
both Green identities, trace subtraction, variance, and polynomial tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

namespace MetricGreenData

def coupledIntegrand (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (e : FrameBundle g) : ℝ :=
  d.preVarianceIntegrand o e + 158 * varianceDensity
    (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)
    (blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame))
    (blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame))

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Apply the finite-array estimate to the actual two Weyl blocks.
The zero faces are supplied by the almost-everywhere derivative theorem. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi QuaternionFrame MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def plusRadialEnergy (e : FrameBundle g) : ℝ :=
  ‖blockRadialGradient (plusWeyl g e.base e.frame) (plusWeylGradient g e.base e.frame)‖ ^ 2

def minusRadialEnergy (e : FrameBundle g) : ℝ :=
  ‖blockRadialGradient (minusWeyl g e.base e.frame) (minusWeylGradient g e.base e.frame)‖ ^ 2

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite curvature contractions occurring in the four-dimensional
Euler and first Pontryagin densities.  These are pointwise identities for
the actual metric curvature; no characteristic-number or Hodge theorem is
assumed or asserted. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem hodgeFirstTensor_twoFormProduct (P Q : Mat4) :
    hodgeFirstTensor (twoFormProductCoordinates P Q) =
      twoFormProductCoordinates (hodgeStarFour P) Q := by
  funext a
  change hodgeStarFour (fun i j => P i j * Q (a 3) (a 2)) (a 0) (a 1) =
    hodgeStarFour P (a 0) (a 1) * Q (a 3) (a 2)
  have hp : (fun i j => P i j * Q (a 3) (a 2)) = Q (a 3) (a 2) • P := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, mul_comm]
  rw [hp, map_smul]
  simp only [Matrix.smul_apply, smul_eq_mul, mul_comm]

theorem hodgeFirstTensor_block (A : Mat3) (Q : Fin 3 → Mat4) (r : ℝ)
    (hQ : ∀ s, hodgeStarFour (Q s) = r • Q s) :
    hodgeFirstTensor (blockTensorCoordinates A Q) = r • blockTensorCoordinates A Q := by
  simp only [blockTensorCoordinates_sum, map_sum, map_smul, hodgeFirstTensor_twoFormProduct, hQ,
    twoFormProductCoordinates_smul_left]
  simp only [smul_comm _ r, ← Finset.smul_sum]

theorem hodgeFirstTensor_plus (A : Mat3) :
    hodgeFirstTensor (blockTensorCoordinates A quaternionMatrix) =
      blockTensorCoordinates A quaternionMatrix := by
  simpa only [one_smul] using hodgeFirstTensor_block A quaternionMatrix 1
    (fun s => by simpa only [one_smul] using hodgeStarFour_quaternion s)

theorem hodgeFirstTensor_minus (A : Mat3) :
    hodgeFirstTensor (blockTensorCoordinates A oppositeMatrix) =
      -blockTensorCoordinates A oppositeMatrix := by
  simpa only [neg_one_smul] using hodgeFirstTensor_block A oppositeMatrix (-1)
    (fun s => by simpa only [neg_one_smul] using hodgeStarFour_opposite s)

/-- The signed curvature norm is the difference of the two block norms. -/
theorem frameTensorPairing_hodgeFirst_of_blocks (R : CovariantCoordinates 4)
    (A B : Mat3)
    (hR : R = blockTensorCoordinates A quaternionMatrix +
      blockTensorCoordinates B oppositeMatrix)
    (hA : blockCoordinates R quaternionMatrix = A)
    (hB : blockCoordinates R oppositeMatrix = B) :
    frameTensorPairing R (hodgeFirstTensor R) = 4 * (squareNorm A - squareNorm B) := by
  have hstar : hodgeFirstTensor R = blockTensorCoordinates A quaternionMatrix -
      blockTensorCoordinates B oppositeMatrix := by
    rw [hR, map_add, hodgeFirstTensor_plus, hodgeFirstTensor_minus, sub_eq_add_neg]
  rw [hstar, sub_eq_add_neg, frameTensorPairing_add_right]
  have hneg : frameTensorPairing R (-blockTensorCoordinates B oppositeMatrix) =
      -frameTensorPairing R (blockTensorCoordinates B oppositeMatrix) := by
    simp only [frameTensorPairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  rw [hneg, frameTensorPairing_blockTensor, frameTensorPairing_blockTensor, hA, hB]
  simp only [matrixPairing, squareNorm, pow_two]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frame_curvature_hodge_pairing (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    frameTensorPairing
      (frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c)))
      (hodgeFirstTensor
        (frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c)))) =
      24 * (normalizedBlockNorm (plusWeyl g c e) ^ 2 -
        normalizedBlockNorm (minusWeyl g c e) ^ 2) := by
  let R := frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c))
  have hR : R = blockTensorCoordinates (1 + plusWeyl g c e) quaternionMatrix +
      blockTensorCoordinates (1 + minusWeyl g c e) oppositeMatrix := by
    funext a
    have ha : a = ![a 0, a 1, a 2, a 3] := by
      funext i
      fin_cases i <;> rfl
    dsimp only [R]
    rw [ha, frameTensor_curvatureCoordinates, actual_einstein_decomposition e hRic]
    rfl
  have hblock (Q : Fin 3 → Mat4) :
      blockCoordinates R Q = curvatureBlock (curvaturePairing g c e) Q := by
    dsimp only [R]
    ext s t
    simp only [blockCoordinates, curvatureBlock]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [frameTensor_curvatureCoordinates]
    rfl
  have hA : blockCoordinates R quaternionMatrix = 1 + plusWeyl g c e := by
    rw [hblock]
    unfold plusWeyl
    abel
  have hB : blockCoordinates R oppositeMatrix = 1 + minusWeyl g c e := by
    rw [hblock]
    unfold minusWeyl
    abel
  have h := frameTensorPairing_hodgeFirst_of_blocks R _ _ hR hA hB
  have ht := actual_weyl_traceFree e hRic
  rw [squareNorm_one_add_trace (plusWeyl g c e) ht.1,
    squareNorm_one_add_trace (minusWeyl g c e) ht.2] at h
  have hpa := normalizedBlockNorm_sq (plusWeyl g c e)
  have hpb := normalizedBlockNorm_sq (minusWeyl g c e)
  change normalizedBlockNorm (plusWeyl g c e) ^ 2 = squareNorm _ / 6 at hpa
  change normalizedBlockNorm (minusWeyl g c e) ^ 2 = squareNorm _ / 6 at hpb
  change frameTensorPairing R (hodgeFirstTensor R) = _
  linarith only [h, hpa, hpb]

theorem frame_curvature_eulerDensity (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    curvatureEulerDensity
      (frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c))) =
      (3 / (4 * Real.pi ^ 2)) * (1 + normalizedBlockNorm (plusWeyl g c e) ^ 2 +
        normalizedBlockNorm (minusWeyl g c e) ^ 2) := by
  have hr (j k : Fin 4) :
      (∑ i : Fin 4, (frameTensor e.matrix
        (curvatureCoordinates g c (chartAt FourSpace c c))) ![i, j, k, i]) =
        if j = k then 3 else 0 := by
    simp only [frameTensor_curvatureCoordinates]
    exact frame_algebraic_ricciThree e hRic j k
  rw [curvatureEulerDensity, frame_curvature_norm_energy e hRic]
  simp only [hr, Fin.sum_univ_four]
  norm_num
  ring

theorem frame_curvature_pontryaginDensity (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    curvaturePontryaginDensity
      (frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c))) =
      (3 / (2 * Real.pi ^ 2)) * (normalizedBlockNorm (plusWeyl g c e) ^ 2 -
        normalizedBlockNorm (minusWeyl g c e) ^ 2) := by
  rw [curvaturePontryaginDensity, frame_curvature_hodge_pairing e hRic]
  ring

theorem frame_curvature_signatureDensity (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    curvatureSignatureDensity
      (frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c))) =
      (1 / (2 * Real.pi ^ 2)) * (normalizedBlockNorm (plusWeyl g c e) ^ 2 -
        normalizedBlockNorm (minusWeyl g c e) ^ 2) := by
  rw [curvatureSignatureDensity, frame_curvature_pontryaginDensity e hRic]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Orthogonal coefficient matrices of orientation-preserving four-frame changes. -/

namespace PositiveEinsteinFour.QuaternionFrame

open Matrix TraceHessian PositiveEinsteinFour.Geometry
open Angular (oppositeMatrix)
open scoped BigOperators

noncomputable section

theorem positiveOrientationMatrix_span (P : Mat4) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) (s : Fin 3) :
    P * quaternionMatrix s * Pᵀ =
      imaginaryCombination quaternionMatrix (fun r => positiveOrientationMatrix P r s) :=
  oriented_quaternion_span P hP hdet s

theorem negativeOrientationMatrix_span (P : Mat4) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) (s : Fin 3) :
    P * oppositeMatrix s * Pᵀ =
      imaginaryCombination oppositeMatrix (fun r => negativeOrientationMatrix P r s) :=
  oriented_opposite_span P hP hdet s

theorem positiveOrientationMatrix_orthogonal (P : Mat4) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) :
    (positiveOrientationMatrix P)ᵀ * positiveOrientationMatrix P = 1 := by
  apply coefficientMatrix_orthogonal P quaternionMatrix _ hP
  · exact CurvatureContraction.plus_twoForm_pairing
  · exact positiveOrientationMatrix_span P hP hdet

theorem negativeOrientationMatrix_orthogonal (P : Mat4) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) :
    (negativeOrientationMatrix P)ᵀ * negativeOrientationMatrix P = 1 := by
  apply coefficientMatrix_orthogonal P oppositeMatrix _ hP
  · exact CurvatureContraction.opposite_twoForm_pairing
  · exact negativeOrientationMatrix_span P hP hdet

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The individual Weyl norms descend to each oriented frame component. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian Angular QuaternionFrame
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem plusWeyl_norm_same_oriented_frame (e f : OrthonormalFrame g c)
    (hor : 0 < e.matrix.det * f.matrix.det) :
    normalizedBlockNorm (plusWeyl g c e) = normalizedBlockNorm (plusWeyl g c f) := by
  exact blockNorm_same_oriented_frame e f quaternionMatrix
    (positiveOrientationMatrix (e.changeMatrix f))
    (positiveOrientationMatrix_orthogonal _ (e.changeMatrix_orthogonal f)
      (e.changeMatrix_det_one f hor))
    (positiveOrientationMatrix_span _ (e.changeMatrix_orthogonal f)
      (e.changeMatrix_det_one f hor))

theorem minusWeyl_norm_same_oriented_frame (e f : OrthonormalFrame g c)
    (hor : 0 < e.matrix.det * f.matrix.det) :
    normalizedBlockNorm (minusWeyl g c e) = normalizedBlockNorm (minusWeyl g c f) := by
  exact blockNorm_same_oriented_frame e f oppositeMatrix
    (negativeOrientationMatrix (e.changeMatrix f))
    (negativeOrientationMatrix_orthogonal _ (e.changeMatrix_orthogonal f)
      (e.changeMatrix_det_one f hor))
    (negativeOrientationMatrix_span _ (e.changeMatrix_orthogonal f)
      (e.changeMatrix_det_one f hor))


theorem actual_plusNorm_frame (o : FrameOrientation g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    plusNorm o e.base = normalizedBlockNorm (plusWeyl g e.base e.frame) := by
  exact plusWeyl_norm_same_oriented_frame (o.frame e.base) e.frame
    ((o.positive_iff_det e.base e.frame).mp he)

theorem actual_minusNorm_frame (o : FrameOrientation g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    minusNorm o e.base = normalizedBlockNorm (minusWeyl g e.base e.frame) := by
  exact minusWeyl_norm_same_oriented_frame (o.frame e.base) e.frame
    ((o.positive_iff_det e.base e.frame).mp he)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Weyl-norm difference variance follows by passing the smooth scalar
theorem to the limit using parallel-frame calculus. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ}

/-- Only the precise classical inputs of the smooth scalar argument. -/
structure ScalarVarianceInputs (d : MetricGreenData g μ) (orientation : FrameOrientation g) : Prop where
  norms : PetersenOrientedNormInput orientation
  orientationFlow : OrientationPreservingFlow d orientation
  supported : ∀ᵐ e ∂μ, e ∈ orientation.positive
  calculus : PetersenScalarCalculusInput d
  poisson : PetersenPoissonInput g μ
  positive : ShiftedCurvaturePositive g
  decomposition : ∀ e : FrameBundle g, frameCurvature g e.base e.frame =
    Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameEnergy
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrate the two actual Weyl derivative energies before applying the
radial comparison. The differential inputs are precisely the integrated
Weyl equations of Gursky--LeBrun (1999), equation (12), p.8, in Ric=3g
normalization. The spherical disintegration and its generic frame-change
premises contain no derivative-energy estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

def plusGradientEnergy {g : SmoothMetric M} (o : FrameOrientation g) (c : M) : ℝ :=
  gradientSquareNorm (plusWeylGradient g c (o.frame c))

def minusGradientEnergy {g : SmoothMetric M} (o : FrameOrientation g) (c : M) : ℝ :=
  gradientSquareNorm (minusWeylGradient g c (o.frame c))

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameRegularity
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundedness on the compact frame space supplies the weighted Lipschitz
condition required by the proved discrete-to-continuous radial comparison. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat3_3
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instNormedSpaceRealMat3_1
theorem frameWeighted_lipschitz {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] (φ : FrameFlow g μ)
    (hC : Continuous (frameCurvatureField g))
    (hH : Continuous (frameCurvatureDerivative g))
    (hpoint : ∀ t e, HasDerivAt
      (fun r => frameCurvatureField g (φ.map r e))
      (frameCurvatureDerivative g (φ.map t e)) t)
    (t : ℝ) (e : FrameBundle g) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a b,
      ‖Averages.sineWeight a • frameCurvatureField g (φ.map (t * a) e) -
        Averages.sineWeight b • frameCurvatureField g (φ.map (t * b) e)‖ ≤
          L * |a - b| := by
  let : NormedAddCommGroup C(FrameBundle g, Mat3) := ContinuousMap.instNormedAddCommGroup
  let : NormedSpace ℝ C(FrameBundle g, Mat3) := ContinuousMap.normedSpace
  let C : C(FrameBundle g, Mat3) := ⟨_, hC⟩
  let H : C(FrameBundle g, Mat3) := ⟨_, hH⟩
  refine ⟨2 * Real.pi * ‖C‖ + 2 * ‖H‖ * |t|, by positivity, ?_⟩
  intro a b
  exact Averages.sineWeighted_rescale_lipschitz
    (fun r => hpoint r e)
    (fun r => C.norm_coe_le_norm (φ.map r e))
    (fun r => H.norm_coe_le_norm (φ.map r e)) t a b

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The norm regularity input is fully derived from the actual local frames
and the four-dimensional quaternion action. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem OrientedNormRegularity.toPetersenInput {o : FrameOrientation g}
    (h : OrientedNormRegularity o) : PetersenOrientedNormInput o where
  plusSquareSmooth := h.plusSquareSmooth
  minusSquareSmooth := h.minusSquareSmooth
  plusFrame := actual_plusNorm_frame o
  minusFrame := actual_minusNorm_frame o

end
end PositiveEinsteinFour.Geometry
end


section

/-! A two-form written in the chosen oriented frame, with its values in
every other frame recovered by actual tensor pullback. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem twoFormFrameValue_at_orientation (o : FrameOrientation g) (u : M → TwoFormFour)
    (c : M) : twoFormFrameValue o u ⟨c, o.frame c⟩ = u c := by
  simp only [twoFormFrameValue, OrthonormalFrame.changeMatrix_self, twoFormFrameAction_one]

theorem twoFormFrameValue_change (o : FrameOrientation g) (u : M → TwoFormFour)
    {c : M} (e f : OrthonormalFrame g c) :
    twoFormFrameValue o u ⟨c, f⟩ =
      twoFormFrameAction (e.changeMatrix f) (twoFormFrameValue o u ⟨c, e⟩) := by
  simp only [twoFormFrameValue, twoFormFrameAction_comp, OrthonormalFrame.changeMatrix_comp]

theorem twoFormFrameValue_hodge (o : FrameOrientation g) (u : M → TwoFormFour)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    twoFormFrameValue o (fun c => twoFormHodge (u c)) e =
      twoFormHodge (twoFormFrameValue o u e) :=
  twoFormFrameAction_hodge _ ((o.frame e.base).changeMatrix_orthogonal e.frame)
    ((o.frame e.base).changeMatrix_det_one e.frame ((o.positive_iff_det _ _).mp he)) _

end
end PositiveEinsteinFour.Geometry
end


section

/-! A covariant derivative of a two-form, with its direction separated
from the two alternating slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormDerivativeRows_hodge_norm (B : Fin 4 → TwoFormFour) :
    frameTensorSquareNorm (twoFormDerivativeRows (fun i => twoFormHodge (B i))) =
      frameTensorSquareNorm (twoFormDerivativeRows B) := by
  simp only [twoFormDerivativeRows_norm, twoFormHodge.norm_map]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Euler and signature curvature integrals in the normalization
used by the classification. These are metric integrals; their global index
interpretation is a separate step. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {g : SmoothMetric M}

def orientedSignatureDensity (g : SmoothMetric M) (o : FrameOrientation g) (c : M) : ℝ :=
  curvatureSignatureDensity
    (frameTensor (o.frame c).matrix (curvatureCoordinates g c (chartAt FourSpace c c)))

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] in
theorem orientedEulerDensity_eq (o : FrameOrientation g) (hRic : RicciThree g) (c : M) :
    orientedEulerDensity g o c = (3 / (4 * Real.pi ^ 2)) *
      (1 + plusNorm o c ^ 2 + minusNorm o c ^ 2) := by
  exact frame_curvature_eulerDensity (o.frame c) hRic

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] in
theorem orientedSignatureDensity_eq (o : FrameOrientation g) (hRic : RicciThree g) (c : M) :
    orientedSignatureDensity g o c = (1 / (2 * Real.pi ^ 2)) *
      (plusNorm o c ^ 2 - minusNorm o c ^ 2) := by
  exact frame_curvature_signatureDensity (o.frame c) hRic

end
end PositiveEinsteinFour.Geometry
end


section

/-! The determinant of a moving frame in a fixed sheet chart follows the
same sign cocycle that defines the actual orientation cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Matrix Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem orientationCover_frameChartMatrix (g : SmoothMetric M) (x : OrientationCover M)
    (e : FrameBundle (orientationCoverMetric g)) (he : e.base ∈ (chartAt FourSpace x).source) :
    frameChartMatrix (orientationCoverMetric g) x e =
      orientationLinearMatrix ((tangentBundleCore I4 M).coordChange
        (achart FourSpace e.base.proj) (achart FourSpace x.proj) e.base.proj) * e.frame.matrix := by
  have hb : e.base.proj ∈ (chartAt FourSpace x.proj).source := by
    have h : orientationCoverLocal x e.base ∈ (chartAt FourSpace x.proj).source := he.2
    simpa only [orientationCoverLocal_apply] using h
  have h₁ := orientationCover_tangent_trivialization x e.base he
  have h₂ := TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I4) hb
  let L : FourSpace →L[ℝ] FourSpace := (tangentBundleCore I4 M).coordChange
    (achart FourSpace e.base.proj) (achart FourSpace x.proj) e.base.proj
  have hl : (trivializationAt FourSpace (TangentSpace I4 : OrientationCover M → Type _) x).continuousLinearMapAt ℝ e.base = L := h₁.trans h₂
  ext a b
  have ht := congrArg (fun A : FourSpace →L[ℝ] FourSpace => A (e.frame.vector b)) hl
  have ht' : ((trivializationAt FourSpace (TangentSpace I4 : OrientationCover M → Type _) x)
      (⟨e.base, e.frame.vector b⟩ : TangentBundle I4 (OrientationCover M))).2 =
      L (e.frame.vector b) := by
    exact (Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt FourSpace (TangentSpace I4 : OrientationCover M → Type _) x)
      (show e.base ∈ (trivializationAt FourSpace (TangentSpace I4 : OrientationCover M → Type _) x).baseSet from he)
      (e.frame.vector b)).symm.trans ht
  change frameChartMatrix (orientationCoverMetric g) x e a b = _
  rw [show frameChartMatrix (orientationCoverMetric g) x e a b = L (e.frame.vector b) a from
    congrArg (fun v : FourSpace => v a) ht']
  have hv : e.frame.vector b = ∑ k, e.frame.matrix k b • coordinateVector k :=
    (sum_coordinateVector (fun k => e.frame.matrix k b)).symm
  rw [hv, map_sum]
  simp only [map_smul, WithLp.ofLp_sum, PiLp.smul_apply, smul_eq_mul, Finset.sum_apply,
    orientationLinearMatrix, Matrix.mul_apply, L]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem orientationCover_frameChartMatrix_det (g : SmoothMetric M) (x : OrientationCover M)
    (e : FrameBundle (orientationCoverMetric g)) (he : e.base ∈ (chartAt FourSpace x).source) :
    (frameChartMatrix (orientationCoverMetric g) x e).det =
      orientationTransitionDet (achart FourSpace e.base.proj) (achart FourSpace x.proj)
        e.base.proj * e.frame.matrix.det := by
  rw [orientationCover_frameChartMatrix g x e he, Matrix.det_mul, orientationLinearMatrix_det]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The tautological orientation on the actual determinant-sign cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Matrix Set Filter _root_.Topology
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem orientationCover_positive_in_chart (g : SmoothMetric M) (x : OrientationCover M)
    (e : FrameBundle (orientationCoverMetric g)) (he : e.base ∈ (chartAt FourSpace x).source) :
    e ∈ orientationCoverPositiveFrames g ↔
      ((orientationCoverCore (M := M)).localTriv (achart FourSpace x.proj) e.base).2 =
        decide (0 < (frameChartMatrix (orientationCoverMetric g) x e).det) := by
  have hb : e.base.proj ∈ (chartAt FourSpace x.proj).source := by
    have h : orientationCoverLocal x e.base ∈ (chartAt FourSpace x.proj).source := he.2
    simpa only [orientationCoverLocal_apply] using h
  have ha := orientationTransitionDet_ne_zero (achart FourSpace e.base.proj)
    (achart FourSpace x.proj) ⟨mem_chart_source FourSpace e.base.proj, hb⟩
  rw [orientationCover_frameChartMatrix_det g x e he]
  change e.base.snd = decide (0 < e.frame.matrix.det) ↔
    (if 0 < orientationTransitionDet (achart FourSpace e.base.proj)
        (achart FourSpace x.proj) e.base.proj then e.base.snd else !e.base.snd) = _
  exact (bool_orientation_change _ _ ha e.frame.det_ne_zero _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Haar probability on a positive frame fiber is independent of its
reference frame. This is the fiberwise part of geometric disintegration. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

instance orientedFiberMeasure_probability (e : OrthonormalFrame g c) :
    IsProbabilityMeasure (orientedFiberMeasure e) := by
  unfold orientedFiberMeasure
  first | exact Measure.isProbabilityMeasure_map (by first | (apply Continuous.aemeasurable; apply continuous_orientedFrameMap <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite regularity for the scalar functions used by the compact heat
parametrix. Four derivatives suffice for the value, gradient and Hessian
identities; no smooth extension of the parametrix is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_finite_contDiffAt (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) {k : ℕ}
    (T : FourSpace → CovariantCoordinates k) (n : ℕ)
    (hT : ∀ a, ContDiffAt ℝ (n + 1) (fun w => T w a) z)
    (a : Fin (k + 1) → Fin 4) :
    ContDiffAt ℝ n (fun w => covariantDerivative g c T w a) z := by
  unfold covariantDerivative
  apply (((hT _).fderiv_right (m := n) (by norm_cast)).clm_apply contDiffAt_const).sub
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro b _
  exact ((christoffel_contDiffAt g c z hz
    (metricInChart_posDef g c z hz).det_pos.ne' b (a 0) (a i.succ)).of_le
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mul ((hT _).of_le (by norm_cast; omega))

theorem scalar_finite_derivative_contDiffAt (g : SmoothMetric M) {f : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (c : M) (k n : ℕ) (hkn : n + k ≤ 4)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (a : Fin k → Fin 4) :
    ContDiffAt ℝ n (fun w => iteratedScalarDerivative g f c k w a) z := by
  induction k generalizing n with
  | zero =>
    exact ((hf.contMDiffAt.comp z (contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas c) hz)).contDiffAt).of_le
        (by exact_mod_cast (show n ≤ 4 by omega))
  | succ k ih =>
    exact covariantDerivative_finite_contDiffAt g c z hz
      (iteratedScalarDerivative g f c k) n
      (fun a => ih (n + 1) (by omega) a) a

theorem scalar_finite_derivative_transition (g : SmoothMetric M) {f : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (c d : M) (k : ℕ) (hk : k ≤ 3)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    iteratedScalarDerivative g f c k z = frameTensor (chartTransitionMatrix c d z)
      (iteratedScalarDerivative g f d k (chartTransition c d z)) := by
  induction k generalizing z with
  | zero => exact scalarCoordinates_transition f c d z hz hx
  | succ k ih =>
    apply covariantDerivative_chart_transition g c d
      (iteratedScalarDerivative g f c k) (iteratedScalarDerivative g f d k) z hz hx
    · intro a
      exact (scalar_finite_derivative_contDiffAt g hf d k 1 (by omega)
        (chartTransition c d z) ((chartAt FourSpace d).map_source hx) a).differentiableAt one_ne_zero
    · exact (chart_overlap_eventually c d z hz hx).mono
        (fun w hw => ih (by omega) w hw.1 hw.2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local second-order operator underlying the actual scalar Laplacian.
Its principal coefficient matrix is the smooth positive definite inverse
metric; all lower-order coefficients are the actual Christoffel symbols. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalarCoordinate_gradient (g : SmoothMetric M) (a : M → ℝ)
    (c : M) (z : FourSpace) (i : Fin 4) :
    iteratedScalarDerivative g a c 1 z ![i] =
      partialDeriv (fun w => a ((chartAt FourSpace c).symm w)) i z := by
  simp only [iteratedScalarDerivative, covariantDerivative, scalarCoordinates,
    Fin.sum_univ_zero, sub_zero, Matrix.cons_val_zero]

theorem scalarCoordinate_hessian (g : SmoothMetric M) (a : M → ℝ)
    (c : M) (z : FourSpace) (i j : Fin 4) :
    iteratedScalarDerivative g a c 2 z ![i, j] =
      partialDeriv (fun w => partialDeriv
        (fun v => a ((chartAt FourSpace c).symm v)) j w) i z -
      ∑ k, christoffel g c z k i j *
        partialDeriv (fun w => a ((chartAt FourSpace c).symm w)) k z := by
  have hzero (w : FourSpace) (v : Fin 1 → Fin 4) :
      iteratedScalarDerivative g a c 1 w v =
        partialDeriv (fun x => a ((chartAt FourSpace c).symm x)) (v 0) w := by
    simp only [iteratedScalarDerivative, covariantDerivative, scalarCoordinates,
      Fin.sum_univ_zero, sub_zero]
  change partialDeriv
    (fun w => iteratedScalarDerivative g a c 1 w (fun k => (![i, j] : Fin 2 → Fin 4) k.succ))
      i z - _ = _
  simp only [hzero, Fin.sum_univ_one, Matrix.cons_val_zero, Function.update_self]
  rfl

theorem scalarPrincipalCoefficients_smooth (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => (metricInChart g c w)⁻¹ i j) z :=
  metricInChart_inv_contDiffAt g c z hz (metricInChart_posDef g c z hz).det_pos.ne' i j

end
end PositiveEinsteinFour.Geometry
end


section

/-! The contraction used by the curvature action on two-forms commutes
with actual orthogonal changes of frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem frameTensorPairing_ext {n : ℕ} (S T : CovariantCoordinates n)
    (h : ∀ U, frameTensorPairing S U = frameTensorPairing T U) : S = T := by
  funext a
  have ha := h (Pi.single a 1)
  simpa [frameTensorPairing, Pi.single_apply] using ha

theorem twoTensorContraction_frame (P : Mat4) (hP : P * Pᵀ = 1)
    (R : CovariantCoordinates 4) (T : CovariantCoordinates 2) :
    twoTensorContraction (frameTensor P R) (frameTensor P T) =
      frameTensor P (twoTensorContraction R T) := by
  apply frameTensorPairing_ext
  intro U
  let S := frameTensor Pᵀ U
  have hS : frameTensor P S = U := by
    dsimp [S]
    rw [← frameTensor_mul, mul_eq_one_comm.mp hP, frameTensor_one]
  calc
    _ = frameTensorPairing (frameTensor P R)
        (twoTensorProduct U (frameTensor P T)) := twoTensorContraction_pairing _ _ _
    _ = frameTensorPairing (frameTensor P R) (frameTensor P (twoTensorProduct S T)) := by
      rw [frameTensor_twoProduct, hS]
    _ = frameTensorPairing R (twoTensorProduct S T) := frameTensor_pairing_orthogonal P hP _ _
    _ = frameTensorPairing (twoTensorContraction R T) S := (twoTensorContraction_pairing _ _ _).symm
    _ = frameTensorPairing (frameTensor P (twoTensorContraction R T)) (frameTensor P S) :=
      (frameTensor_pairing_orthogonal P hP _ _).symm
    _ = _ := by rw [hS]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The curvature term in the coordinate Jacobi equation, expressed in
an actual orthonormal frame, has normal matrix `1 + frameCurvatureField`. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem actual_jacobiCurvatureCombination_frame (e : OrthonormalFrame g c)
    (v : JacobiCoordinateVector) :
    e.matrix⁻¹ * jacobiCurvatureCombination
        (fun i j => coordinateCurvatureMatrix g c i j (chartAt FourSpace c c))
        (e.matrix *ᵥ v) (fun a => e.matrix a 0) * e.matrix =
      ∑ i, v i • curvatureEndomorphism (frameCurvature g c e) i 0 := by
  rw [jacobiCurvatureCombination_frame]
  simp only [frame_curvatureEndomorphism]

theorem actual_normal_jacobi_curvature (e : OrthonormalFrame g c) (v : Fin 3 → ℝ) :
    e.matrix⁻¹ *ᵥ (jacobiCurvatureCombination
        (fun i j => coordinateCurvatureMatrix g c i j (chartAt FourSpace c c))
        (e.matrix *ᵥ Fin.cons 0 v) (fun a => e.matrix a 0) *ᵥ
          (fun a => e.matrix a 0)) =
      Fin.cons 0 ((1 + frameCurvatureField g ⟨c, e⟩) *ᵥ v) := by
  have hcol : (fun a => e.matrix a 0) = e.matrix *ᵥ Pi.single 0 1 := by
    ext a
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h : e.matrix⁻¹ *ᵥ (jacobiCurvatureCombination
        (fun i j => coordinateCurvatureMatrix g c i j (chartAt FourSpace c c))
        (e.matrix *ᵥ Fin.cons 0 v) (fun a => e.matrix a 0) *ᵥ
          (fun a => e.matrix a 0)) =
      (∑ i : Fin 4, (Fin.cons (0 : ℝ) v : Fin 4 → ℝ) i •
        curvatureEndomorphism (frameCurvature g c e) i 0) *ᵥ
        Pi.single 0 1 := by
    have hm := congrArg (fun A : Mat4 => A *ᵥ Pi.single 0 1)
      (actual_jacobiCurvatureCombination_frame e (Fin.cons 0 v))
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hcol] at hm
    exact hm
  rw [h]
  ext a
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  refine Fin.cases ?_ (fun i => ?_) a
  · simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, curvatureEndomorphism,
      Fin.cons_zero]
    apply Finset.sum_eq_zero
    intro i _
    have hs := frameCurvature_last_skew e i 0 0 0
    have hz : frameCurvature g c e i 0 0 0 = 0 := by linarith
    rw [hz, mul_zero]
  · have hs := frameJacobiMatrix_symmetric (g := g) ⟨c, e⟩
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, curvatureEndomorphism,
      Fin.cons_succ]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add,
      Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    have hij := congrArg (fun A : Mat3 => A i j) hs
    simp only [Matrix.transpose_apply, frameJacobiMatrix_apply] at hij
    rw [hij]
    rw [frameJacobiMatrix_apply]
    ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual linearization of the tangent-coordinate geodesic vector
field. Its formula is derived from the Christoffel coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def geodesicCoordinateField (g : SmoothMetric M) (c : M)
    (p : FourSpace × FourSpace) : FourSpace × FourSpace :=
  (p.2, WithLp.toLp 2 (-(jacobiConnection
    (fun i => connectionMatrix g c i p.1) (WithLp.ofLp p.2) *ᵥ WithLp.ofLp p.2)))

def geodesicVariationAcceleration (g : SmoothMetric M) (c : M)
    (x v y w : FourSpace) : FourSpace :=
  WithLp.toLp 2 (-(jacobiConnectionDerivative
      (fun i j => matrixPartial (connectionMatrix g c j) i x)
      (WithLp.ofLp y) (WithLp.ofLp v) *ᵥ WithLp.ofLp v) -
    jacobiConnection (fun i => connectionMatrix g c i x) (WithLp.ofLp w) *ᵥ
      WithLp.ofLp v -
    jacobiConnection (fun i => connectionMatrix g c i x) (WithLp.ofLp v) *ᵥ
      WithLp.ofLp w)

theorem geodesicCoordinateField_contDiffAt (g : SmoothMetric M) (c : M)
    (p : FourSpace × FourSpace) (hp : p.1 ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (geodesicCoordinateField g c) p := by
  have hΓ (a i j : Fin 4) : ContDiffAt ℝ ∞
      (fun q : FourSpace × FourSpace => christoffel g c q.1 a i j) p :=
    (christoffel_contDiffAt g c p.1 hp (metricInChart_posDef g c p.1 hp).det_pos.ne'
      a i j).comp p contDiffAt_fst
  apply contDiffAt_snd.prodMk
  apply (contDiffAt_piLp 2).mpr
  intro a
  change ContDiffAt ℝ ∞ (fun q : FourSpace × FourSpace =>
    -(∑ j, (∑ i, q.2 i * christoffel g c q.1 a i j) * q.2 j)) p
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.mul
  · apply ContDiffAt.sum
    intro i _
    have hv : ContDiffAt ℝ ∞ (fun q : FourSpace × FourSpace => q.2 i) p := by
      fun_prop
    exact hv.mul (hΓ a i j)
  · fun_prop

theorem connection_variation_derivative (g : SmoothMetric M) (c : M)
    (x v : ℝ → FourSpace) (y w : FourSpace) (t : ℝ)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x y t) (hv : HasDerivAt v w t) :
    HasDerivAt (fun s => jacobiConnection (fun i => connectionMatrix g c i (x s))
      (WithLp.ofLp (v s)))
      (jacobiConnectionDerivative
        (fun i j => matrixPartial (connectionMatrix g c j) i (x t))
        (WithLp.ofLp y) (WithLp.ofLp (v t)) +
        jacobiConnection (fun i => connectionMatrix g c i (x t)) (WithLp.ofLp w)) t := by
  apply hasDerivAt_pi.mpr
  intro a
  apply hasDerivAt_pi.mpr
  intro b
  have hΓ (k : Fin 4) : HasDerivAt
      (fun s => connectionMatrix g c k (x s) a b)
      (∑ r, y r * matrixPartial (connectionMatrix g c k) r (x t) a b) t :=
    hasDerivAt_coordinate_comp hx
      ((christoffel_contDiffAt g c (x t) hz (metricInChart_posDef g c (x t) hz).det_pos.ne'
        a k b).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hvk (k : Fin 4) : HasDerivAt (fun s => v s k) (w k) t :=
    (EuclideanSpace.proj k : FourSpace →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have h := HasDerivAt.fun_sum (fun k (_ : k ∈ Finset.univ) => (hvk k).mul (hΓ k))
  have heq : (∑ k, (w k * connectionMatrix g c k (x t) a b +
      v t k * (∑ r, y r * matrixPartial (connectionMatrix g c k) r (x t) a b))) =
      (jacobiConnectionDerivative
        (fun r k => matrixPartial (connectionMatrix g c k) r (x t))
        (WithLp.ofLp y) (WithLp.ofLp (v t)) +
        jacobiConnection (fun k => connectionMatrix g c k (x t)) (WithLp.ofLp w)) a b := by
    simp only [jacobiConnectionDerivative, jacobiConnection, Matrix.add_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    rw [add_comm]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [heq] at h
  exact h

theorem geodesicCoordinateField_curve_derivative (g : SmoothMetric M) (c : M)
    (x v : ℝ → FourSpace) (y w : FourSpace) (t : ℝ)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x y t) (hv : HasDerivAt v w t) :
    HasDerivAt (fun s => geodesicCoordinateField g c (x s, v s))
      (w, geodesicVariationAcceleration g c (x t) (v t) y w) t := by
  have hU := connection_variation_derivative g c x v y w t hz hx hv
  have hacc (a : Fin 4) : HasDerivAt (fun s =>
      -(jacobiConnection (fun i => connectionMatrix g c i (x s))
        (WithLp.ofLp (v s)) *ᵥ WithLp.ofLp (v s)) a)
      (geodesicVariationAcceleration g c (x t) (v t) y w a) t := by
    have hvj (j : Fin 4) : HasDerivAt (fun s => v s j) (w j) t :=
      (EuclideanSpace.proj j : FourSpace →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hv
    have h := (HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hU a) j).mul (hvj j))).neg
    have heq : -(∑ j,
        ((jacobiConnectionDerivative
          (fun i k => matrixPartial (connectionMatrix g c k) i (x t))
          (WithLp.ofLp y) (WithLp.ofLp (v t)) +
            jacobiConnection (fun i => connectionMatrix g c i (x t))
              (WithLp.ofLp w)) a j * v t j +
          jacobiConnection (fun i => connectionMatrix g c i (x t))
            (WithLp.ofLp (v t)) a j * w j)) =
        geodesicVariationAcceleration g c (x t) (v t) y w a := by
      simp only [geodesicVariationAcceleration, Matrix.mulVec, dotProduct,
        Matrix.add_apply, Pi.neg_apply, Pi.sub_apply, add_mul,
        Finset.sum_add_distrib]
      ring
    rw [heq] at h
    simpa only [Matrix.mulVec, dotProduct, Pi.neg_apply, Pi.mul_apply] using! h
  have hforce := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt t
    (hasDerivAt_pi.mpr hacc)
  exact hv.prodMk hforce

theorem geodesicCoordinateField_fderiv (g : SmoothMetric M) (c : M)
    (x v y w : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    fderiv ℝ (geodesicCoordinateField g c) (x, v) (y, w) =
      (w, geodesicVariationAcceleration g c x v y w) := by
  have hxc : HasDerivAt (fun s : ℝ => x + s • y) y 0 := by
    simpa only [Pi.add_apply, id_eq, one_smul, zero_add] using!
      (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const y)
  have hvc : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    simpa only [Pi.add_apply, id_eq, one_smul, zero_add] using!
      (hasDerivAt_const (0 : ℝ) v).add ((hasDerivAt_id (0 : ℝ)).smul_const w)
  have hactual := geodesicCoordinateField_curve_derivative g c
    (fun s : ℝ => x + s • y) (fun s : ℝ => v + s • w) y w 0
    (by simpa only [zero_smul, add_zero] using hx) hxc hvc
  have hf := (geodesicCoordinateField_contDiffAt g c (x, v) hx).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hf' : HasFDerivAt (geodesicCoordinateField g c)
      (fderiv ℝ (geodesicCoordinateField g c) (x, v)) (x + (0 : ℝ) • y, v + (0 : ℝ) • w) := by
    simpa only [zero_smul, add_zero] using hf.hasFDerivAt
  have hd := hf'.comp_hasDerivAt 0 (hxc.prodMk hvc)
  simpa only [zero_smul, add_zero] using hd.unique hactual

/-- The variational equation of the actual tangent vector field gives
the two ordinary derivative inputs of the coordinate Jacobi theorem. -/
theorem geodesic_variation_derivatives (g : SmoothMetric M) (c : M)
    (γ Z : ℝ → FourSpace × FourSpace) (t : ℝ)
    (hz : (γ t).1 ∈ (chartAt FourSpace c).target)
    (hZ : HasDerivAt Z (fderiv ℝ (geodesicCoordinateField g c) (γ t) (Z t)) t) :
    HasDerivAt (fun s => (Z s).1) (Z t).2 t ∧
      HasDerivAt (fun s => (Z s).2)
        (geodesicVariationAcceleration g c (γ t).1 (γ t).2 (Z t).1 (Z t).2) t := by
  rw [geodesicCoordinateField_fderiv g c (γ t).1 (γ t).2 (Z t).1 (Z t).2 hz] at hZ
  exact ⟨hZ.fst, hZ.snd⟩

def geodesicVariationCovariantDerivative (g : SmoothMetric M) (c : M)
    (γ Z : ℝ → FourSpace × FourSpace) : ℝ → JacobiCoordinateVector :=
  geodesicCovariantDerivative g c (fun s => (γ s).1)
    (fun s => WithLp.ofLp (γ s).2) (fun s => WithLp.ofLp (Z s).1)
    (fun s => WithLp.ofLp (Z s).2)

theorem geodesic_variation_covariant_differentiableAt (g : SmoothMetric M) (c : M)
    (γ Z : ℝ → FourSpace × FourSpace) (t : ℝ)
    (hz : (γ t).1 ∈ (chartAt FourSpace c).target)
    (hγ : DifferentiableAt ℝ γ t) (hZ : DifferentiableAt ℝ Z t) :
    DifferentiableAt ℝ (geodesicVariationCovariantDerivative g c γ Z) t := by
  have hc (a i j : Fin 4) : DifferentiableAt ℝ
      (fun s => christoffel g c (γ s).1 a i j) t := by
    have hdΓ : DifferentiableAt ℝ (fun x : FourSpace => christoffel g c x a i j)
        (γ t).1 := (christoffel_contDiffAt g c (γ t).1 hz
      (metricInChart_posDef g c (γ t).1 hz).det_pos.ne' a i j).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact hdΓ.comp (f := fun s => (γ s).1) t hγ.fst
  have hv (i : Fin 4) : DifferentiableAt ℝ (fun s => (γ s).2 i) t :=
    (EuclideanSpace.proj i : FourSpace →L[ℝ] ℝ).differentiableAt.comp t hγ.snd
  have hy (i : Fin 4) : DifferentiableAt ℝ (fun s => (Z s).1 i) t :=
    (EuclideanSpace.proj i : FourSpace →L[ℝ] ℝ).differentiableAt.comp t hZ.fst
  have hw (i : Fin 4) : DifferentiableAt ℝ (fun s => (Z s).2 i) t :=
    (EuclideanSpace.proj i : FourSpace →L[ℝ] ℝ).differentiableAt.comp t hZ.snd
  apply differentiableAt_pi.mpr
  intro a
  change DifferentiableAt ℝ (fun s => (Z s).2 a +
    ∑ j, (∑ i, (γ s).2 i * christoffel g c (γ s).1 a i j) * (Z s).1 j) t
  exact (hw a).add (DifferentiableAt.fun_sum fun j _ =>
    (DifferentiableAt.fun_sum fun i _ => (hv i).mul (hc a i j)).mul (hy j))

/-- A true first variation of the actual coordinate geodesic field
satisfies the curvature Jacobi equation. -/
theorem geodesic_variation_jacobi (g : SmoothMetric M) (c : M)
    (γ Z : ℝ → FourSpace × FourSpace) (t : ℝ)
    (hz : (γ t).1 ∈ (chartAt FourSpace c).target)
    (hγ : HasDerivAt γ (geodesicCoordinateField g c (γ t)) t)
    (hZ : HasDerivAt Z (fderiv ℝ (geodesicCoordinateField g c) (γ t) (Z t)) t) :
    deriv (geodesicVariationCovariantDerivative g c γ Z) t +
      jacobiConnection (fun i => connectionMatrix g c i (γ t).1)
        (WithLp.ofLp (γ t).2) *ᵥ geodesicVariationCovariantDerivative g c γ Z t +
      (∑ i, ∑ j, ((Z t).1 i * (γ t).2 j) •
        coordinateCurvatureMatrix g c i j (γ t).1) *ᵥ WithLp.ofLp (γ t).2 = 0 := by
  let v : ℝ → JacobiCoordinateVector := fun s => WithLp.ofLp (γ s).2
  let y : ℝ → JacobiCoordinateVector := fun s => WithLp.ofLp (Z s).1
  let w : ℝ → JacobiCoordinateVector := fun s => WithLp.ofLp (Z s).2
  let a : JacobiCoordinateVector :=
    -(jacobiConnection (fun i => connectionMatrix g c i (γ t).1) (v t) *ᵥ v t)
  let b : JacobiCoordinateVector :=
    WithLp.ofLp (geodesicVariationAcceleration g c (γ t).1 (γ t).2 (Z t).1 (Z t).2)
  have hv : HasDerivAt v a t := by
    apply hasDerivAt_pi.mpr
    intro i
    exact (EuclideanSpace.proj i : FourSpace →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hγ.snd
  have hvar := geodesic_variation_derivatives g c γ Z t hz hZ
  have hy : HasDerivAt y (w t) t := by
    apply hasDerivAt_pi.mpr
    intro i
    exact (EuclideanSpace.proj i : FourSpace →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hvar.1
  have hw : HasDerivAt w b t := by
    apply hasDerivAt_pi.mpr
    intro i
    exact (EuclideanSpace.proj i : FourSpace →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hvar.2
  exact coordinate_geodesic_jacobi g c (fun s => (γ s).1) v y w a b t hz
    hγ.fst hv hy hw rfl rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second-variation density and boundary term in an actual metric chart.
All metric, connection and curvature coefficients come from the existing
Levi-Civita definitions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def jacobiMetricFirstDirectional (g : SmoothMetric M) (c : M) (z : FourSpace)
    (y : JacobiCoordinateVector) : Mat4 :=
  ∑ i, y i • matrixPartial (metricInChart g c) i z

def jacobiMetricSecondDirectional (g : SmoothMetric M) (c : M) (z : FourSpace)
    (y : JacobiCoordinateVector) : Mat4 :=
  ∑ i, ∑ j, (y i * y j) • matrixPartial (matrixPartial (metricInChart g c) j) i z

theorem jacobiMetricFirstDirectional_eq (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (y : JacobiCoordinateVector) :
    jacobiMetricFirstDirectional g c z y =
      jacobiMetricRate (metricInChart g c z)
        (jacobiConnection (fun i => connectionMatrix g c i z) y) :=
  parallelFrame_metric_rate g c z hz y

theorem jacobiMetricSecondDirectional_eq (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (y : JacobiCoordinateVector) :
    jacobiMetricSecondDirectional g c z y =
      jacobiMetricSecondRate (metricInChart g c z)
        (jacobiConnection (fun i => connectionMatrix g c i z) y)
        (jacobiConnectionDerivative
          (fun i j => matrixPartial (connectionMatrix g c j) i z) y y) := by
  unfold jacobiMetricSecondDirectional
  simp_rw [matrixPartial_metric_second g c z hz (metricInChart_posDef g c z hz).det_pos.ne']
  rw [weightedMetricSecond_identity]
  have hfirst : (∑ i, y i • matrixPartial (metricInChart g c) i z) =
      jacobiMetricRate (metricInChart g c z)
        (jacobiConnection (fun i => connectionMatrix g c i z) y) :=
    jacobiMetricFirstDirectional_eq g c z hz y
  rw [hfirst]
  rfl

theorem actual_jacobiCurvature_metric_skew (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (y v : JacobiCoordinateVector) :
    (jacobiCurvature (fun i => connectionMatrix g c i z)
        (fun i j => matrixPartial (connectionMatrix g c j) i z) y v)ᵀ * metricInChart g c z +
      metricInChart g c z * jacobiCurvature (fun i => connectionMatrix g c i z)
        (fun i j => matrixPartial (connectionMatrix g c j) i z) y v = 0 := by
  rw [actual_jacobiCurvature_eq]
  simp only [Matrix.transpose_sum, Matrix.transpose_smul, Finset.sum_mul,
    Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  rw [← smul_add, coordinateCurvatureMatrix_skew g c z hz
    (metricInChart_posDef g c z hz).det_pos.ne']
  simp

theorem actual_coordinateEnergySecondDensity (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (v y w : JacobiCoordinateVector) :
    coordinateEnergySecondDensity (metricInChart g c z)
        (jacobiMetricFirstDirectional g c z y) (jacobiMetricSecondDirectional g c z y) v w =
      coordinateIndexDensity (metricInChart g c z) (fun i => connectionMatrix g c i z)
          (fun i j => matrixPartial (connectionMatrix g c j) i z) v y w +
        coordinateEnergyBoundaryRate (metricInChart g c z) (fun i => connectionMatrix g c i z)
          (fun i j => matrixPartial (connectionMatrix g c j) i z) v y w := by
  rw [jacobiMetricFirstDirectional_eq g c z hz, jacobiMetricSecondDirectional_eq g c z hz]
  apply coordinateEnergySecondDensity_eq_index_add_boundary
  · ext i j
    exact metricInChart_comm g c z j i
  · exact fun a i j => christoffel_comm g c z a i j
  · intro r a i j
    change partialDeriv (fun p => christoffel g c p a i j) r z =
      partialDeriv (fun p => christoffel g c p a j i) r z
    exact congrArg (fun f : FourSpace → ℝ => partialDeriv f r z)
      (funext fun p => christoffel_comm g c p a i j)
  · exact actual_jacobiCurvature_metric_skew g c z hz y v

theorem hasDerivAt_connection_weighted (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (y : ℝ → JacobiCoordinateVector)
    (v w : JacobiCoordinateVector) (t : ℝ)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x (WithLp.toLp 2 v) t) (hy : HasDerivAt y w t) :
    HasDerivAt (fun s => jacobiConnection (fun i => connectionMatrix g c i (x s)) (y s))
      (jacobiConnectionDerivative
        (fun i j => matrixPartial (connectionMatrix g c j) i (x t)) v (y t) +
        jacobiConnection (fun i => connectionMatrix g c i (x t)) w) t := by
  apply hasDerivAt_pi.mpr
  intro a
  apply hasDerivAt_pi.mpr
  intro b
  have hΓ (j : Fin 4) : HasDerivAt (fun s => connectionMatrix g c j (x s) a b)
      (∑ i, v i * matrixPartial (connectionMatrix g c j) i (x t) a b) t :=
    hasDerivAt_coordinate_comp hx
      ((christoffel_contDiffAt g c (x t) hz (metricInChart_posDef g c (x t) hz).det_pos.ne'
        a j b).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hh := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
    (hasDerivAt_pi.mp hy j).mul (hΓ j))
  have heq : (∑ j, (w j * connectionMatrix g c j (x t) a b +
      y t j * (∑ i, v i * matrixPartial (connectionMatrix g c j) i (x t) a b))) =
      (jacobiConnectionDerivative
        (fun i j => matrixPartial (connectionMatrix g c j) i (x t)) v (y t) +
        jacobiConnection (fun i => connectionMatrix g c i (x t)) w) a b := by
    simp only [jacobiConnectionDerivative, jacobiConnection, Matrix.add_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
    rw [add_comm]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq] at hh
  exact hh

/-- The boundary correction is the derivative of an actual scalar along
a coordinate geodesic. Its vanishing at zero variation endpoints can therefore
be used by the ordinary fundamental theorem of calculus. -/
theorem actual_coordinateEnergyBoundary_hasDerivAt (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (v y : ℝ → JacobiCoordinateVector)
    (a w : JacobiCoordinateVector) (t : ℝ)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x (WithLp.toLp 2 (v t)) t)
    (hv : HasDerivAt v a t) (hy : HasDerivAt y w t)
    (ha : a = -(jacobiConnection (fun i => connectionMatrix g c i (x t)) (v t) *ᵥ v t)) :
    HasDerivAt
      (fun s => jacobiMetricPair (metricInChart g c (x s)) (v s)
        (jacobiConnection (fun i => connectionMatrix g c i (x s)) (y s) *ᵥ y s))
      (coordinateEnergyBoundaryRate (metricInChart g c (x t))
        (fun i => connectionMatrix g c i (x t))
        (fun i j => matrixPartial (connectionMatrix g c j) i (x t)) (v t) (y t) w) t := by
  let G : ℝ → Mat4 := fun s => metricInChart g c (x s)
  let A := jacobiConnection (fun i => connectionMatrix g c i (x t)) (v t)
  let B : ℝ → Mat4 := fun s => jacobiConnection (fun i => connectionMatrix g c i (x s)) (y s)
  let E := jacobiConnectionDerivative
    (fun i j => matrixPartial (connectionMatrix g c j) i (x t)) (v t) (y t)
  let W := jacobiConnection (fun i => connectionMatrix g c i (x t)) w
  have hG (i j : Fin 4) : HasDerivAt (fun s => G s i j)
      (jacobiMetricRate (G t) A i j) t := by
    rw [← jacobiMetricFirstDirectional_eq g c (x t) hz (v t)]
    have hd := hasDerivAt_coordinate_comp hx
      ((metricInChart_contDiffAt g c (x t) hz i j).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    simpa only [G, jacobiMetricFirstDirectional, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, matrixPartial] using hd
  have hB : HasDerivAt B (E + W) t :=
    hasDerivAt_connection_weighted g c x y (v t) w t hz hx hy
  have hu := hasDerivAt_matrix_vector B (E + W) y w t hB hy
  have hp := hasDerivAt_metricPair G (jacobiMetricRate (G t) A) v
    (fun s => B s *ᵥ y s) a ((E + W) *ᵥ y t + B t *ᵥ w) t hG hv hu
  have hcomm : W *ᵥ y t = B t *ᵥ w :=
    actual_jacobiConnection_comm g c (x t) w (y t)
  have hrhs : jacobiMetricPair (jacobiMetricRate (G t) A) (v t) (B t *ᵥ y t) +
      jacobiMetricPair (G t) a (B t *ᵥ y t) +
      jacobiMetricPair (G t) (v t) ((E + W) *ᵥ y t + B t *ᵥ w) =
      coordinateEnergyBoundaryRate (G t) (fun i => connectionMatrix g c i (x t))
        (fun i j => matrixPartial (connectionMatrix g c j) i (x t)) (v t) (y t) w := by
    change a = -(A *ᵥ v t) at ha
    rw [jacobiMetricRate_pair, ha, jacobiMetricPair_neg_left,
      Matrix.add_mulVec, hcomm]
    change _ = jacobiMetricPair (G t) (v t)
      (A *ᵥ (B t *ᵥ y t) + E *ᵥ y t + (2 : ℝ) • (B t *ᵥ w))
    simp only [jacobiMetricPair_add_right, jacobiMetricPair_smul_right]
    ring
  rw [hrhs] at hp
  exact hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The integrated Weyl identity follows from the actual pointwise Weyl
equation and measure-preserving parallel-frame differentiation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

namespace MetricGreenData

theorem integratedWeylEquation (d : MetricGreenData g μ) :
    (∫ e, Angular.gradientSquareNorm (plusWeylGradient g e.base e.frame) ∂μ) =
      36 * (∫ e, normalizedDeterminantShape (plusWeyl g e.base e.frame) *
        normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 3 -
        normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 ∂μ) := by
  let W : C(FrameBundle g, MatrixVector) :=
    ⟨fun e => matrixVector (plusWeyl g e.base e.frame),
      matrixVectorMap.continuous.comp d.continuousWeyl⟩
  let Z (i : Fin 4) : C(FrameBundle g, MatrixVector) :=
    ⟨fun e => matrixVector (plusWeylGradient g e.base e.frame i),
      matrixVectorMap.continuous.comp (d.continuousGradient i)⟩
  let H (i : Fin 4) : C(FrameBundle g, MatrixVector) :=
    ⟨fun e => matrixVector (plusWeylHessian g e.base e.frame i i),
      matrixVectorMap.continuous.comp (d.continuousHessian i i)⟩
  have h := Averages.weighted_four_direction_green μ
    (fun i => (d.flow i).map) (fun i => (d.flow i).continuous)
    (fun i => (d.flow i).preserves) (1 : C(FrameBundle g, ℝ))
    (fun _ => 0) W Z H
    (fun _ t _ => hasDerivAt_const t (1 : ℝ))
    (fun i t e => hasDerivAt_matrixVector (d.derivativeWeyl i t e))
    (fun i t e => hasDerivAt_matrixVector (d.derivativeGradient i i t e))
  have hZ (e : FrameBundle g) : (∑ i, ‖Z i e‖ ^ 2) =
      Angular.gradientSquareNorm (plusWeylGradient g e.base e.frame) := by
    change (∑ i, ‖matrixVector (plusWeylGradient g e.base e.frame i)‖ ^ 2) = _
    simp_rw [matrixVector_norm_sq]
    simp only [Angular.gradientSquareNorm, Angular.squareNorm, matrixPairing, pow_two]
  have hH (e : FrameBundle g) : (∑ i, H i e) =
      matrixVector (hessianTrace (plusWeylHessian g e.base e.frame)) := by
    change (∑ i, matrixVectorMap (plusWeylHessian g e.base e.frame i i)) =
      matrixVectorMap (∑ i, plusWeylHessian g e.base e.frame i i)
    exact (map_sum matrixVectorMap _ _).symm
  have he : (∫ e, Angular.gradientSquareNorm (plusWeylGradient g e.base e.frame) ∂μ) =
      -(∫ e, matrixPairing (plusWeyl g e.base e.frame)
        (weylLaplacian (plusWeyl g e.base e.frame)) ∂μ) := by
    calc
      _ = -(∫ e, inner ℝ (W e)
          (matrixVector (hessianTrace (plusWeylHessian g e.base e.frame))) ∂μ) := by
        simpa only [ContinuousMap.one_apply, one_mul, ContinuousMap.zero_apply,
          zero_mul, Finset.sum_const_zero, add_zero, hZ, hH] using h
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with e
        change inner ℝ (matrixVector (plusWeyl g e.base e.frame))
          (matrixVector (hessianTrace (plusWeylHessian g e.base e.frame))) = _
        rw [inner_matrixVector, metric_weyl_trace g d.weyl]
  rw [he, ← integral_neg]
  calc
    _ = ∫ e, 36 * (normalizedDeterminantShape (plusWeyl g e.base e.frame) *
        normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 3 -
        normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with e
      rw [weylLaplacian_pairing _ (d.weyl.symmetric e) (d.weyl.traceFree e)]
      ring
    _ = _ := integral_const_mul _ _

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! A proper clopen sheet of the orientation cover supplies a genuine continuous
frame orientation on the base. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Matrix Set Function _root_.Topology
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frame_reflect_det {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) : e.reflect.matrix.det = -e.matrix.det := by
  change (e.matrix * frameReflectionMatrix).det = _
  rw [Matrix.det_mul]
  have hr : frameReflectionMatrix.det = -1 := by
    norm_num [frameReflectionMatrix, Matrix.det_diagonal, orientationSign, Fin.prod_univ_succ]
  rw [hr]
  ring

theorem orientationFrameClass_fiber_surjective (g : SmoothMetric M) (c : M) (b : Bool) :
    ∃ e : OrthonormalFrame g c, orientationFrameClass g ⟨c, e⟩ = ⟨c, b⟩ := by
  classical
  let e := canonicalFrame g c
  have hx : ∃ f : OrthonormalFrame g c, b = decide (0 < f.matrix.det) := by
    by_cases he : b = decide (0 < e.matrix.det)
    · exact ⟨e, he⟩
    · refine ⟨e.reflect, ?_⟩
      rw [frame_reflect_det]
      have hn := e.det_ne_zero
      cases b <;> rcases lt_or_gt_of_ne hn with hn | hn <;>
        simp_all [not_lt.mpr hn.le]
  obtain ⟨f, hf⟩ := hx
  exact ⟨f, congrArg (fun b : Bool => (⟨c, b⟩ : OrientationCover M)) hf.symm⟩

theorem frame_sign_eq_iff {g : SmoothMetric M} {c : M}
    (e f : OrthonormalFrame g c) :
    decide (0 < e.matrix.det) = decide (0 < f.matrix.det) ↔
      0 < e.matrix.det * f.matrix.det := by
  rcases lt_or_gt_of_ne e.det_ne_zero with he | he <;>
    rcases lt_or_gt_of_ne f.det_ne_zero with hf | hf
  · simp [not_lt.mpr he.le, not_lt.mpr hf.le, mul_pos_of_neg_of_neg he hf]
  · simp [not_lt.mpr he.le, hf, not_lt.mpr (mul_neg_of_neg_of_pos he hf).le]
  · simp [he, not_lt.mpr hf.le, not_lt.mpr (mul_neg_of_pos_of_neg he hf).le]
  · simp [he, hf, mul_pos he hf]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Locality and support control for the actual scalar Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set Function
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalarLaplacianBase_coordinate_formula (g : SmoothMetric M) (a : M → ℝ) (c : M) :
    scalarLaplacianBase g a c =
      ∑ i, ∑ j, (chartMetric g c)⁻¹ i j *
        (partialDeriv (fun w => partialDeriv
          (fun v => a ((chartAt FourSpace c).symm v)) j w) i (chartAt FourSpace c c) -
          ∑ k, christoffel g c (chartAt FourSpace c c) k i j *
            partialDeriv (fun w => a ((chartAt FourSpace c).symm w)) k
              (chartAt FourSpace c c)) := by
  rw [scalarLaplacianBase, scalarLaplacian_eq_inverse_trace]
  simp_rw [scalarCoordinate_hessian]
  rfl

theorem scalarLaplacianBase_congr_nhds (g : SmoothMetric M) {a b : M → ℝ}
    {c : M} (h : a =ᶠ[𝓝 c] b) :
    scalarLaplacianBase g a c = scalarLaplacianBase g b c := by
  let z := chartAt FourSpace c c
  have hz : z ∈ (chartAt FourSpace c).target :=
    (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  have hc : Tendsto (chartAt FourSpace c).symm (𝓝 z) (𝓝 c) := by
    simpa only [z, (chartAt FourSpace c).left_inv (mem_chart_source FourSpace c)] using
      ((chartAt FourSpace c).symm.continuousAt hz).tendsto
  have h₀ : (fun w => a ((chartAt FourSpace c).symm w)) =ᶠ[𝓝 z]
      (fun w => b ((chartAt FourSpace c).symm w)) := h.comp_tendsto hc
  have h₁ (i : Fin 4) :
      (fun w => partialDeriv (fun v => a ((chartAt FourSpace c).symm v)) i w) =ᶠ[𝓝 z]
      (fun w => partialDeriv (fun v => b ((chartAt FourSpace c).symm v)) i w) := by
    exact (h₀.fderiv (𝕜 := ℝ)).mono (fun w hw =>
      congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) hw)
  rw [scalarLaplacianBase_coordinate_formula, scalarLaplacianBase_coordinate_formula]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  congr 1
  · exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i))
      ((h₁ j).fderiv_eq (𝕜 := ℝ))
  · apply Finset.sum_congr rfl
    intro k _
    rw [(h₁ k).eq_of_nhds]

theorem scalarLaplacianBase_zero (g : SmoothMetric M) :
    scalarLaplacianBase g (fun _ : M => (0 : ℝ)) = 0 := by
  funext c
  rw [scalarLaplacianBase_coordinate_formula]
  simp [partialDeriv, fderiv_const_apply]

theorem scalarLaplacianBase_tsupport (g : SmoothMetric M) (a : M → ℝ) :
    tsupport (scalarLaplacianBase g a) ⊆ tsupport a := by
  apply closure_minimal _ (isClosed_tsupport a)
  intro c hc
  by_contra hca
  have ha : a =ᶠ[𝓝 c] (fun _ : M => (0 : ℝ)) := by
    filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hca] with x hx
    exact image_eq_zero_of_notMem_tsupport hx
  have hzero := scalarLaplacianBase_congr_nhds g ha
  rw [scalarLaplacianBase_zero] at hzero
  exact hc hzero

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature action on the six two-form coordinates. The
minus sign matches the convention R(i,j,k,l) = <R(i,j)k,l>. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormCurvatureAction_frame (P : Mat4) (hP : P * Pᵀ = 1)
    (R : CovariantCoordinates 4)
    (hR : ∀ i j k l, R ![j,i,k,l] = -R ![i,j,k,l])
    (hRP : ∀ i j k l, frameTensor P R ![j,i,k,l] = -frameTensor P R ![i,j,k,l])
    (a : TwoFormFour) :
    twoFormCurvatureAction (frameTensor P R) (twoFormFrameAction P a) =
      twoFormFrameAction P (twoFormCurvatureAction R a) := by
  apply twoFormTensor_injective
  rw [twoFormTensor_curvature _ hRP, twoFormTensor_frameAction,
    twoTensorContraction_frame P hP, twoFormTensor_frameAction,
    twoFormTensor_curvature _ hR]
  funext v
  exact (frameTensor_const_mul P (-1 / 2) (twoTensorContraction R (twoFormTensor a)) v).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrating the proved Weyl equation bounds the full first derivative
energy. Reflection supplies the opposite block on the same frame measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory Angular
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {X : Type*} [TopologicalSpace X]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

namespace MetricGreenData

local instance frameWeylEnergyInstance1_r0ded1c_1 : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup
local instance frameWeylEnergyInstance2_r0ded1c_1 : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace
theorem weylCubic_integrable (d : MetricGreenData g μ) :
    Integrable (fun e => normalizedDeterminantShape (plusWeyl g e.base e.frame) *
      normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 3 -
      normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2) μ := by
  have hc : Continuous (fun e : FrameBundle g =>
      (plusWeyl g e.base e.frame).det / 2 -
      normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2) :=
    (d.continuousWeyl.matrix_det.div_const 2).sub
      ((continuous_normalizedBlockNorm.comp d.continuousWeyl).pow 2)
  apply (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).congr
  filter_upwards [] with e
  rw [normalizedDeterminantShape_mul]
  ring

theorem weylGradientEnergy_le (d : MetricGreenData g μ)
    (hbound : ∀ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) ≤ 2) :
    (∫ e, gradientSquareNorm (plusWeylGradient g e.base e.frame) ∂μ) ≤
      36 * ∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 ∂μ := by
  apply integrated_gradient_energy_le _ _ d.weylCubic_integrable d.integratedWeylEquation
  · filter_upwards [] with e
    exact ⟨normalizedBlockNorm_nonneg _, hbound e,
      normalizedDeterminantShape_le_one _ (d.weyl.symmetric e) (d.weyl.traceFree e)⟩
  · exact ((continuous_normalizedBlockNorm.comp d.continuousWeyl).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [CompactSpace (FrameBundle g)] in
theorem reflected_gradientSquareNorm (e : FrameBundle g) :
    gradientSquareNorm (plusWeylGradient g (frameReflection e).base (frameReflection e).frame) =
      gradientSquareNorm (minusWeylGradient g e.base e.frame) := by
  have hz : plusWeylGradient g (frameReflection e).base (frameReflection e).frame =
      reflectedGradient (minusWeylGradient g e.base e.frame) := by
    funext i
    exact plusWeylGradient_reflect g e.base e.frame i
  rw [hz]
  simp only [gradientSquareNorm, squareNorm, reflectedGradient,
    Matrix.smul_apply, smul_eq_mul, mul_pow, orientationSign_sq, one_mul]

theorem oppositeWeylGradientEnergy_le (d : MetricGreenData g μ)
    (hparallel : ParallelReflection d)
    (hbound : ∀ e : FrameBundle g, normalizedBlockNorm (minusWeyl g e.base e.frame) ≤ 2) :
    (∫ e, gradientSquareNorm (minusWeylGradient g e.base e.frame) ∂μ) ≤
      36 * ∫ e, normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2 ∂μ := by
  have hb (e : FrameBundle g) : normalizedBlockNorm (plusWeyl g e.base e.frame) ≤ 2 := by
    have he := hbound (frameReflection e)
    simpa only [frameReflection, minusWeyl_reflect] using he
  have h := (d.onReflectedMeasure hparallel).weylGradientEnergy_le hb
  rw [integral_reflectedMeasure, integral_reflectedMeasure] at h
  simpa only [reflected_gradientSquareNorm, blockNorm_frameReflection] using h

theorem totalWeylGradientEnergy_le (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (hparallel : ParallelReflection d)
    (hbound : ∀ e : FrameBundle g,
      normalizedBlockNorm (plusWeyl g e.base e.frame) +
        normalizedBlockNorm (minusWeyl g e.base e.frame) ≤ 2) :
    (∫ e, gradientSquareNorm (plusWeylGradient g e.base e.frame) +
      gradientSquareNorm (minusWeylGradient g e.base e.frame) ∂μ) ≤
    36 * ∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 +
      normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2 ∂μ := by
  have hp := d.weylGradientEnergy_le (fun e => by
    linarith [hbound e, normalizedBlockNorm_nonneg (minusWeyl g e.base e.frame)])
  have hm := d.oppositeWeylGradientEnergy_le hparallel (fun e => by
    linarith [hbound e, normalizedBlockNorm_nonneg (plusWeyl g e.base e.frame)])
  have hpi := (continuous_gradientSquareNorm _ d.continuousGradient).integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hmi := (continuous_gradientSquareNorm _ o.continuousGradient).integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hvi := ((continuous_normalizedBlockNorm.comp d.continuousWeyl).pow 2).integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hbi := ((continuous_normalizedBlockNorm.comp o.continuousWeyl).pow 2).integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  change Integrable (fun e : FrameBundle g =>
    normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2) μ at hvi
  change Integrable (fun e : FrameBundle g =>
    normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2) μ at hbi
  rw [integral_add hpi hmi, integral_add hvi hbi]
  linarith

end MetricGreenData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual second derivatives of the energy of a straight chart variation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The second derivative for an arbitrary two-jet of the position and
velocity. The hypotheses are ordinary parameter derivatives of these data. -/
theorem actual_metricEnergy_secondJet (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (y v w : ℝ → JacobiCoordinateVector)
    (u q : JacobiCoordinateVector) (hz : x 0 ∈ (chartAt FourSpace c).target)
    (hx : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt x (WithLp.toLp 2 (y s)) s)
    (hy : HasDerivAt y u 0)
    (hv : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt v (w s) s) (hw : HasDerivAt w q 0) :
    HasDerivAt (deriv (fun s : ℝ => (1 / 2 : ℝ) *
      jacobiMetricPair (metricInChart g c (x s)) (v s) (v s)))
      (coordinateEnergySecondDensity (metricInChart g c (x 0))
        (jacobiMetricFirstDirectional g c (x 0) (y 0))
        (jacobiMetricSecondDirectional g c (x 0) (y 0)) (v 0) (w 0) +
        (1 / 2 : ℝ) * jacobiMetricPair (jacobiMetricFirstDirectional g c (x 0) u) (v 0) (v 0) +
        jacobiMetricPair (metricInChart g c (x 0)) (v 0) q) 0 := by
  let G : ℝ → Mat4 := fun s => metricInChart g c (x s)
  let H : ℝ → Mat4 := fun s => jacobiMetricFirstDirectional g c (x s) (y s)
  let K := jacobiMetricSecondDirectional g c (x 0) (y 0) +
    jacobiMetricFirstDirectional g c (x 0) u
  have hx0 := hx.self_of_nhds
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), x s ∈ (chartAt FourSpace c).target :=
    hx0.continuousAt.eventually ((chartAt FourSpace c).open_target.mem_nhds hz)
  have hG : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i j, HasDerivAt (fun r => G r i j) (H s i j) s := by
    filter_upwards [hx, hnear] with s hxs hs i j
    have hd := hasDerivAt_coordinate_comp hxs
      ((metricInChart_contDiffAt g c (x s) hs i j).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    simpa only [G, H, jacobiMetricFirstDirectional, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, matrixPartial] using hd
  have hH (i j : Fin 4) : HasDerivAt (fun r => H r i j) (K i j) 0 := by
    have hp (k : Fin 4) : ContDiffAt ℝ ∞
        (fun z => matrixPartial (metricInChart g c) k z i j) (x 0) :=
      ((metricInChart_contDiffAt g c (x 0) hz i j).fderiv_right (m := ∞)
        (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffAt_const
    have hd (k : Fin 4) : HasDerivAt
        (fun r => matrixPartial (metricInChart g c) k (x r) i j)
        (∑ l, y 0 l * matrixPartial (matrixPartial (metricInChart g c) k) l (x 0) i j) 0 := by
      simpa only [matrixPartial] using
        hasDerivAt_coordinate_comp hx0 ((hp k).differentiableAt (by simp))
    have hs := HasDerivAt.fun_sum (fun k (_ : k ∈ Finset.univ) =>
      (hasDerivAt_pi.mp hy k).mul (hd k))
    have hsum : (∑ k, (u k * matrixPartial (metricInChart g c) k (x 0) i j +
        y 0 k * (∑ l, y 0 l * matrixPartial (matrixPartial (metricInChart g c) k) l (x 0) i j))) =
        K i j := by
      simp only [K, Matrix.add_apply, jacobiMetricFirstDirectional, jacobiMetricSecondDirectional,
        Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
      rw [add_comm]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsum] at hs
    simpa only [H, jacobiMetricFirstDirectional, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Pi.mul_apply] using hs
  have hGsym : (G 0).IsSymm := by
    ext i j
    exact metricInChart_comm g c (x 0) j i
  have hHsym : (H 0).IsSymm := by
    change (jacobiMetricFirstDirectional g c (x 0) (y 0)).IsSymm
    rw [jacobiMetricFirstDirectional_eq g c (x 0) hz]
    exact jacobiMetricRate_symm hGsym _
  have h := matrixEnergy_secondJet G H K v w q hG hH hv hw hGsym hHsym
  have heq : coordinateEnergySecondDensity (G 0) (H 0) K (v 0) (w 0) =
      coordinateEnergySecondDensity (G 0) (H 0)
        (jacobiMetricSecondDirectional g c (x 0) (y 0)) (v 0) (w 0) +
        (1 / 2 : ℝ) * jacobiMetricPair (jacobiMetricFirstDirectional g c (x 0) u) (v 0) (v 0) := by
    simp only [coordinateEnergySecondDensity, K, jacobiMetricPair_matrix_add]
    ring
  rw [heq] at h
  exact h

/-- The second-jet correction is itself a boundary derivative along a
geodesic; together with the straight term its boundary is the covariant
parameter acceleration. -/
theorem actual_metricEnergy_jetBoundary_hasDerivAt (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (v u : ℝ → JacobiCoordinateVector)
    (a q : JacobiCoordinateVector) (t : ℝ)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x (WithLp.toLp 2 (v t)) t)
    (hv : HasDerivAt v a t) (hu : HasDerivAt u q t)
    (ha : a = -(jacobiConnection (fun i => connectionMatrix g c i (x t)) (v t) *ᵥ v t)) :
    HasDerivAt (fun s => jacobiMetricPair (metricInChart g c (x s)) (v s) (u s))
      ((1 / 2 : ℝ) * jacobiMetricPair (jacobiMetricFirstDirectional g c (x t) (u t))
        (v t) (v t) + jacobiMetricPair (metricInChart g c (x t)) (v t) q) t := by
  let G : ℝ → Mat4 := fun s => metricInChart g c (x s)
  let A := jacobiConnection (fun i => connectionMatrix g c i (x t)) (v t)
  let B := jacobiConnection (fun i => connectionMatrix g c i (x t)) (u t)
  have hG (i j : Fin 4) : HasDerivAt (fun s => G s i j)
      (jacobiMetricRate (G t) A i j) t := by
    rw [← jacobiMetricFirstDirectional_eq g c (x t) hz (v t)]
    have hd := hasDerivAt_coordinate_comp hx
      ((metricInChart_contDiffAt g c (x t) hz i j).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    simpa only [G, jacobiMetricFirstDirectional, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, matrixPartial] using hd
  have h := energyPair_hasDerivAt G (jacobiMetricRate (G t) A) v u a q t hG hv hu
  have hsym : (G t).IsSymm := by
    ext i j
    exact metricInChart_comm g c (x t) j i
  have hcomm : A *ᵥ u t = B *ᵥ v t :=
    actual_jacobiConnection_comm g c (x t) (v t) (u t)
  have heq : jacobiMetricPair (jacobiMetricRate (G t) A) (v t) (u t) +
      jacobiMetricPair (G t) a (u t) + jacobiMetricPair (G t) (v t) q =
      (1 / 2 : ℝ) * jacobiMetricPair (jacobiMetricFirstDirectional g c (x t) (u t))
        (v t) (v t) + jacobiMetricPair (G t) (v t) q := by
    change a = -(A *ᵥ v t) at ha
    rw [jacobiMetricFirstDirectional_eq g c (x t) hz,
      jacobiMetricRate_pair, ha, jacobiMetricPair_neg_left,
      jacobiMetricRate_pair, jacobiMetricPair_symm hsym (B *ᵥ v t) (v t), hcomm]
    ring
  rw [heq] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The kinetic flow at zero momentum. Its stationary solution and
linearization provide the local inverse-function input for exponential
coordinates at the zero tangent vector. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The differential sends a momentum perturbation to its raised velocity;
the position perturbation has zero rate at zero momentum. -/
def kineticZeroDifferential (g : SmoothMetric M) (c : M) (x : FourSpace) :
    CotangentCoordinates →L[ℝ] CotangentCoordinates :=
  (((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) ((metricInChart g c x)⁻¹)).comp
    (ContinuousLinearMap.snd ℝ FourSpace FourSpace)).prod 0


end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual intrinsic covariant-derivative pairing of smooth two-forms.
The factor one-half removes the duplicated skew-tensor entries. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

local instance twoFormEnergy_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six-coordinate matrix and symmetry of the curvature action. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoForm_curvature_row (R : CovariantCoordinates 4)
    (hR : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l])
    (a : TwoFormFour) (i j : Fin 4) :
    (∑ k, ∑ l, R ![i,j,k,l] * twoFormMatrix a k l) =
      2 * ∑ b : Fin 6, R ![i,j,(AlgebraicCurvature.pair b).1,
        (AlgebraicCurvature.pair b).2] * a b := by
  have h10 := hR i j 0 1
  have h20 := hR i j 0 2
  have h30 := hR i j 0 3
  have h21 := hR i j 1 2
  have h31 := hR i j 1 3
  have h32 := hR i j 2 3
  simp [Fin.sum_univ_succ, twoFormMatrix, AlgebraicCurvature.pair,
    h10, h20, h30, h21, h31, h32]
  ring

theorem twoFormCurvatureAction_component (R : CovariantCoordinates 4)
    (hR : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l])
    (a : TwoFormFour) (i : Fin 6) :
    twoFormCurvatureAction R a i = -∑ j : Fin 6,
      R ![(AlgebraicCurvature.pair i).1, (AlgebraicCurvature.pair i).2,
        (AlgebraicCurvature.pair j).1, (AlgebraicCurvature.pair j).2] * a j := by
  change (-1 / 2 : ℝ) * twoFormExtract _ i = _
  rw [twoFormExtract_apply]
  change (-1 / 2 : ℝ) * (∑ k, ∑ l,
    R ![(AlgebraicCurvature.pair i).1, (AlgebraicCurvature.pair i).2,k,l] *
      twoFormMatrix a k l) = _
  rw [twoForm_curvature_row R hR]
  ring

theorem twoFormCurvatureAction_symmetric (R : CovariantCoordinates 4)
    (hR : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l])
    (hpair : ∀ i j k l, R ![k,l,i,j] = R ![i,j,k,l]) (a b : TwoFormFour) :
    inner ℝ (twoFormCurvatureAction R a) b = inner ℝ a (twoFormCurvatureAction R b) := by
  change (∑ i, b i * twoFormCurvatureAction R a i) =
    ∑ i, twoFormCurvatureAction R b i * a i
  simp only [twoFormCurvatureAction_component R hR, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hpair]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual six-dimensional Weitzenböck potential and its first two
matrix traces. These are local algebraic identities, not an index formula. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormPotentialMatrix_trace (R : CovariantCoordinates 4) :
    (twoFormPotentialMatrix R).trace = 36 - 2 * (twoFormCurvatureMatrix R).trace := by
  norm_num [twoFormPotentialMatrix, Matrix.trace_sub, Matrix.trace_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature tensor norm is four times the square norm of
its matrix on the six increasing index pairs. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem skew_square_sum (Q : Mat4) (hQ : Qᵀ = -Q) :
    (∑ i, ∑ j, Q i j ^ 2) =
      2 * ∑ a : Fin 6, Q (AlgebraicCurvature.pair a).1 (AlgebraicCurvature.pair a).2 ^ 2 := by
  have hs (i j : Fin 4) : Q j i = -Q i j := congrArg (fun A : Mat4 => A i j) hQ
  have hd (i : Fin 4) : Q i i = 0 := by have h := hs i i; linarith only [h]
  simp [Fin.sum_univ_succ, AlgebraicCurvature.pair, hd,
    hs 0 1, hs 0 2, hs 0 3, hs 1 2, hs 1 3, hs 2 3]
  ring

theorem twoFormCurvatureMatrix_tensorNorm (R : CovariantCoordinates 4)
    (hf : ∀ i j k l, R ![j,i,k,l] = -R ![i,j,k,l])
    (hl : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l]) :
    frameTensorSquareNorm R = 4 * ∑ a, ∑ b, twoFormCurvatureMatrix R a b ^ 2 := by
  have hlast (i j : Fin 4) :
      (∑ k, ∑ l, R ![i,j,k,l] ^ 2) =
        2 * ∑ b : Fin 6, R ![i,j,(AlgebraicCurvature.pair b).1,
          (AlgebraicCurvature.pair b).2] ^ 2 := by
    apply skew_square_sum
    ext k l
    exact hl i j k l
  have hfirst (b : Fin 6) :
      (∑ i, ∑ j, R ![i,j,(AlgebraicCurvature.pair b).1,
          (AlgebraicCurvature.pair b).2] ^ 2) =
        2 * ∑ a : Fin 6, R ![(AlgebraicCurvature.pair a).1,
          (AlgebraicCurvature.pair a).2,(AlgebraicCurvature.pair b).1,
          (AlgebraicCurvature.pair b).2] ^ 2 := by
    apply skew_square_sum
    ext i j
    exact hf i j _ _
  rw [frameTensorSquareNorm, frameTensorPairing, sum_four_components]
  simp only [← pow_two, hlast, ← Finset.mul_sum]
  have hswap :
      (∑ i, ∑ j, ∑ b : Fin 6, R ![i,j,(AlgebraicCurvature.pair b).1,
          (AlgebraicCurvature.pair b).2] ^ 2) =
        ∑ b : Fin 6, ∑ i, ∑ j, R ![i,j,(AlgebraicCurvature.pair b).1,
          (AlgebraicCurvature.pair b).2] ^ 2 := by
    calc
      _ = ∑ i, ∑ b : Fin 6, ∑ j, R ![i,j,(AlgebraicCurvature.pair b).1,
          (AlgebraicCurvature.pair b).2] ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hswap]
  simp only [hfirst, ← Finset.mul_sum, twoFormCurvatureMatrix, neg_sq]
  rw [Finset.sum_comm]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A C² coordinate conjugacy transports the first variational equation.
Only the coordinate map is differentiated twice; a C² flow is not assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

theorem variational_equation_of_intertwining
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : E → F) (X : E → E) (Y : F → F) (γ Z : ℝ → E) (t : ℝ)
    (hQ : ContDiffAt ℝ 2 Q (γ t))
    (hX : DifferentiableAt ℝ X (γ t))
    (hY : DifferentiableAt ℝ Y (Q (γ t)))
    (hintertwine : (fun p => fderiv ℝ Q p (X p)) =ᶠ[𝓝 (γ t)] fun p => Y (Q p))
    (hγ : HasDerivAt γ (X (γ t)) t)
    (hZ : HasDerivAt Z (fderiv ℝ X (γ t) (Z t)) t) :
    HasDerivAt (fun s => fderiv ℝ Q (γ s) (Z s))
      (fderiv ℝ Y (Q (γ t)) (fderiv ℝ Q (γ t) (Z t))) t := by
  have hQd : DifferentiableAt ℝ Q (γ t) := hQ.differentiableAt (by norm_num)
  have hDQd : DifferentiableAt ℝ (fderiv ℝ Q) (γ t) :=
    (hQ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hleft := hDQd.hasFDerivAt.clm_apply hX.hasFDerivAt
  have hright := hY.hasFDerivAt.comp (γ t) hQd.hasFDerivAt
  have heq := (hleft.congr_of_eventuallyEq hintertwine.symm).unique hright
  have hvalue := congrArg (fun L : E →L[ℝ] F => L (Z t)) heq
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at hvalue
  have hsym := (hQ.isSymmSndFDerivAt (by norm_num)).eq (X (γ t)) (Z t)
  have hrate : fderiv ℝ (fderiv ℝ Q) (γ t) (X (γ t)) (Z t) +
      fderiv ℝ Q (γ t) (fderiv ℝ X (γ t) (Z t)) =
      fderiv ℝ Y (Q (γ t)) (fderiv ℝ Q (γ t) (Z t)) := by
    rw [hsym, add_comm]
    exact hvalue
  have hd := (hDQd.hasFDerivAt.comp_hasDerivAt t hγ).clm_apply hZ
  simp only [Function.comp_def] at hd
  rwa [hrate] at hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compactly supported chart tensor, transported into the centered
tangent coordinates and then into any other chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

theorem frameTensor_zero_two (E : Mat4) :
    frameTensor E (0 : CovariantCoordinates 2) = 0 := by
  funext a
  simp [frameTensor]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Levi-Civita commutator on a smooth two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem tensorSlotAction_two (A : Mat4) (T : CovariantCoordinates 2) (k l : Fin 4) :
    tensorSlotAction A T ![k,l] =
      (∑ p, A p k * T ![p,l]) + ∑ p, A p l * T ![k,p] := by
  have h0 (p : Fin 4) : Function.update ![k,l] 0 p = ![p,l] := by
    ext i
    fin_cases i <;> simp
  have h1 (p : Fin 4) : Function.update ![k,l] 1 p = ![k,p] := by
    ext i
    fin_cases i <;> simp
  simp only [tensorSlotAction, Fin.sum_univ_two, covariantSlotAction, h0, h1,
    Matrix.cons_val_zero, Matrix.cons_val_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contraction of the two derivative slots, in arbitrary coordinates
and in actual orthonormal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem twoFormSecondTrace_orthogonal (P : Mat4) (hP : P * Pᵀ = 1)
    (T : CovariantCoordinates 4) :
    (fun v => ∑ i, frameTensor P T (Fin.cons i (Fin.cons i v))) =
      frameTensor P (fun v => ∑ i, T (Fin.cons i (Fin.cons i v))) := by
  funext v
  rw [twoFormSecondTrace_frame, hP]
  congr 1
  funext w
  simp [twoFormSecondTrace, Matrix.one_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Polarization of the exact tensor/pair-matrix norm identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormCurvatureMatrix_tensorPairing (R S : CovariantCoordinates 4)
    (hfR : ∀ i j k l, R ![j,i,k,l] = -R ![i,j,k,l])
    (hlR : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l])
    (hfS : ∀ i j k l, S ![j,i,k,l] = -S ![i,j,k,l])
    (hlS : ∀ i j k l, S ![i,j,l,k] = -S ![i,j,k,l]) :
    frameTensorPairing R S =
      4 * ∑ i, ∑ j, twoFormCurvatureMatrix R i j * twoFormCurvatureMatrix S i j := by
  have hf (i j k l : Fin 4) : (R + S) ![j,i,k,l] = -(R + S) ![i,j,k,l] := by
    change R ![j,i,k,l] + S ![j,i,k,l] = -(R ![i,j,k,l] + S ![i,j,k,l])
    rw [hfR i j k l, hfS i j k l, neg_add]
  have hl (i j k l : Fin 4) : (R + S) ![i,j,l,k] = -(R + S) ![i,j,k,l] := by
    change R ![i,j,l,k] + S ![i,j,l,k] = -(R ![i,j,k,l] + S ![i,j,k,l])
    rw [hlR i j k l, hlS i j k l, neg_add]
  have hp : frameTensorSquareNorm (R + S) = frameTensorSquareNorm R +
      2 * frameTensorPairing R S + frameTensorSquareNorm S := by
    unfold frameTensorSquareNorm frameTensorPairing
    simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
    simp only [mul_comm (S _) (R _)]
    ring
  let Q (K : TwoFormMatrix) := ∑ i, ∑ j, K i j ^ 2
  have hQ (K L : TwoFormMatrix) : Q (K + L) = Q K +
      2 * (∑ i, ∑ j, K i j * L i j) + Q L := by
    simp only [Q, Matrix.add_apply, add_sq, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum]
  have hC : twoFormCurvatureMatrix (R + S) = twoFormCurvatureMatrix R + twoFormCurvatureMatrix S := by
    ext i j
    exact neg_add _ _
  have hn := twoFormCurvatureMatrix_tensorNorm (R + S) hf hl
  change frameTensorSquareNorm (R + S) = 4 * Q (twoFormCurvatureMatrix (R + S)) at hn
  rw [hp, hC, hQ] at hn
  have hR := twoFormCurvatureMatrix_tensorNorm R hfR hlR
  have hS := twoFormCurvatureMatrix_tensorNorm S hfS hlS
  change frameTensorSquareNorm R = 4 * Q (twoFormCurvatureMatrix R) at hR
  change frameTensorSquareNorm S = 4 * Q (twoFormCurvatureMatrix S) at hS
  linarith only [hn, hR, hS]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite determinant conversion from radial/normal Jacobi components
to the metric volume density of a coordinate differential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem jacobiBlockMatrix_mulVec (a : ℝ) (J : Matrix (Fin 3) (Fin 3) ℝ)
    (v : Fin 4 → ℝ) :
    jacobiBlockMatrix a J *ᵥ v =
      Fin.cons (a * v 0) (J *ᵥ fun i => v i.succ) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, jacobiBlockMatrix]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, jacobiBlockMatrix]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A chart variation with exact prescribed endpoint curves.  The affine
correction preserves the desired position field and mixed derivative at zero,
while supplying the second jets required for chart boundary cancellation. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter
open scoped _root_.Topology

noncomputable section

section Vector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem endpointCorrectedPosition_zero (x y A B : ℝ → E) (a b t : ℝ)
    (hA : A 0 = x a) (hB : B 0 = x b) :
    endpointCorrectedPosition x y A B a b 0 t = x t := by
  simp [endpointCorrectedPosition, endpointResidual, hA, hB]

theorem endpointCorrectedParameter_zero (y A' B' : ℝ → E) (a b t : ℝ)
    (hA : A' 0 = y a) (hB : B' 0 = y b) :
    endpointCorrectedParameter y A' B' a b 0 t = y t := by
  simp [endpointCorrectedParameter, hA, hB]

theorem endpointCorrectedSecond_left (A'' B'' : ℝ → E)
    (a b ε : ℝ) (hab : a ≠ b) :
    endpointCorrectedSecond A'' B'' a b ε a = A'' ε := by
  simp [endpointCorrectedSecond, endpointWeightLeft, endpointWeightRight,
    sub_ne_zero.mpr hab.symm]

theorem endpointCorrectedSecond_right (A'' B'' : ℝ → E)
    (a b ε : ℝ) (hab : a ≠ b) :
    endpointCorrectedSecond A'' B'' a b ε b = B'' ε := by
  simp [endpointCorrectedSecond, endpointWeightLeft, endpointWeightRight,
    sub_ne_zero.mpr hab.symm]

theorem endpointCorrectedVelocity_zero (x y v w A B : ℝ → E) (a b t : ℝ)
    (hA : A 0 = x a) (hB : B 0 = x b) :
    endpointCorrectedVelocity x y v w A B a b 0 t = v t := by
  simp [endpointCorrectedVelocity, endpointResidual, hA, hB]

theorem endpointCorrectedMixed_zero (y w A' B' : ℝ → E) (a b t : ℝ)
    (hA : A' 0 = y a) (hB : B' 0 = y b) :
    endpointCorrectedMixed y w A' B' a b 0 t = w t := by
  simp [endpointCorrectedMixed, hA, hB]

/-- One parameter interval works for the entire compact segment. -/
theorem endpointCorrectedPosition_inside (x y A B : ℝ → E) (a b : ℝ)
    (hx : Continuous x) (hy : Continuous y) (hA : Continuous A) (hB : Continuous B)
    (hA0 : A 0 = x a) (hB0 : B 0 = x b) (U : Set E) (hU : IsOpen U)
    (hxU : ∀ t ∈ Icc a b, x t ∈ U) :
    ∃ δ > 0, ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      endpointCorrectedPosition x y A B a b ε t ∈ U := by
  have hP := continuous_endpointCorrectedPosition x y A B a b hx hy hA hB
  have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ t ∈ Icc a b,
      endpointCorrectedPosition x y A B a b ε t ∈ U := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    apply hP.continuousAt.eventually
    apply hU.mem_nhds
    change endpointCorrectedPosition x y A B a b 0 t ∈ U
    rw [endpointCorrectedPosition_zero x y A B a b t hA0 hB0]
    exact hxU t ht
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro ε hε t ht
  apply hball ?_ t ht
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  rw [abs_lt]
  constructor <;> linarith [hε.1, hε.2]

end Vector
end
end PositiveEinsteinFour.Geometry
end


section

/-! In Ric = 3g the local graded traces of the Weitzenböck potential
have vanishing degree-zero/degree-one terms and the required curvature norm
in degree two. No heat-kernel or characteristic-number assertion is made. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem symmetric_zero_diagonal_sum (S : Mat4)
    (hs : ∀ i j, S j i = S i j) (hd : ∀ i, S i i = 0) :
    (∑ i, ∑ j, S i j) =
      2 * ∑ a : Fin 6, S (AlgebraicCurvature.pair a).1 (AlgebraicCurvature.pair a).2 := by
  simp [Fin.sum_univ_succ, AlgebraicCurvature.pair, hd,
    hs 0 1, hs 0 2, hs 0 3, hs 1 2, hs 1 3, hs 2 3]
  ring

theorem twoFormCurvatureMatrix_trace_contraction (R : CovariantCoordinates 4)
    (hf : ∀ i j k l, R ![j,i,k,l] = -R ![i,j,k,l])
    (hl : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l]) :
    2 * (twoFormCurvatureMatrix R).trace = ∑ i, ∑ j, R ![i,j,j,i] := by
  let S : Mat4 := fun i j => R ![i,j,j,i]
  have hs (i j : Fin 4) : S j i = S i j :=
    (hf i j i j).trans (hl i j i j).symm
  have hd (i : Fin 4) : S i i = 0 := by
    have h := hf i i i i
    dsimp only [S]
    linarith only [h]
  have hsum := symmetric_zero_diagonal_sum S hs hd
  have ht : (twoFormCurvatureMatrix R).trace =
      ∑ a : Fin 6, S (AlgebraicCurvature.pair a).1 (AlgebraicCurvature.pair a).2 := by
    apply Finset.sum_congr rfl
    intro a _
    exact (hl _ _ _ _).symm
  rw [ht]
  exact hsum.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compactly supported chart tensor, transported into the centered
tangent coordinates and then into any other chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

theorem frameTensor_zero_one (E : Mat4) :
    frameTensor E (0 : CovariantCoordinates 1) = 0 := by
  funext a
  simp [frameTensor]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual two-form Hodge star as a six-dimensional matrix, and
its action on the first pair of curvature indices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormHodgeMatrix_trace : twoFormHodgeMatrix.trace = 0 := by
  norm_num [twoFormHodgeMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

theorem twoFormCurvatureMatrix_hodgeFirst (R : CovariantCoordinates 4) :
    twoFormCurvatureMatrix (hodgeFirstTensor R) = twoFormHodgeMatrix * twoFormCurvatureMatrix R := by
  ext i j
  fin_cases i <;>
    simp [twoFormCurvatureMatrix, hodgeFirstTensor, hodgeStarFour, twoFormHodgeMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ, AlgebraicCurvature.pair]

theorem hodgeFirstTensor_firstSkew (R : CovariantCoordinates 4) (i j k l : Fin 4) :
    hodgeFirstTensor R ![j,i,k,l] = -hodgeFirstTensor R ![i,j,k,l] := by
  fin_cases i <;> fin_cases j <;> simp [hodgeFirstTensor, hodgeStarFour]

theorem hodgeFirstTensor_lastSkew (R : CovariantCoordinates 4)
    (hl : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l]) (i j k l : Fin 4) :
    hodgeFirstTensor R ![i,j,l,k] = -hodgeFirstTensor R ![i,j,k,l] := by
  have h01 := hl 0 1 k l
  have h02 := hl 0 2 k l
  have h03 := hl 0 3 k l
  have h12 := hl 1 2 k l
  have h13 := hl 1 3 k l
  have h23 := hl 2 3 k l
  fin_cases i <;> fin_cases j <;>
    simp [hodgeFirstTensor, hodgeStarFour, h01, h02, h03, h12, h13, h23]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Hodge-signed quadratic curvature trace is the actual signed
curvature contraction entering the signature density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem twoFormCurvatureMatrix_signed_trace (R : CovariantCoordinates 4)
    (hf : ∀ i j k l, R ![j,i,k,l] = -R ![i,j,k,l])
    (hp : ∀ i j k l, R ![k,l,i,j] = R ![i,j,k,l])
    (hb : ∀ i j k l, R ![i,j,k,l] + R ![j,k,i,l] + R ![k,i,j,l] = 0) :
    (twoFormHodgeMatrix * twoFormCurvatureMatrix R).trace = 0 := by
  have h := hb 0 1 2 3
  rw [hf 0 2 1 3, hp 0 3 1 2] at h
  norm_num [twoFormHodgeMatrix, twoFormCurvatureMatrix, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_succ, AlgebraicCurvature.pair]
  rw [hp 0 1 2 3, hp 0 2 1 3, hp 0 3 1 2]
  linarith only [h]

theorem twoFormCurvatureMatrix_signed_square_trace (R : CovariantCoordinates 4)
    (hf : ∀ i j k l, R ![j,i,k,l] = -R ![i,j,k,l])
    (hl : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l])
    (hp : ∀ i j k l, R ![k,l,i,j] = R ![i,j,k,l]) :
    4 * (twoFormHodgeMatrix * twoFormCurvatureMatrix R * twoFormCurvatureMatrix R).trace =
      frameTensorPairing R (hodgeFirstTensor R) := by
  have hs := twoFormCurvatureMatrix_symmetric R hp
  have ht := twoFormCurvatureMatrix_tensorPairing R (hodgeFirstTensor R) hf hl
    (hodgeFirstTensor_firstSkew R) (hodgeFirstTensor_lastSkew R hl)
  rw [twoFormCurvatureMatrix_hodgeFirst] at ht
  rw [ht]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij : twoFormCurvatureMatrix R j i = twoFormCurvatureMatrix R i j :=
    congrArg (fun A : TwoFormMatrix => A i j) hs
  rw [hij]
  ring

theorem twoFormPotentialMatrix_signed_square_trace (R : CovariantCoordinates 4) :
    (twoFormHodgeMatrix * twoFormPotentialMatrix R * twoFormPotentialMatrix R).trace =
      -24 * (twoFormHodgeMatrix * twoFormCurvatureMatrix R).trace +
        4 * (twoFormHodgeMatrix * twoFormCurvatureMatrix R * twoFormCurvatureMatrix R).trace := by
  simp only [twoFormPotentialMatrix, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, twoFormHodgeMatrix_trace]
  ring

theorem twoFormPotentialMatrix_signed_square (R : CovariantCoordinates 4)
    (hf : ∀ i j k l, R ![j,i,k,l] = -R ![i,j,k,l])
    (hl : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l])
    (hp : ∀ i j k l, R ![k,l,i,j] = R ![i,j,k,l])
    (hb : ∀ i j k l, R ![i,j,k,l] + R ![j,k,i,l] + R ![k,i,j,l] = 0) :
    (twoFormHodgeMatrix * twoFormPotentialMatrix R * twoFormPotentialMatrix R).trace =
      frameTensorPairing R (hodgeFirstTensor R) := by
  rw [twoFormPotentialMatrix_signed_square_trace, twoFormCurvatureMatrix_signed_trace R hf hp hb,
    mul_zero, zero_add, twoFormCurvatureMatrix_signed_square_trace R hf hl hp]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The finite signed Gram expansion of the four transport amplitudes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

theorem heatSignedGram_polynomial (U t : ℝ) (A B C : HeatMat6) :
    heatSignedGram (U • 1 + t • A + t ^ 2 • B + t ^ 3 • C)
      (U • 1 + t • A + t ^ 2 • B + t ^ 3 • C) =
    2 * t * (U * (twoFormHodgeMatrix * A).trace) + t ^ 2 *
      (2 * U * (twoFormHodgeMatrix * B).trace + heatSignedGram A A +
        t * (2 * U * (twoFormHodgeMatrix * C).trace + 2 * heatSignedGram A B) +
        t ^ 2 * (2 * heatSignedGram A C + heatSignedGram B B) +
        t ^ 3 * (2 * heatSignedGram B C) + t ^ 4 * heatSignedGram C C) := by
  simp only [heatSignedGram_add_left, heatSignedGram_add_right,
    heatSignedGram_smul_left, heatSignedGram_smul_right]
  rw [heatSignedGram_comm A 1, heatSignedGram_comm B 1, heatSignedGram_comm C 1,
    heatSignedGram_comm B A, heatSignedGram_comm C A, heatSignedGram_comm C B]
  simp only [heatSignedGram_one_left, Matrix.mul_one,
    twoFormHodgeMatrix_trace]
  ring

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HeatKernels10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The two coefficients that survive the signed Gaussian limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatSignedGram_scalar_sub (a : ℝ) (V : HeatMat6)
    (hV : Vᵀ = V) (htrace : (twoFormHodgeMatrix * V).trace = 0) :
    heatSignedGram (a • 1 - V) (a • 1 - V) = (twoFormHodgeMatrix * V * V).trace := by
  unfold heatSignedGram
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hV]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
    twoFormHodgeMatrix_trace, htrace, mul_zero, sub_zero, zero_sub, neg_neg]
  exact congrArg Matrix.trace (Matrix.mul_assoc twoFormHodgeMatrix V V).symm

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


