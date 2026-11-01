-- Prove2me | Definitions.Def_OAIQ091C022
-- name    : OAIQ091C022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:07:24.196816+00:00
-- url     : https://prove2.me/theorems/5ab4106d-356e-4777-88b2-393653eaeeab
-- title:
--   Definitions bundle OAIQ091C022 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 419 declarations of OpenAI's Lean: 58 definitions, 1 inductive type or structure, 1 instance and 359 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.ZeroFormDeRhamCohomology`, `OAI.PositiveEinsteinFour.Geometry.actualBallRadialMass`, `OAI.PositiveEinsteinFour.Geometry.actualComplexProjectiveMap`, `OAI.PositiveEinsteinFour.Geometry.actualComplexProjectiveSection`, `OAI.PositiveEinsteinFour.Geometry.actualFlatKernelDeterminant`, `OAI.PositiveEinsteinFour.Geometry.actualJacobiMatrix`, `OAI.PositiveEinsteinFour.Geometry.actualRadialMass`, `OAI.PositiveEinsteinFour.Geometry.chartGramBlock`, `OAI.PositiveEinsteinFour.Geometry.complexAffineLog`, `OAI.PositiveEinsteinFour.Geometry.complexCircleMatrix`, `OAI.PositiveEinsteinFour.Geometry.complexCircleVector`, `OAI.PositiveEinsteinFour.Geometry.complexCompanion`, `OAI.PositiveEinsteinFour.Geometry.complexCutChartDomain`, `OAI.PositiveEinsteinFour.Geometry.complexCutChartMap`, `OAI.PositiveEinsteinFour.Geometry.complexNormalLift`, `OAI.PositiveEinsteinFour.Geometry.complexNormalPoint`, `OAI.PositiveEinsteinFour.Geometry.complexParametrizedCone`, `OAI.PositiveEinsteinFour.Geometry.complexPolarLiftDifferential`, `OAI.PositiveEinsteinFour.Geometry.complexPolarProjection`, `OAI.PositiveEinsteinFour.Geometry.complexProjectiveInterior`, `OAI.PositiveEinsteinFour.Geometry.complexProjectiveMetric`, `OAI.PositiveEinsteinFour.Geometry.complexProjectiveNorth`, `OAI.PositiveEinsteinFour.Geometry.complexProjectivePolarData`, `OAI.PositiveEinsteinFour.Geometry.exponentialBallAreaMeasure`, `OAI.PositiveEinsteinFour.Geometry.frameOrientation_of_clopen_sheet`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyBaseAugment`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyHessianDualNormedGroup`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyHessianDualNormedSpace`, `OAI.PositiveEinsteinFour.Geometry.heatFamilySliceChart`, `OAI.PositiveEinsteinFour.Geometry.heatFamilySpatialFDeriv`, `OAI.PositiveEinsteinFour.Geometry.orientationCoverFrameOrientation`, `OAI.PositiveEinsteinFour.Geometry.regularizedPlusWeylScalar`, `OAI.PositiveEinsteinFour.Geometry.rescaleFrameOrientation`, `OAI.PositiveEinsteinFour.Geometry.roundAntipodalPoint`, `OAI.PositiveEinsteinFour.Geometry.roundBoundaryEndpoint`, `OAI.PositiveEinsteinFour.Geometry.roundBoundaryProjection`, `OAI.PositiveEinsteinFour.Geometry.roundLog`, `OAI.PositiveEinsteinFour.Geometry.roundSphereExponential`, `OAI.PositiveEinsteinFour.Geometry.roundSphereMap`, `OAI.PositiveEinsteinFour.Geometry.roundTail` and 19 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `EinsteinFour_CurvatureTensors02`, `EinsteinFour_FrameAverages`, `EinsteinFour_GeodesicGeometry04`, `EinsteinFour_GeodesicGeometry05`, `EinsteinFour_GeodesicGeometry11`, `EinsteinFour_GeodesicGeometry12`, `EinsteinFour_GeodesicGeometry13`, `EinsteinFour_HeatKernels10`, `EinsteinFour_HodgeTheory08`, `EinsteinFour_HodgeTheory09`, `EinsteinFour_HodgeTheory11`, `EinsteinFour_ScalarRegularity06`, `EinsteinFour_ScalarRegularity07`, `EinsteinFour_WeylEstimates03`, `EinsteinFour_WeylEstimates06`, `EinsteinFour_WeylEstimates14`, `EinsteinFour_WeylNormal`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C038` and `OAIQ091C018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C025`, `OAIQ091C026`, `OAIQ091C046`, `OAIQ091C051`, `OAIQ091C052` and `OAIQ091C071`; the proof of `OAI.PositiveEinsteinFour.classification`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C038
import Definitions.Def_OAIQ091C018

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylNormal
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.canonicalFrameMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.canonicalUnitTangentMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.chartCoordinateMeasure_sigmaFinite _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_pseudoMetrizable _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothH1TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothL2TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instNonemptyOrthonormalFrame _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarAngularProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarDirectionProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite _root_.OAI.PositiveEinsteinFour.Geometry.tangentBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.unitTangentBundle_secondCountable
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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat3
theorem normalCurvatureDeviation_mean_square
    (h : FollandMoments) (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (hdecomp : frameCurvature g c e =
      einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e))
    (hT : (plusWeyl g c e).trace = 0) (hU : (minusWeyl g c e).trace = 0) :
    (∫ q, squareNorm (normalCurvatureDeviation g c e q) ∂sphereMeasure) =
      (3 / 2) * (normalizedBlockNorm (plusWeyl g c e) ^ 2 +
        normalizedBlockNorm (minusWeyl g c e) ^ 2) := by
  simp_rw [normalCurvatureDeviation_eq_of_decomposition g c e hdecomp]
  exact integral_squareNorm_normalDeviation_normalized h _ _ hT hU

theorem normalCurvatureDeviation_mean_frobenius
    (h : FollandMoments) (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (hdecomp : frameCurvature g c e =
      einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e))
    (hT : (plusWeyl g c e).trace = 0) (hU : (minusWeyl g c e).trace = 0) :
    (∫ q, ‖normalCurvatureDeviation g c e q‖ ^ 2 ∂sphereMeasure) =
      (3 / 2) * (normalizedBlockNorm (plusWeyl g c e) ^ 2 +
        normalizedBlockNorm (minusWeyl g c e) ^ 2) := by
  simpa only [squareNorm_eq_frobenius_norm_sq] using
    normalCurvatureDeviation_mean_square h g c e hdecomp hT hU

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameAverages
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.canonicalFrameMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.canonicalUnitTangentMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.chartCoordinateMeasure_sigmaFinite _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_pseudoMetrizable _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothH1TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothL2TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarAngularProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarDirectionProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite _root_.OAI.PositiveEinsteinFour.Geometry.tangentBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.unitTangentBundle_secondCountable
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
/-- Derive the time-zero curvature energy from the published disintegration
and the proved frame transformation and angular contraction. -/
theorem frameCurvatureField_mean_square
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)} (hμ : BrinKarcherAveraging g μ)
    (h : FollandMoments) (S : M → ℝ)
    (hCi : Integrable (fun e => ‖frameCurvatureField g e‖ ^ 2) μ)
    (hSi : Integrable S (normalizedVolume g))
    (hInv : DirectionInvariant (fun e => ‖frameCurvatureField g e‖ ^ 2))
    (hdec : ∀ c (e : OrthonormalFrame g c), frameCurvature g c e =
      einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e))
    (htr : ∀ c (e : OrthonormalFrame g c),
      (plusWeyl g c e).trace = 0 ∧ (minusWeyl g c e).trace = 0)
    (hS : ∀ c (e : OrthonormalFrame g c),
      normalizedBlockNorm (plusWeyl g c e) ^ 2 +
        normalizedBlockNorm (minusWeyl g c e) ^ 2 = S c) :
    (∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂μ) =
      (3 / 2) * (∫ c, S c ∂normalizedVolume g) := by
  rw [hμ.fiberFormula _ (fun c => (3 / 2) * S c) hCi (hSi.const_mul _) hInv]
  · exact integral_const_mul _ _
  · intro c e
    simp_rw [frameCurvatureField_turn]
    rw [normalCurvatureDeviation_mean_frobenius h g c e (hdec c e)
      (htr c e).1 (htr c e).2, hS]

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.canonicalFrameMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.canonicalUnitTangentMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.chartCoordinateMeasure_sigmaFinite _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_pseudoMetrizable _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothH1TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothL2TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarAngularProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarDirectionProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.tangentBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.unitTangentBundle_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Actual local orthonormal frames obtained from smooth coordinate vectors
by the explicit four-column normalizer. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The framed coordinate curvature, expressed entirely in one fixed chart. -/
def chartGramBlock (g : SmoothMetric M) (c : M) (S : Mat4)
    (Q : Fin 3 → Mat4) (z : FourSpace) : Mat3 :=
  blockCoordinates (frameTensor (chartGramMatrix g c S z)
    (curvatureCoordinates g c z)) Q - 1


theorem chartGramBlock_eq_frame (g : SmoothMetric M) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) (Q : Fin 3 → Mat4) (z : ChartTarget c) :
    chartGramBlock g c S Q z =
      curvatureBlock (curvaturePairing g ((chartAt FourSpace c).symm z)
        (chartGramFrame g c S hS z)) Q - 1 := by
  have hc := curvatureCoordinates_transition g c ((chartAt FourSpace c).symm z) z z.property
    (mem_chart_source FourSpace ((chartAt FourSpace c).symm z))
  rw [chartTransitionMatrix_to_center c z z.property] at hc
  unfold chartGramBlock
  rw [hc, ← frameTensor_mul]
  congr 1
  ext i j
  simp only [blockCoordinates, curvatureBlock, curvaturePairing]
  apply congrArg ((1 / 8 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [show frameTensor (chartInverseMatrix c z * chartGramMatrix g c S z)
      (curvatureCoordinates g ((chartAt FourSpace c).symm z)
        (chartTransition c ((chartAt FourSpace c).symm z) z))
        ![a.1, a.2, b.2, b.1] =
      frameCurvature g ((chartAt FourSpace c).symm z)
        (chartGramFrame g c S hS z) a.1 a.2 b.2 b.1 from
    frameTensor_curvatureCoordinates (chartGramFrame g c S hS z) a.1 a.2 b.2 b.1]

theorem chartGramBlock_contDiffAt (g : SmoothMetric M) (c : M) (S : Mat4)
    (Q : Fin 3 → Mat4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (i j : Fin 3) : ContDiffAt ℝ ∞ (fun w => chartGramBlock g c S Q w i j) z := by
  let E : FourSpace → Mat4 := chartGramMatrix g c S
  let T : FourSpace → CovariantCoordinates 4 := curvatureCoordinates g c
  have hE : ∀ a b, ContDiffAt ℝ ∞ (fun w => E w a b) z :=
    chartGramMatrix_contDiffAt g c S z hz
  have hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z :=
    curvatureCoordinates_contDiffAt g c z hz (metricInChart_posDef g c z hz).det_pos.ne'
  have hF := frameTensor_contDiffAt hE hT
  have hB := blockCoordinates_contDiffAt hF Q i j
  exact hB.sub contDiffAt_const

theorem chartGramBlock_squareNorm_contDiffAt (g : SmoothMetric M) (c : M) (S : Mat4)
    (Q : Fin 3 → Mat4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (fun w => normalizedBlockNorm (chartGramBlock g c S Q w) ^ 2) z := by
  simp only [normalizedBlockNorm_sq]
  apply ContDiffAt.div_const
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (chartGramBlock_contDiffAt g c S Q z hz i j).pow 2


end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.mem_scalarH1MeanZero _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1SubtractMean_idempotent _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_equiv _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_none _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_some _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradientL2_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradient_subtractMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Smoothness of the individual oriented Weyl squared norms, obtained
from actual local frames and the coordinate curvature formulas. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem oriented_frame_normSquare_smooth (o : FrameOrientation g)
    (Q : Fin 3 → Mat4) (f : M → ℝ)
    (hf : ∀ e ∈ o.positive, f e.base = normalizedBlockNorm
      (curvatureBlock (curvaturePairing g e.base e.frame) Q - 1)) :
    ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun x => f x ^ 2) := by
  intro c
  obtain ⟨S, hS, hpositive⟩ := exists_positive_localGramSection g o c
  let z := chartAt FourSpace c c
  have hz : z ∈ (chartAt FourSpace c).target :=
    (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  have hs : ContDiffAt ℝ ∞ (fun w => normalizedBlockNorm (chartGramBlock g c S Q w) ^ 2) z :=
    chartGramBlock_squareNorm_contDiffAt g c S Q z hz
  have hc : ContMDiffAt I4 𝓘(ℝ, ℝ) ∞
      (fun x => normalizedBlockNorm (chartGramBlock g c S Q (chartAt FourSpace c x)) ^ 2) c :=
    hs.contMDiffAt.comp c (contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas c) (mem_chart_source FourSpace c))
  apply hc.congr_of_eventuallyEq
  filter_upwards [hpositive, (chartAt FourSpace c).open_source.mem_nhds
    (mem_chart_source FourSpace c)] with x hx hsource
  let zx : ChartTarget c := ⟨chartAt FourSpace c x, (chartAt FourSpace c).map_source hsource⟩
  have hp : chartGramSection g c S hS zx ∈ o.positive := by
    simpa only [localGramSection, dite_eq_left hsource] using hx
  have hval : f x = normalizedBlockNorm (chartGramBlock g c S Q (chartAt FourSpace c x)) := by
    calc
      f x = f ((chartAt FourSpace c).symm zx) :=
        congrArg f ((chartAt FourSpace c).left_inv hsource).symm
      _ = normalizedBlockNorm (curvatureBlock
          (curvaturePairing g ((chartAt FourSpace c).symm zx)
            (chartGramFrame g c S hS zx)) Q - 1) := hf (chartGramSection g c S hS zx) hp
      _ = _ := congrArg normalizedBlockNorm (chartGramBlock_eq_frame g c S hS Q zx).symm
  exact congrArg (fun r : ℝ => r ^ 2) hval

theorem actual_plusNorm_square_smooth (o : FrameOrientation g) :
    ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun x => plusNorm o x ^ 2) := by
  apply oriented_frame_normSquare_smooth o quaternionMatrix (plusNorm o)
  intro e he
  exact actual_plusNorm_frame o e he

theorem actual_minusNorm_square_smooth (o : FrameOrientation g) :
    ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun x => minusNorm o x ^ 2) := by
  apply oriented_frame_normSquare_smooth o oppositeQuaternion (minusNorm o)
  intro e he
  exact actual_minusNorm_frame o e he

end
end PositiveEinsteinFour.Geometry
end


section

/-! The norm regularity input is fully derived from the actual local frames
and the four-dimensional quaternion action. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem actual_orientedNormRegularity (o : FrameOrientation g) :
    OrientedNormRegularity o where
  plusSquareSmooth := actual_plusNorm_square_smooth o
  minusSquareSmooth := actual_minusNorm_square_smooth o

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

variable [CompactSpace M]

theorem integral_orientedEulerDensity (o : FrameOrientation g) (hRic : RicciThree g)
    (hvol : FinitePositiveVolume g) :
    (∫ c, orientedEulerDensity g o c ∂volumeMeasure g) = 2 * volumeRatio g *
      (1 + (∫ c, plusNorm o c ^ 2 ∂normalizedVolume g) +
        ∫ c, minusNorm o c ^ 2 ∂normalizedVolume g) := by
  let : IsProbabilityMeasure (normalizedVolume g) := normalizedVolume_isProbability hvol
  have hp := (actual_plusNorm_square_smooth o).continuous.integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  have hm := (actual_minusNorm_square_smooth o).continuous.integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  rw [volumeMeasure_integral_eq_total_mul hvol]
  simp_rw [orientedEulerDensity_eq o hRic]
  have hadd := integral_add ((integrable_const (1 : ℝ)).add hp) hm
  have hadd' := integral_add (integrable_const (1 : ℝ) (μ := normalizedVolume g)) hp
  simp only [Pi.add_apply] at hadd hadd'
  rw [integral_const_mul, hadd, hadd']
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold volumeRatio
  ring

theorem integral_orientedSignatureDensity (o : FrameOrientation g) (hRic : RicciThree g)
    (hvol : FinitePositiveVolume g) :
    (∫ c, orientedSignatureDensity g o c ∂volumeMeasure g) = (4 / 3 : ℝ) * volumeRatio g *
      ((∫ c, plusNorm o c ^ 2 ∂normalizedVolume g) -
        ∫ c, minusNorm o c ^ 2 ∂normalizedVolume g) := by
  let : IsProbabilityMeasure (normalizedVolume g) := normalizedVolume_isProbability hvol
  have hp := (actual_plusNorm_square_smooth o).continuous.integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  have hm := (actual_minusNorm_square_smooth o).continuous.integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  rw [volumeMeasure_integral_eq_total_mul hvol]
  simp_rw [orientedSignatureDensity_eq o hRic]
  rw [integral_const_mul, integral_sub hp hm]
  unfold volumeRatio
  ring

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

theorem orientationCover_positive_eventually (g : SmoothMetric M)
    (e : FrameBundle (orientationCoverMetric g)) :
    ∀ᶠ f in 𝓝 e, (f ∈ orientationCoverPositiveFrames g ↔
      e ∈ orientationCoverPositiveFrames g) := by
  let x := e.base
  let T := (orientationCoverCore (M := M)).localTriv (achart FourSpace x.proj)
  have hx : x ∈ T.source := T.mem_source.mpr (mem_chart_source FourSpace x.proj)
  have hc : ContinuousAt (fun f : FrameBundle (orientationCoverMetric g) => (T f.base).2) e :=
    continuous_snd.continuousAt.comp
      ((T.toOpenPartialHomeomorph.continuousAt hx).comp (continuous_frameBase _).continuousAt)
  have hs : ∀ᶠ f in 𝓝 e, (T f.base).2 = (T e.base).2 := by
    exact hc.eventually (isOpen_discrete _ |>.mem_nhds (mem_singleton _))
  have hd : ContinuousAt (fun f : FrameBundle (orientationCoverMetric g) =>
      (frameChartMatrix (orientationCoverMetric g) x f).det) e :=
    continuous_id.matrix_det.continuousAt.comp
      (continuousAt_pi.mpr (fun i => continuousAt_pi.mpr (fun j =>
        frameChartMatrix_continuousAt _ x e (mem_chart_source FourSpace x) i j)))
  have hn : (frameChartMatrix (orientationCoverMetric g) x e).det ≠ 0 := by
    rw [orientationCover_frameChartMatrix_det g x e (mem_chart_source FourSpace x),
      orientationTransitionDet_self _ (mem_chart_source FourSpace x.proj), one_mul]
    exact e.frame.det_ne_zero
  have hd' : ∀ᶠ f in 𝓝 e,
      decide (0 < (frameChartMatrix (orientationCoverMetric g) x f).det) =
      decide (0 < (frameChartMatrix (orientationCoverMetric g) x e).det) := by
    by_cases hpos : 0 < (frameChartMatrix (orientationCoverMetric g) x e).det
    · filter_upwards [hd.eventually (Ioi_mem_nhds hpos)] with f hf
      simp [hf, hpos]
    · have hneg : (frameChartMatrix (orientationCoverMetric g) x e).det < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) hn
      filter_upwards [hd.eventually (Iio_mem_nhds hneg)] with f hf
      simp [not_lt.mpr hf.le, hpos]
  have hb : ∀ᶠ f : FrameBundle (orientationCoverMetric g) in 𝓝 e,
      f.base ∈ (chartAt FourSpace x).source :=
    (continuous_frameBase _).continuousAt.eventually
      ((chartAt FourSpace x).open_source.mem_nhds (mem_chart_source FourSpace x))
  filter_upwards [hs, hd', hb] with f hs hd' hf
  rw [orientationCover_positive_in_chart g x f hf,
    orientationCover_positive_in_chart g x e (mem_chart_source FourSpace x)]
  exact (congrArg₂ Eq hs hd').to_iff

theorem orientationCoverPositiveFrames_clopen (g : SmoothMetric M) :
    IsClopen (orientationCoverPositiveFrames g) := by
  have hp : IsOpen (orientationCoverPositiveFrames g) := isOpen_iff_mem_nhds.mpr (by
    intro e he
    filter_upwards [orientationCover_positive_eventually g e] with f hf
    exact hf.mpr he)
  have hn : IsOpen (orientationCoverPositiveFrames g)ᶜ := isOpen_iff_mem_nhds.mpr (by
    intro e he
    filter_upwards [orientationCover_positive_eventually g e] with f hf
    exact fun h => he (hf.mp h))
  exact ⟨isOpen_compl_iff.mp hn, hp⟩

def orientationCoverFrameOrientation (g : SmoothMetric M) :
    FrameOrientation (orientationCoverMetric g) where
  positive := orientationCoverPositiveFrames g
  clopen := orientationCoverPositiveFrames_clopen g
  nonempty_fiber x := by
    classical
    let e := canonicalFrame (orientationCoverMetric g) x
    by_cases he : x.snd = decide (0 < e.matrix.det)
    · exact ⟨e, he⟩
    · refine ⟨e.reflect, ?_⟩
      change x.snd = decide (0 < e.reflect.matrix.det)
      rw [reflected_frame_det]
      have hn := e.det_ne_zero
      cases hs : x.snd <;> rcases lt_or_gt_of_ne hn with hn | hn <;>
        simp_all [not_lt.mpr hn.le] <;> rfl
  compatible x e f he := by
    change x.snd = decide (0 < e.matrix.det) at he
    change (x.snd = decide (0 < f.matrix.det)) ↔ 0 < e.matrix.det * f.matrix.det
    rw [he]
    have he' := e.det_ne_zero
    have hf' := f.det_ne_zero
    rcases lt_or_gt_of_ne he' with he' | he' <;> rcases lt_or_gt_of_ne hf' with hf' | hf'
    · simp [not_lt.mpr he'.le, not_lt.mpr hf'.le, mul_pos_of_neg_of_neg he' hf']; rfl
    · simp [not_lt.mpr he'.le, hf', not_lt.mpr (mul_neg_of_neg_of_pos he' hf').le]
    · simp [he', not_lt.mpr hf'.le, not_lt.mpr (mul_neg_of_pos_of_neg he' hf').le]
    · simp [he', hf', mul_pos he' hf']; rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The oriented orthonormal-frame probability, formed from actual normalized
Riemannian volume and Haar probability on the oriented orthogonal fiber. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

variable [T3Space M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normalizedVolumeProbability
theorem canonicalFrameMeasure_integral (g : SmoothMetric M) (o : FrameOrientation g)
    (F : FrameBundle g → ℝ) (hF : Integrable F (canonicalFrameMeasure g o)) :
    (∫ e, F e ∂canonicalFrameMeasure g o) =
      ∫ x, ∫ Q, F (orientedFrameParametrization g o (x, Q)) ∂orientedFrameHaar
        ∂normalizedVolume g := by
  have hmap := measurable_orientedFrameParametrization g o
  have hi : Integrable (fun p => F (orientedFrameParametrization g o p))
      ((normalizedVolume g).prod orientedFrameHaar) :=
    hF.comp_measurable hmap
  rw [canonicalFrameMeasure, integral_map hmap.aemeasurable hF.aestronglyMeasurable]
  exact integral_prod _ hi


end
end PositiveEinsteinFour.Geometry
end


section

/-! Every orthonormal frame determines a continuous point of the actual
orientation cover. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Matrix Set Filter _root_.Topology
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameChartMatrix_det_transition (g : SmoothMetric M) (c : M) (e : FrameBundle g) :
    (frameChartMatrix g c e).det =
      orientationTransitionDet (achart FourSpace e.base) (achart FourSpace c) e.base *
        e.frame.matrix.det := by
  rw [frameChartMatrix_eq, Matrix.det_mul]
  congr 1
  let L := (tangentBundleCore I4 M).coordChange
    (achart FourSpace e.base) (achart FourSpace c) e.base
  have hL : L = fderiv ℝ (chartTransition e.base c) (chartAt FourSpace e.base e.base) := by
    simp only [L, tangentBundleCore_coordChange_achart, extChartAt_coe, extChartAt_coe_symm,
      I4, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
      Function.comp_id, range_id, fderivWithin_univ]
    rfl
  have hm : chartTransitionMatrix e.base c (chartAt FourSpace e.base e.base) =
      LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin 4)) (PiLp.basisFun 2 ℝ (Fin 4)) L.toLinearMap := by
    ext i j
    simp [chartTransitionMatrix, LinearMap.toMatrix_apply, coordinateVector, hL]
  rw [hm, LinearMap.det_toMatrix]
  rfl

theorem orientationFrameClass_local (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    (orientationCoverCore (M := M)).localTriv (achart FourSpace c) (orientationFrameClass g e) =
      (e.base, decide (0 < (frameChartMatrix g c e).det)) := by
  apply Prod.ext
  · rfl
  · rw [frameChartMatrix_det_transition]
    change (if 0 < orientationTransitionDet (achart FourSpace e.base) (achart FourSpace c) e.base
      then decide (0 < e.frame.matrix.det) else !decide (0 < e.frame.matrix.det)) = _
    have ha := orientationTransitionDet_ne_zero (achart FourSpace e.base) (achart FourSpace c)
      ⟨mem_chart_source FourSpace e.base, he⟩
    have hb := e.frame.det_ne_zero
    rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hb with hb | hb
    · simp [not_lt.mpr ha.le, not_lt.mpr hb.le, mul_pos_of_neg_of_neg ha hb]
    · simp [not_lt.mpr ha.le, hb, not_lt.mpr (mul_neg_of_neg_of_pos ha hb).le]
    · simp [ha, not_lt.mpr hb.le, not_lt.mpr (mul_neg_of_pos_of_neg ha hb).le]
    · simp [ha, hb, mul_pos ha hb]

theorem continuous_orientationFrameClass (g : SmoothMetric M) :
    Continuous (orientationFrameClass g) := by
  apply continuous_iff_continuousAt.mpr
  intro e
  let T := (orientationCoverCore (M := M)).localTriv (achart FourSpace e.base)
  have hnear : ∀ᶠ f : FrameBundle g in 𝓝 e, f.base ∈ (chartAt FourSpace e.base).source :=
    (continuous_frameBase g).continuousAt.eventually
      ((chartAt FourSpace e.base).open_source.mem_nhds (mem_chart_source FourSpace e.base))
  apply (T.toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left
    (f := orientationFrameClass g) (x := e) (by exact hnear)).mpr
  have hdet : ContinuousAt (fun f : FrameBundle g => (frameChartMatrix g e.base f).det) e :=
    continuous_id.matrix_det.continuousAt.comp
      (continuousAt_pi.mpr (fun i => continuousAt_pi.mpr (fun j =>
        frameChartMatrix_continuousAt g e.base e (mem_chart_source FourSpace e.base) i j)))
  have hn : (frameChartMatrix g e.base e).det ≠ 0 := by
    rw [frameChartMatrix_det_transition, orientationTransitionDet_self _
      (mem_chart_source FourSpace e.base), one_mul]
    exact e.frame.det_ne_zero
  have hsign : ContinuousAt (fun f : FrameBundle g => decide (0 < (frameChartMatrix g e.base f).det)) e := by
    by_cases hpos : 0 < (frameChartMatrix g e.base e).det
    · apply (continuousAt_const (y := true)).congr_of_eventuallyEq
      filter_upwards [hdet.eventually (Ioi_mem_nhds hpos)] with f hf
      simp [hf]
    · have hneg : (frameChartMatrix g e.base e).det < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) hn
      apply (continuousAt_const (y := false)).congr_of_eventuallyEq
      filter_upwards [hdet.eventually (Iio_mem_nhds hneg)] with f hf
      simp [not_lt.mpr hf.le]
  apply ((continuous_frameBase g).continuousAt.prodMk hsign).congr_of_eventuallyEq
  filter_upwards [hnear] with f hf
  exact orientationFrameClass_local g e.base f hf

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

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

def frameOrientation_of_clopen_sheet (g : SmoothMetric M) {U : Set (OrientationCover M)}
    (hU : IsClopen U) (hne : U.Nonempty) (hproper : Uᶜ.Nonempty) : FrameOrientation g where
  positive := orientationFrameClass g ⁻¹' U
  clopen := hU.preimage (continuous_orientationFrameClass g)
  nonempty_fiber c := by
    have hc : c ∈ orientationCoverProjection '' U := by
      rw [orientationCover_clopen_surjective hU hne]
      trivial
    obtain ⟨x, hx, hxc⟩ := hc
    obtain ⟨e, he⟩ := orientationFrameClass_fiber_surjective g c x.snd
    refine ⟨e, ?_⟩
    change orientationFrameClass g ⟨c, e⟩ ∈ U
    rw [he]
    have heq : (⟨c, x.snd⟩ : OrientationCover M) = x := by
      cases x
      cases hxc
      rfl
    rwa [heq]
  compatible c e f he := by
    change orientationFrameClass g ⟨c, e⟩ ∈ U at he
    change (orientationFrameClass g ⟨c, f⟩ ∈ U) ↔ _
    rw [← frame_sign_eq_iff e f]
    constructor
    · intro hf
      have hij := (orientationCover_clopen_projection_bijective hU hne hproper).injective
        (a₁ := ⟨orientationFrameClass g ⟨c, e⟩, he⟩)
        (a₂ := ⟨orientationFrameClass g ⟨c, f⟩, hf⟩) rfl
      exact congrArg (fun z : U => z.val.snd) hij
    · intro hf
      have heq : orientationFrameClass g ⟨c, e⟩ = orientationFrameClass g ⟨c, f⟩ :=
        congrArg (fun b : Bool => (⟨c, b⟩ : OrientationCover M)) hf
      rwa [← heq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normalized Hausdorff sphere measure has full support.
This follows from its proved Haar-orbit representation. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular MeasureTheory
noncomputable section

theorem continuous_haar_sphere_orbit :
    Continuous (fun P : OrientedOrthogonalFour => orientedDirection P firstDirection) := by
  have hp : Continuous (fun P : OrientedOrthogonalFour => (P, firstDirection)) :=
    continuous_id.prodMk continuous_const
  have ha : Continuous ((fun p : OrientedOrthogonalFour × Directions =>
      orientedDirection p.1 p.2) ∘ (fun P : OrientedOrthogonalFour => (P, firstDirection))) :=
    continuous_orientedDirection.comp hp
  simpa only [Function.comp_def] using ha

theorem sphereMeasure_eq_haar_orbit :
    Measure.map (fun P : OrientedOrthogonalFour => orientedDirection P firstDirection)
      orientedFrameHaar = sphereMeasure := by
  let F := fun P : OrientedOrthogonalFour => orientedDirection P firstDirection
  have hF : Continuous F := continuous_haar_sphere_orbit
  let : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability
  let : IsProbabilityMeasure (Measure.map F orientedFrameHaar) := ⟨by
    rw [Measure.map_apply hF.measurable MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hF.aemeasurable f.continuous.aestronglyMeasurable]
  exact haar_integral_direction f f.continuous firstDirection

theorem sphereMeasure_openPos : Measure.IsOpenPosMeasure sphereMeasure := by
  rw [← sphereMeasure_eq_haar_orbit]
  apply continuous_haar_sphere_orbit.isOpenPosMeasure_map
  intro q
  exact ⟨directionOrientedMatrix q, orientedDirection_completion q⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Four-dimensional polar volume in the same directions used in the
curvature averages. The dimensional constant is kept as the actual angular
mass, since it cancels when the energy-shell probability is normalized. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

noncomputable section

theorem polarAngularMass_eq_ball :
    polarAngularMass = 4 * (volume : Measure FourSpace) (Metric.ball 0 1) := by
  rw [polarAngularMass, Measure.toSphere_apply_univ]
  simp [FourSpace]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Lipschitz parametrizations remain locally Lipschitz in a fixed manifold chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M]

theorem metric_chart_local_edist_bound (g : SmoothMetric M) (c x : M)
    (hx : x ∈ (chartAt FourSpace c).source) (A : FourSpace →L[ℝ] FourSpace) :
    ∃ K : ℝ≥0, ∃ V ∈ 𝓝 x, ∀ y ∈ V, ∀ z ∈ V,
      edist (A (chartAt FourSpace c y)) (A (chartAt FourSpace c z)) ≤
        K * metricEDistance g y z := by
  let z₀ : ChartTarget c := ⟨chartAt FourSpace c x,(chartAt FourSpace c).map_source hx⟩
  let E := frozenFrameLinearEquiv g c z₀
  let L : ℝ≥0 := ⟨1 / Real.sqrt (1 - (1/2 : ℝ)),by positivity⟩
  obtain ⟨V,hV,_,hbound⟩ := exists_frozenFrame_chart_lipschitz_at g c z₀ (1/2)
    (by norm_num) (by norm_num)
  have hVx : V ∈ 𝓝 x := by simpa only [z₀,(chartAt FourSpace c).left_inv hx] using hV
  refine ⟨‖A.comp E.toContinuousLinearMap‖₊ * L,V,hVx,?_⟩
  intro y hy z hz
  have hlin := (A.comp E.toContinuousLinearMap).lipschitz
    (E.symm (chartAt FourSpace c y)) (E.symm (chartAt FourSpace c z))
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    E.apply_symm_apply] at hlin
  calc
    _ ≤ ‖A.comp E.toContinuousLinearMap‖₊ *
        edist (E.symm (chartAt FourSpace c y)) (E.symm (chartAt FourSpace c z)) := hlin
    _ ≤ ‖A.comp E.toContinuousLinearMap‖₊ *
        ((L : ℝ≥0∞) * metricEDistance g y z) := by
      apply mul_le_mul_right
      rw [show (L : ℝ≥0∞) = ENNReal.ofReal (1 / Real.sqrt (1-(1/2 : ℝ))) from
        ENNReal.coe_nnreal_eq L]
      exact hbound y hy z hz
    _ = _ := by rw [ENNReal.coe_mul,mul_assoc]

theorem metric_chart_lipschitz_image (g : SmoothMetric M) (c : M)
    (A : FourSpace →L[ℝ] FourSpace) (f : ℂ → M) (hf : Continuous f) (L : ℝ≥0)
    (hL : ∀ z w, metricEDistance g (f z) (f w) ≤ L * edist z w) :
    ∀ z ∈ f ⁻¹' (chartAt FourSpace c).source,
      ∃ K : ℝ≥0, ∃ V ∈ 𝓝 z,
        LipschitzOnWith K (fun w => A (chartAt FourSpace c (f w))) V := by
  intro z hz
  obtain ⟨K,V,hV,hK⟩ := metric_chart_local_edist_bound g c (f z) hz A
  refine ⟨K*L,f ⁻¹' V,hf.continuousAt hV,?_⟩
  intro a ha b hb
  calc
    _ ≤ (K : ℝ≥0∞) * metricEDistance g (f a) (f b) := hK _ ha _ hb
    _ ≤ (K : ℝ≥0∞) * ((L : ℝ≥0∞)*edist a b) := mul_le_mul_right (hL a b) _
    _ = _ := by rw [ENNReal.coe_mul,mul_assoc]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer the derived full Weyl derivative bound through the published
frame disintegration. No integrated Weyl equation is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.frameEnergyTransferInstance1
local instance frameEnergyTransferInstance2_r9d9562_1 : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace
theorem frame_derivative_energy_le_of_parallel_data
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (d : MetricGreenData g μ) (o : OppositeWeylData d)
    (hparallel : ParallelReflection d) (orientation : FrameOrientation g)
    (hμ : BrinKarcherAveraging g μ) (h : FollandMoments)
    (hHi : Integrable (fun e => ‖frameCurvatureDerivative g e‖ ^ 2) μ)
    (hEiBase : Integrable (fun c => plusGradientEnergy orientation c +
      minusGradientEnergy orientation c) (normalizedVolume g))
    (hInv : DirectionInvariant (fun e => ‖frameCurvatureDerivative g e‖ ^ 2))
    (hturn : ∀ c (e : OrthonormalFrame g c) q,
      frameCurvatureDerivative g (frameTurn e q) = normalCurvatureDerivative g c e q)
    (hE : ∀ c (e : OrthonormalFrame g c),
      gradientSquareNorm (plusWeylGradient g c e) +
        gradientSquareNorm (minusWeylGradient g c e) =
          plusGradientEnergy orientation c + minusGradientEnergy orientation c)
    (hS : ∀ c (e : OrthonormalFrame g c),
      normalizedBlockNorm (plusWeyl g c e) ^ 2 +
        normalizedBlockNorm (minusWeyl g c e) ^ 2 =
          plusNorm orientation c ^ 2 + minusNorm orientation c ^ 2)
    (hvi : Integrable (fun c => plusNorm orientation c ^ 2) (normalizedVolume g))
    (hbi : Integrable (fun c => minusNorm orientation c ^ 2) (normalizedVolume g))
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g) :
    (∫ e, ‖frameCurvatureDerivative g e‖ ^ 2 ∂μ) ≤
      (9 / 4) * (∫ c, plusNorm orientation c ^ 2 +
        minusNorm orientation c ^ 2 ∂normalizedVolume g) := by
  have hmean := frameCurvatureDerivative_mean_square g hμ h
    (fun c => plusGradientEnergy orientation c + minusGradientEnergy orientation c)
    hHi hEiBase hInv hturn
    (fun _ e a => actual_plusWeylGradient_symmetric e hRic a)
    (fun _ e a => actual_plusWeylGradient_trace e hRic a) hE
  have hEi : Integrable (fun e : FrameBundle g =>
      gradientSquareNorm (plusWeylGradient g e.base e.frame) +
        gradientSquareNorm (minusWeylGradient g e.base e.frame)) μ :=
    ((continuous_gradientSquareNorm _ d.continuousGradient).add
      (continuous_gradientSquareNorm _ o.continuousGradient)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSi : Integrable (fun e : FrameBundle g =>
      normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 +
        normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2) μ :=
    (((continuous_normalizedBlockNorm.comp d.continuousWeyl).pow 2).add
      ((continuous_normalizedBlockNorm.comp o.continuousWeyl).pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he := hμ.integral_of_base_value h _ _ hEi hEiBase
    (fun e => hE e.base e.frame)
  have hs := hμ.integral_of_base_value h _ _ hSi (hvi.add hbi)
    (fun e => hS e.base e.frame)
  have hbound := d.totalWeylGradientEnergy_le o hparallel
    (fun e => (actual_norm_pinching hRic hpositive e).le)
  rw [he, hs] at hbound
  simp only [Pi.add_apply] at hbound
  rw [hmean]
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Disintegration of the constructed frame probability for functions that
only depend on the first frame direction. The measure is the actual product
of normalized Riemannian volume and oriented orthogonal Haar probability. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular MeasureTheory Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

/-- Right multiplication by the explicit completion produces the direction
obtained by the orthogonal action on the sphere. -/
theorem orientedFrameMap_completion_first (e : OrthonormalFrame g c)
    (P : OrientedOrthogonalFour) (q : Directions) :
    (orientedFrameMap e (P * directionOrientedMatrix q)).frame.vector 0 =
      (frameTurn e (orientedDirection P q)).frame.vector 0 := by
  change _ = (e.turn (orientedDirection P q)).vector 0
  rw [OrthonormalFrame.turn_first]
  ext i
  change (∑ j, e.matrix i j * (P.val * directionFrameMatrix q) j 0) =
    ∑ j, e.matrix i j * (P.val *ᵥ WithLp.ofLp q.val) j
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, directionFrameMatrix_zero]

/-- Haar averaging of a direction-invariant function equals its spherical
average. Only integrability on the Haar fiber is required. -/
theorem orientedHaar_integral_eq_sphere (e : OrthonormalFrame g c)
    (F : FrameBundle g → ℝ) (hInv : DirectionInvariant F)
    (hF : Integrable (fun Q => F (orientedFrameMap e Q)) orientedFrameHaar) :
    (∫ Q, F (orientedFrameMap e Q) ∂orientedFrameHaar) =
      ∫ q, F (frameTurn e q) ∂sphereMeasure := by
  apply haar_integral_eq_sphere_of_rotation _ _ hF
  intro P q
  exact hInv (orientedFrameMap e (P * directionOrientedMatrix q))
    (frameTurn e (orientedDirection P q)) rfl
    (orientedFrameMap_completion_first e P q)

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

/-- The precise Brin--Karcher averaging input holds for the frame probability
constructed from actual Riemannian volume. -/
theorem canonicalFrameMeasure_averaging (g : SmoothMetric M) (o : FrameOrientation g) :
    BrinKarcherAveraging g (canonicalFrameMeasure g o) where
  probability := inferInstance
  fiberFormula F A hF _hA hInv hmean := by
    let : IsProbabilityMeasure (normalizedVolume g) :=
      normalizedVolume_isProbability (actual_finitePositiveVolume g)
    rw [canonicalFrameMeasure_integral g o F hF]
    have hi : Integrable (fun p => F (orientedFrameParametrization g o p))
        ((normalizedVolume g).prod orientedFrameHaar) :=
      hF.comp_measurable (measurable_orientedFrameParametrization g o)
    apply integral_congr_ae
    filter_upwards [hi.prod_right_ae] with x hx
    have hf : Integrable
        (fun Q => F (orientedFrameMap (positiveFrameSection g o x).frame Q))
        orientedFrameHaar := hx
    calc
      _ = ∫ q, F (frameTurn (positiveFrameSection g o x).frame q) ∂sphereMeasure :=
        orientedHaar_integral_eq_sphere _ F hInv hf
      _ = A (positiveFrameSection g o x).base := hmean _ _
      _ = A x := congrArg A (positiveFrameSection_base g o x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Weyl norm gap follows from the regularized energy estimate and
the sharp scalar Sobolev inequality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance weylGapFrameCompact_r9d9562_1 (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g
omit [T3Space M] [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M] in
theorem continuous_plusNorm (g : SmoothMetric M) (o : FrameOrientation g) :
    Continuous (plusNorm o) := by
  have h := Real.continuous_sqrt.comp (actual_plusNorm_square_smooth o).continuous
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact (Real.sqrt_sq (plusNorm_nonneg o x)).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive constant multiplication of an actual smooth Riemannian metric.
The constructor and chart-tensor identities discharge the local part of the
classical scaling input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bornology
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metricInChart_rescaleMetric (g : SmoothMetric M) (c : ℝ) (hc : 0 < c)
    (x : M) (z : FourSpace) :
    metricInChart (rescaleMetric g c hc) x z = c • metricInChart g x z := by
  ext i j
  rfl

theorem chartMetric_rescaleMetric (g : SmoothMetric M) (c : ℝ) (hc : 0 < c)
    (x : M) : chartMetric (rescaleMetric g c hc) x = c • chartMetric g x :=
  metricInChart_rescaleMetric g c hc x _

end
end PositiveEinsteinFour.Geometry
end


section

/-! A positive scalar change of metric transports the actual clopen
orientation of the orthonormal frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scaleFrameBundle (g h : SmoothMetric M) (a : ℝ)
    (ha : ∀ x, (a ^ 2) • chartMetric h x = chartMetric g x)
    (e : FrameBundle g) : FrameBundle h :=
  ⟨e.base, e.frame.scaleBetween a (ha e.base)⟩

theorem continuous_scaleFrameBundle (g h : SmoothMetric M) (a : ℝ)
    (ha : ∀ x, (a ^ 2) • chartMetric h x = chartMetric g x) :
    Continuous (scaleFrameBundle g h a ha) := by
  apply continuous_induced_rng.mpr
  have hv (i : Fin 4) : Continuous (fun e : FrameBundle g =>
      (⟨e.base, a • e.frame.vector i⟩ : TangentBundle I4 M)) :=
    (continuous_tangent_fiber_smul a).comp
      ((continuous_apply i).comp (continuous_snd.comp (continuous_frameRealization g)))
  convert! (continuous_frameBase g).prodMk (continuous_pi hv) using 1
  all_goals try with_reducible_and_instances rfl

theorem det_scale_product_pos_iff (a : ℝ) (ha : 0 < a) (E F : Mat4) :
    0 < (a • E).det * (a • F).det ↔ 0 < E.det * F.det := by
  rw [Matrix.det_smul, Matrix.det_smul]
  have hpow : 0 < a ^ Fintype.card (Fin 4) := pow_pos ha _
  have heq : (a ^ Fintype.card (Fin 4) * E.det) *
      (a ^ Fintype.card (Fin 4) * F.det) =
      (a ^ Fintype.card (Fin 4) * a ^ Fintype.card (Fin 4)) * (E.det * F.det) := by ring
  rw [heq, mul_pos_iff_of_pos_left (mul_pos hpow hpow)]

def rescaleFrameOrientation (g : SmoothMetric M) (c : ℝ) (hc : 0 < c)
    (o : FrameOrientation g) : FrameOrientation (rescaleMetric g c hc) := by
  let a := Real.sqrt c
  have ha : 0 < a := Real.sqrt_pos.mpr hc
  have ha2 : a ^ 2 = c := Real.sq_sqrt hc.le
  have hforward (x : M) : (a ^ 2) • chartMetric g x =
      chartMetric (rescaleMetric g c hc) x := by
    rw [ha2, chartMetric_rescaleMetric]
  let f := scaleFrameBundle (rescaleMetric g c hc) g a hforward
  have hback (x : M) : (a⁻¹ ^ 2) • chartMetric (rescaleMetric g c hc) x =
      chartMetric g x := by
    rw [chartMetric_rescaleMetric, smul_smul, ← ha2]
    have hs : a⁻¹ ^ 2 * a ^ 2 = 1 := by field_simp [ha.ne']
    rw [hs, one_smul]
  refine { positive := f ⁻¹' o.positive
           clopen := o.clopen.preimage (continuous_scaleFrameBundle _ _ a hforward)
           nonempty_fiber := ?_
           compatible := ?_ }
  · intro x
    obtain ⟨e, he⟩ := o.nonempty_fiber x
    refine ⟨e.scaleBetween a⁻¹ (hback x), ?_⟩
    have hf : f ⟨x, e.scaleBetween a⁻¹ (hback x)⟩ = (⟨x, e⟩ : FrameBundle g) := by
      apply frameRealization_injective g
      apply Prod.ext
      · rfl
      · funext i
        change (⟨x, ((e.scaleBetween a⁻¹ (hback x)).scaleBetween a
          (hforward x)).vector i⟩ : TangentBundle I4 M) = ⟨x, e.vector i⟩
        simp only [OrthonormalFrame.scaleBetween_vector, smul_smul,
          mul_inv_cancel₀ ha.ne', one_smul]
    change f ⟨x, e.scaleBetween a⁻¹ (hback x)⟩ ∈ o.positive
    rw [hf]
    exact he
  · intro x e k he
    change (⟨x, k.scaleBetween a (hforward x)⟩ : FrameBundle g) ∈ o.positive ↔
      0 < e.matrix.det * k.matrix.det
    rw [o.compatible x (e.scaleBetween a (hforward x))
      (k.scaleBetween a (hforward x)) he]
    exact det_scale_product_pos_iff a ha e.matrix k.matrix

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The sharp upper normalization needed by the polar volume estimate.
Arbitrarily fine ball covers with nearly optimal total Lebesgue measure
bound the unnormalized fourth Hausdorff measure. Only the upper bound is
needed; no isodiametric inequality or equality case is used. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal _root_.Topology

noncomputable section

theorem fourSpace_volume_ball (x : FourSpace) (r : ℝ) :
    volume (ball x r) = ENNReal.ofReal r ^ 4 * ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  simpa [FourSpace] using
    InnerProductSpace.volume_ball_of_dim_even (E := FourSpace) (k := 2) (by simp [FourSpace]) x r

theorem fourSpace_volume_closedBall (x : FourSpace) (r : ℝ) :
    volume (closedBall x r) = ENNReal.ofReal r ^ 4 * ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  simpa [FourSpace] using
    InnerProductSpace.volume_closedBall_of_dim_even (E := FourSpace) (k := 2)
      (by simp [FourSpace]) x r

theorem fourSpace_ediam_closedBall_le (x : FourSpace) {r : ℝ} (hr : 0 ≤ r) :
    Metric.ediam (closedBall x r) ≤ 2 * ENNReal.ofReal r := by
  rw [← Metric.closedEBall_ofReal hr]
  exact Metric.ediam_closedEBall_le

theorem fourSpace_ball_cost (x : FourSpace) {r : ℝ} (hr : 0 ≤ r) :
    Metric.ediam (closedBall x r) ^ (4 : ℝ) ≤
      ENNReal.ofReal (32 / Real.pi ^ 2) * volume (closedBall x r) := by
  rw [show (4 : ℝ) = (4 : ℕ) by norm_num, ENNReal.rpow_natCast]
  calc
    Metric.ediam (closedBall x r) ^ 4 ≤ (2 * ENNReal.ofReal r) ^ 4 :=
      pow_le_pow_left₀ zero_le (fourSpace_ediam_closedBall_le x hr) 4
    _ = 16 * ENNReal.ofReal r ^ 4 := by rw [mul_pow]; norm_num
    _ = ENNReal.ofReal (32 / Real.pi ^ 2) * volume (closedBall x r) := by
      rw [fourSpace_volume_closedBall, mul_left_comm,
        ball_normalization_product, mul_comm]

theorem euclideanHausdorff_unitBall_le :
    (Measure.hausdorffMeasure 4 : Measure FourSpace) (ball 0 1) ≤ 16 := by
  classical
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδpos : ∀ n, 0 < δ n := fun n => by dsimp [δ]; positivity
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hcovers (n : ℕ) : ∃ (s : Set FourSpace) (r : FourSpace → ℝ),
      s.Countable ∧ s ⊆ ball 0 1 ∧ (∀ x ∈ s, r x ∈ Ioo 0 (δ n)) ∧
      (ball (0 : FourSpace) 1 ⊆ ⋃ x ∈ s, closedBall x (r x)) ∧
      (∑' x : s, volume (closedBall x.val (r x.val))) ≤
        volume (ball (0 : FourSpace) 1) + ENNReal.ofReal (δ n) := by
    apply Besicovitch.exists_closedBall_covering_tsum_measure_le volume
      (ne_of_gt (ENNReal.ofReal_pos.mpr (hδpos n))) (fun _ => Ioo 0 (δ n)) (ball 0 1)
    intro x _ ε hε
    refine ⟨min (δ n) ε / 2, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact half_pos (lt_min (hδpos n) hε)
    · exact (half_lt_self (lt_min (hδpos n) hε)).trans_le (min_le_left _ _)
    · exact half_pos (lt_min (hδpos n) hε)
    · exact (half_lt_self (lt_min (hδpos n) hε)).trans_le (min_le_right _ _)
  choose s r hcount _hradcenter hrad hcover hsum using hcovers
  let : ∀ n, Countable (s n) := fun n => (hcount n).to_subtype
  have hδe : Tendsto (fun n => ENNReal.ofReal (δ n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_apply] using!
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hδ
  have hdiam : Tendsto (fun n => 2 * ENNReal.ofReal (δ n)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using!
      (ENNReal.continuous_const_mul (a := 2) (by norm_num)).continuousAt.tendsto.comp hδe
  have hH := Measure.hausdorffMeasure_le_liminf_tsum (ι := fun n => s n) 4
    (ball (0 : FourSpace) 1) (fun n => 2 * ENNReal.ofReal (δ n)) hdiam
    (fun n x => closedBall x.val (r n x.val))
    (Eventually.of_forall fun n x =>
      (fourSpace_ediam_closedBall_le x.val (hrad n x.val x.property).1.le).trans
        (by gcongr; exact (hrad n x.val x.property).2.le))
    (Eventually.of_forall fun n => by simpa only [iUnion_subtype] using hcover n)
  have hcost (n : ℕ) :
      (∑' x : s n, Metric.ediam (closedBall x.val (r n x.val)) ^ (4 : ℝ)) ≤
      ENNReal.ofReal (32 / Real.pi ^ 2) *
        (volume (ball (0 : FourSpace) 1) + ENNReal.ofReal (δ n)) := by
    calc
      _ ≤ ∑' x : s n, ENNReal.ofReal (32 / Real.pi ^ 2) *
          volume (closedBall x.val (r n x.val)) :=
        ENNReal.tsum_le_tsum fun x => fourSpace_ball_cost x.val (hrad n x.val x.property).1.le
      _ = ENNReal.ofReal (32 / Real.pi ^ 2) *
          ∑' x : s n, volume (closedBall x.val (r n x.val)) := ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr; exact hsum n
  have hlim : Tendsto (fun n => ENNReal.ofReal (32 / Real.pi ^ 2) *
      (volume (ball (0 : FourSpace) 1) + ENNReal.ofReal (δ n))) atTop (𝓝 16) := by
    have h := (ENNReal.continuous_const_mul (a := ENNReal.ofReal (32 / Real.pi ^ 2))
      ENNReal.ofReal_ne_top).continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := volume (ball (0 : FourSpace) 1))).add hδe)
    simpa only [Function.comp_apply, add_zero, fourSpace_volume_ball, ENNReal.ofReal_one, one_pow, one_mul,
      ball_normalization_product] using! h
  exact hH.trans ((Filter.liminf_le_liminf (Eventually.of_forall hcost)).trans_eq hlim.liminf_eq)

theorem euclideanHausdorffFactor_le :
    (euclideanHausdorffFactor : ℝ≥0∞) ≤ ENNReal.ofReal (32 / Real.pi ^ 2) := by
  have h := euclideanHausdorff_unitBall_le
  rw [euclideanHausdorff_apply, fourSpace_volume_ball, ENNReal.ofReal_one,
    one_pow, one_mul, ← ball_normalization_product] at h
  exact (ENNReal.mul_le_mul_iff_left (by positivity : ENNReal.ofReal (Real.pi ^ 2 / 2) ≠ 0)
    ENNReal.ofReal_ne_top).mp h

theorem riemannianChartFactor_le_one : riemannianChartFactor ≤ 1 := by
  calc
    riemannianChartFactor ≤ ENNReal.ofReal (Real.pi ^ 2 / 32) *
        ENNReal.ofReal (32 / Real.pi ^ 2) :=
      by dsimp only [riemannianChartFactor]; gcongr; exact euclideanHausdorffFactor_le
    _ = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have h : Real.pi ^ 2 / 32 * (32 / Real.pi ^ 2) = 1 := by
        field_simp
      rw [h, ENNReal.ofReal_one]

theorem polarAngularMass_eq : polarAngularMass = ENNReal.ofReal (2 * Real.pi ^ 2) := by
  rw [polarAngularMass_eq_ball, fourSpace_volume_ball, ENNReal.ofReal_one, one_pow, one_mul]
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identification and integration of the actual Jacobi determinant with
its first-conjugate-point truncation. The family is the single global
solution attached to each actual frame, independent of endpoint time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def actualJacobiMatrix (g : SmoothMetric M) (hRic : RicciThree g)
    (p : ℝ × FrameBundle g) : NormalMatrix :=
  (actualJacobiSolution g hRic p.2).J p.1

end
end PositiveEinsteinFour.Geometry
end


section

/-! Before the first conjugate point the Jacobi determinant is positive.
The proof removes the initial zero by `dslope`, then uses continuity and
invertibility on the whole closed interval. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix Set
open scoped _root_.Topology Matrix.Norms.L2Operator

noncomputable section

theorem jacobi_det_pos_of_preconjugate (J : ℝ → NormalMatrix) (t : ℝ)
    (ht : 0 < t) (hc : ContinuousOn J (Icc 0 t))
    (hJ0 : J 0 = 0) (hJ : HasDerivAt J 1 0)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (J s)) :
    0 < (J t).det := by
  have hnorm := normalizedJacobi_continuousOn hc hJ
  have hunit := normalizedJacobi_isUnit hJ0 hJ hpre
  have hdet : Continuous (fun A : NormalMatrix => A.det) := continuous_id.matrix_det
  have hp : 0 < (normalizedJacobi J t).det := by
    apply positive_of_continuousOn_nonzero (fun s => (normalizedJacobi J s).det) t ht.le
      (hdet.comp_continuousOn hnorm)
    · rw [normalizedJacobi_zero hJ, Matrix.det_one]
      norm_num
    · intro s hs
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (hunit s hs)).ne_zero
  rw [normalizedJacobi_pos hJ0 ht.ne', Matrix.det_smul, Fintype.card_fin] at hp
  exact (mul_pos_iff_of_pos_left (pow_pos (inv_pos.mpr ht) 3)).mp hp

theorem MatrixJacobiSolution.det_pos_of_preconjugate {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (t : ℝ) (ht : 0 < t)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s)) :
    0 < (d.J t).det := by
  apply jacobi_det_pos_of_preconjugate d.J t ht d.continuous_J.continuousOn
    d.initial_position
  · simpa only [d.initial_velocity] using d.position_derivative 0
  · exact hpre

theorem RegularJacobi.det_pos_of_preconjugate {t : ℝ} (d : RegularJacobi t)
    (ht : 0 < t) (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s)) :
    0 < (d.J t).det := by
  apply jacobi_det_pos_of_preconjugate d.J t ht
    (fun s hs => (d.position_derivative s hs).continuousAt.continuousWithinAt)
    d.initial_position
  · simpa only [d.initial_velocity] using d.position_derivative 0 ⟨le_rfl, ht.le⟩
  · exact hpre

theorem RegularJacobi.truncatedDensity_nonneg {t : ℝ} (d : RegularJacobi t)
    (ht : 0 ≤ t) : 0 ≤ d.truncatedDensity := by
  classical
  unfold RegularJacobi.truncatedDensity
  split_ifs with hpre
  · by_cases ht0 : t = 0
    · subst t
      rw [d.initial_position, Matrix.det_zero]
    · exact (d.det_pos_of_preconjugate (lt_of_le_of_ne ht (Ne.symm ht0)) hpre).le
  · exact le_rfl

end
end PositiveEinsteinFour.Jacobi

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Jacobi
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobi_det_pos_of_preconjugate (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (t : ℝ) (ht : 0 < t)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit ((actualJacobiSolution g hRic e).J s)) :
    0 < ((actualJacobiSolution g hRic e).J t).det :=
  (actualJacobiSolution g hRic e).det_pos_of_preconjugate t ht hpre

end
end PositiveEinsteinFour.Geometry
end


section

/-! The regularized Weyl cube root is an actual smooth base scalar.
Its moments and Dirichlet energy agree with the frame quantities in the
regularized gap argument. The sharp scalar inequality remains explicit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

/-- Positive regularization makes the Weyl cube root smooth even on its zero set. -/
def regularizedPlusWeylScalar (o : FrameOrientation g) (ε : ℝ) (hε : 0 < ε) :
    SmoothScalar (M := M) := by
  refine ⟨fun x => (plusNorm o x ^ 2 + ε ^ 2) ^ (1 / 6 : ℝ), ?_⟩
  intro x
  have hp : 0 < plusNorm o x ^ 2 + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  exact (Real.contDiffAt_rpow_const_of_ne hp.ne').comp_contMDiffAt
    (f := fun x : M => plusNorm o x ^ 2 + ε ^ 2)
    ((actual_plusNorm_square_smooth o).add contMDiff_const).contMDiffAt

theorem regularizedPlusWeylScalar_frame (o : FrameOrientation g)
    (ε : ℝ) (hε : 0 < ε) (e : FrameBundle g) (he : e ∈ o.positive) :
    (regularizedPlusWeylScalar o ε hε).val e.base =
      regularizedWeylRoot ε (plusWeyl g e.base e.frame) := by
  change (plusNorm o e.base ^ 2 + ε ^ 2) ^ (1 / 6 : ℝ) = _
  rw [regularizedWeylRoot_eq, actual_plusNorm_frame o e he]

theorem regularizedPlusWeylScalar_gradient {μ : Measure (FrameBundle g)}
    (p : ParallelMetricData g μ) (o : FrameOrientation g)
    (hflow : OrientationPreservingFlow p.toMetricGreenData o)
    (ε : ℝ) (hε : 0 < ε) (e : FrameBundle g) (he : e ∈ o.positive)
    (i : Fin 4) :
    scalarGradient g (regularizedPlusWeylScalar o ε hε).val e i =
      p.toMetricGreenData.weylRootFirstField ε hε i e := by
  let a := regularizedPlusWeylScalar o ε hε
  let s : ScalarCovariantData p.toMetricGreenData a.val :=
    Classical.choice (p.scalarCalculus.toPetersenInput a.val a.property)
  exact scalarGradient_eq_of_frame_derivative s o hflow
    (p.toMetricGreenData.weylRootField ε)
    (fun i => p.toMetricGreenData.weylRootFirstField ε hε i)
    (regularizedPlusWeylScalar_frame o ε hε)
    (p.toMetricGreenData.regularizedWeylRoot_derivative ε hε) e he i

variable [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance weylScalarFrameCompact : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem regularizedPlusWeylScalar_moment (o : FrameOrientation g)
    (p : ParallelMetricData g (canonicalFrameMeasure g o))
    (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    (∫ e, p.toMetricGreenData.weylRootField ε e ^ n ∂canonicalFrameMeasure g o) =
      ∫ x, (regularizedPlusWeylScalar o ε hε).val x ^ n ∂normalizedVolume g := by
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  calc
    _ = ∫ e : FrameBundle g,
        (regularizedPlusWeylScalar o ε hε).val e.base ^ n
          ∂canonicalFrameMeasure g o := by
      apply integral_congr_ae
      filter_upwards [canonicalFrameMeasure_supported g o] with e he
      rw [regularizedPlusWeylScalar_frame o ε hε e he]
      rfl
    _ = _ := canonicalFrameMeasure_integral_base g o _
      (((regularizedPlusWeylScalar o ε hε).property.continuous.pow n).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local continuous representatives of one actual L2 function agree on
overlaps by full support of Riemannian volume, and hence glue globally. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

/-- The gluing uses only the actual full-support volume and local smooth
representatives.  No global continuity or elliptic premise is assumed. -/
theorem scalar_continuous_representative_of_local (g : SmoothMetric M)
    (b : Lp ℝ 2 (normalizedVolume g))
    (hlocal : ∀ x : M, ∃ U : Set M, ∃ f : M → ℝ,
      IsOpen U ∧ x ∈ U ∧ ContinuousOn f U ∧
        (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict U] f) :
    ∃ F : M → ℝ, Continuous F ∧ F =ᵐ[normalizedVolume g] b := by
  let := normalizedVolume_isOpenPosMeasure g
  choose U f hU hx hf hb using hlocal
  let F : M → ℝ := fun x => f x x
  have hagree (x y : M) (hy : y ∈ U x) : F y = f x y := by
    have hb₁ : (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict (U y ∩ U x)] f y :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hb y)
    have hb₂ : (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict (U y ∩ U x)] f x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hb x)
    have heq : EqOn (f y) (f x) (U y ∩ U x) :=
      Measure.eqOn_open_of_ae_eq (hb₁.symm.trans hb₂) ((hU y).inter (hU x))
        ((hf y).mono inter_subset_left)
        ((hf x).mono inter_subset_right)
    exact heq ⟨hx y, hy⟩
  have hF : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply ((hf x).continuousAt ((hU x).mem_nhds (hx x))).congr_of_eventuallyEq
    filter_upwards [(hU x).mem_nhds (hx x)] with y hy
    exact hagree x y hy
  refine ⟨F, hF, ?_⟩
  have hcover : (univ : Set M) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have heach (x : M) : ∀ᵐ y ∂normalizedVolume g, y ∈ U x → F y = b y := by
    have he := (ae_restrict_iff' (hU x).measurableSet).mp (hb x)
    filter_upwards [he] with y hy
    intro hyU
    exact (hagree x y hyU).trans (hy hyU).symm
  have hfin : ∀ᵐ y ∂normalizedVolume g, ∀ x : s, y ∈ U x → F y = b y :=
    ae_all_iff.mpr (fun x => heach x)
  filter_upwards [hfin] with y hy
  obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp (hs (mem_univ y))
  exact hy ⟨x, hxs⟩ hyx

end
end PositiveEinsteinFour.Geometry
end


section

/-! A bounded-derivative smooth scalar chain rule on the actual first-jet
closure.  The proof uses smooth approximation and strong convergence of
bounded multipliers, rather than assuming a weak chain rule. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff BigOperators _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def smoothScalarCompose (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (a : SmoothScalar (M := M)) : SmoothScalar (M := M) :=
  ⟨fun x => φ (a.val x), hφ.contMDiff.comp a.property⟩

theorem smoothScalarCompose_gradient {μ : Measure (FrameBundle g)}
    (d : ParallelMetricData g μ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (a : SmoothScalar (M := M)) (e : FrameBundle g) (i : Fin 4) :
    scalarGradient g (smoothScalarCompose φ hφ a).val e i =
      deriv φ (a.val e.base) * scalarGradient g a.val e i := by
  obtain ⟨f, hf⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
  change (d.toMetricGreenData.flow i).map 0 f = e at hf
  let sa := Classical.choice (d.scalarCalculus.toPetersenInput a.val a.property)
  let b := smoothScalarCompose φ hφ a
  let sb := Classical.choice (d.scalarCalculus.toPetersenInput b.val b.property)
  have hd := sa.derivativeValue i 0 f
  rw [hf] at hd
  have hb := sb.derivativeValue i 0 f
  rw [hf] at hb
  have houter : HasDerivAt φ (deriv φ (a.val e.base)) (a.val e.base) :=
    (hφ.differentiable (by simp)).differentiableAt.hasDerivAt
  have hc := HasDerivAt.comp (h₂ := φ)
    (h := fun t : ℝ => a.val (((d.toMetricGreenData.flow i).map t) f).base)
    0 (by simpa only [hf] using houter) hd
  exact hb.unique hc

variable {μ : Measure (FrameBundle g)} [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem scalarValueL2_coe (a : SmoothScalar (M := M)) :
    smoothScalarValueL2 g μ a =ᵐ[μ] fun e => a.val e.base :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (smoothScalarValue g a)

theorem scalarGradientL2_coe (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (i : Fin 4) :
    smoothScalarGradientL2 d i a =ᵐ[μ] fun e => scalarGradient g a.val e i :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (smoothScalarGradient d i a)

theorem scalarCompose_value (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {C : ℝ≥0} (hLip : LipschitzWith C φ) (hzero : φ 0 = 0)
    (a : SmoothScalar (M := M)) :
    smoothScalarValueL2 g μ (smoothScalarCompose φ hφ a) =
      hLip.compLp hzero (smoothScalarValueL2 g μ a) := by
  apply Lp.ext
  filter_upwards [scalarValueL2_coe (g := g) (μ := μ) a,
    scalarValueL2_coe (g := g) (μ := μ) (smoothScalarCompose φ hφ a),
    hLip.coeFn_compLp hzero (smoothScalarValueL2 g μ a)] with e ha hb hc
  rw [hb, hc]
  change φ (a.val e.base) = φ (smoothScalarValueL2 g μ a e)
  rw [ha]

theorem scalarCompose_gradient (d : ParallelMetricData g μ)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) {D : ℝ}
    (hbound : ∀ r, |deriv φ r| ≤ D) (a : SmoothScalar (M := M)) (i : Fin 4) :
    smoothScalarGradientL2 d i (smoothScalarCompose φ hφ a) =
      scalarCompositionL2Multiply (fun e => deriv φ (smoothScalarValueL2 g μ a e))
        ((hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable
          (Lp.aestronglyMeasurable (smoothScalarValueL2 g μ a)))
        (fun e => hbound _) (smoothScalarGradientL2 d i a) := by
  apply Lp.ext
  filter_upwards [scalarGradientL2_coe d (smoothScalarCompose φ hφ a) i,
    scalarGradientL2_coe d a i, scalarValueL2_coe (g := g) (μ := μ) a,
    scalarCompositionL2Multiply_coe (fun e => deriv φ (smoothScalarValueL2 g μ a e))
      ((hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable (smoothScalarValueL2 g μ a)))
      (fun e => hbound _) (smoothScalarGradientL2 d i a)] with e h₁ h₂ h₃ h₄
  rw [h₁, h₄, h₂, h₃]
  exact smoothScalarCompose_gradient d φ hφ a e i

/-- Composition by a smooth function with bounded derivative preserves the
actual scalar H¹ closure and has the expected four weak derivatives. -/
theorem scalarH1_compose_exists (d : ParallelMetricData g μ)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) {C : ℝ≥0}
    (hLip : LipschitzWith C φ) (hzero : φ 0 = 0)
    {D : ℝ} (hD : 0 ≤ D) (hbound : ∀ r, |deriv φ r| ≤ D)
    (u : scalarH1 d) :
    ∃ v : scalarH1 d, scalarH1Value d v = hLip.compLp hzero (scalarH1Value d u) ∧
      ∀ i : Fin 4, scalarH1Gradient d i v =ᵐ[μ]
        fun e => deriv φ (scalarH1Value d u e) * scalarH1Gradient d i u e := by
  obtain ⟨s, hs, ht⟩ := mem_closure_iff_seq_limit.mp u.property
  choose a ha using hs
  have hjet : Tendsto (fun n => smoothScalarFirstJet d (a n)) atTop (𝓝 u.val) := by
    simpa only [ha] using ht
  let V : ℕ → ScalarL2 g μ := fun n => smoothScalarValueL2 g μ (a n)
  have hV : Tendsto V atTop (𝓝 (scalarH1Value d u)) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) none).continuous.tendsto
      u.val |>.comp hjet
  obtain ⟨ns, hns, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hV).exists_seq_tendsto_ae
  let f : ℕ → ScalarL2 g μ := fun n => V (ns n)
  let G : Fin 4 → ℕ → ScalarL2 g μ := fun i n => smoothScalarGradientL2 d i (a (ns n))
  have hG (i : Fin 4) : Tendsto (G i) atTop (𝓝 (scalarH1Gradient d i u)) :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin 4) => ScalarL2 g μ) (some i)).continuous.tendsto
      u.val |>.comp hjet).comp hns.tendsto_atTop
  let k : ℕ → FrameBundle g → ℝ := fun n e => deriv φ (f n e)
  let k₀ : FrameBundle g → ℝ := fun e => deriv φ (scalarH1Value d u e)
  have hk (n : ℕ) : AEStronglyMeasurable (k n) μ :=
    (hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable (f n))
  have hk₀ : AEStronglyMeasurable k₀ μ :=
    (hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (scalarH1Value d u))
  have hkD (n : ℕ) (e : FrameBundle g) : |k n e| ≤ D := hbound _
  have hk₀D (e : FrameBundle g) : |k₀ e| ≤ D := hbound _
  have hkconv : ∀ᵐ e ∂μ, Tendsto (fun n => k n e) atTop (𝓝 (k₀ e)) := by
    filter_upwards [hAE] with e he
    exact (hφ.continuous_deriv (by simp)).continuousAt.tendsto.comp he
  let v₀ : ScalarL2 g μ := hLip.compLp hzero (scalarH1Value d u)
  let vG : Fin 4 → ScalarL2 g μ := fun i =>
    scalarCompositionL2Multiply k₀ hk₀ hk₀D (scalarH1Gradient d i u)
  let p : Option (Fin 4) → ScalarL2 g μ := fun j => match j with
    | none => v₀
    | some i => vG i
  let E := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin 4) => ScalarL2 g μ)
  let v : ScalarJetL2 g μ := E.symm p
  have hc : Tendsto (fun n => E (smoothScalarFirstJet d
      (smoothScalarCompose φ hφ (a (ns n))))) atTop (𝓝 p) := by
    apply tendsto_pi_nhds.mpr
    intro j
    cases j with
    | none =>
      change Tendsto (fun n => smoothScalarValueL2 g μ
        (smoothScalarCompose φ hφ (a (ns n)))) atTop (𝓝 v₀)
      simp only [scalarCompose_value φ hφ hLip hzero]
      exact (hLip.continuous_compLp hzero).continuousAt.tendsto.comp (hV.comp hns.tendsto_atTop)
    | some i =>
      change Tendsto (fun n => smoothScalarGradientL2 d i
        (smoothScalarCompose φ hφ (a (ns n)))) atTop (𝓝 (vG i))
      simp only [scalarCompose_gradient d φ hφ hbound]
      exact scalarCompositionL2Multiply_tendsto hk hk₀ hD hkD hk₀D hkconv (hG i)
  have hvlim : Tendsto (fun n => smoothScalarFirstJet d
      (smoothScalarCompose φ hφ (a (ns n)))) atTop (𝓝 v) := by
    simpa only [Function.comp_def, E.symm_apply_apply] using!
      (E.symm.continuous.tendsto p).comp hc
  have hv : v ∈ scalarH1 d := by
    apply (Submodule.isClosed_topologicalClosure (LinearMap.range (smoothScalarFirstJet d))).mem_of_tendsto hvlim
    exact Eventually.of_forall fun n => Submodule.le_topologicalClosure _
      ⟨smoothScalarCompose φ hφ (a (ns n)), rfl⟩
  refine ⟨⟨v, hv⟩, rfl, ?_⟩
  intro i
  exact scalarCompositionL2Multiply_coe k₀ hk₀ hk₀D (scalarH1Gradient d i u)

/-- A bound on the ordinary derivative supplies the Lipschitz hypothesis. -/
theorem scalarH1_compose_exists_of_deriv_bound (d : ParallelMetricData g μ)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hzero : φ 0 = 0)
    {D : ℝ≥0} (hbound : ∀ r, |deriv φ r| ≤ D) (u : scalarH1 d) :
    ∃ v : scalarH1 d,
      (scalarH1Value d v : FrameBundle g → ℝ) =ᵐ[μ]
        (fun e => φ (scalarH1Value d u e)) ∧
      ∀ i : Fin 4, scalarH1Gradient d i v =ᵐ[μ]
        fun e => deriv φ (scalarH1Value d u e) * scalarH1Gradient d i u e := by
  have hLip : LipschitzWith D φ := lipschitzWith_of_nnnorm_deriv_le
    (hφ.differentiable (by simp)) (fun r => by
      exact_mod_cast (show ‖deriv φ r‖ ≤ (D : ℝ) by simpa only [Real.norm_eq_abs] using hbound r))
  obtain ⟨v, hv, hgrad⟩ := scalarH1_compose_exists d φ hφ hLip hzero D.coe_nonneg hbound u
  refine ⟨v, ?_, hgrad⟩
  rw [hv]
  exact hLip.coeFn_compLp hzero _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Limits of the value and all four weak derivatives remain in the actual
intrinsic first-jet closure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem scalarH1_jet_limit (d : ParallelMetricData g μ) (v : ℕ → scalarH1 d)
    (f : ScalarL2 g μ) (G : Fin 4 → ScalarL2 g μ)
    (hf : Tendsto (fun n => scalarH1Value d (v n)) atTop (𝓝 f))
    (hG : ∀ i, Tendsto (fun n => scalarH1Gradient d i (v n)) atTop (𝓝 (G i))) :
    ∃ u : scalarH1 d, scalarH1Value d u = f ∧ ∀ i, scalarH1Gradient d i u = G i := by
  let p : Option (Fin 4) → ScalarL2 g μ := fun j => match j with
    | none => f
    | some i => G i
  let E := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin 4) => ScalarL2 g μ)
  have hp : Tendsto (fun n => E (v n).val) atTop (𝓝 p) := by
    apply tendsto_pi_nhds.mpr
    intro j
    cases j with
    | none => exact hf
    | some i => exact hG i
  have hlim : Tendsto (fun n => (v n).val) atTop (𝓝 (E.symm p)) := by
    simpa only [Function.comp_def, E.symm_apply_apply] using!
      (E.symm.continuous.tendsto p).comp hp
  have hu : E.symm p ∈ scalarH1 d := by
    apply (Submodule.isClosed_topologicalClosure (LinearMap.range (smoothScalarFirstJet d))).mem_of_tendsto hlim
    exact Eventually.of_forall (fun n => (v n).property)
  exact ⟨⟨E.symm p, hu⟩, rfl, fun _ => rfl⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Rational Brezis--Kato tests with bounded derivatives.  Their exact
algebra relates the tested Dirichlet form to the square test, uniformly as
the truncation parameter tends to zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

theorem scalarKatoTest_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    HasDerivAt (scalarKatoTest lam) (scalarKatoTestRate lam s) s := by
  have hd : HasDerivAt (fun r : ℝ => 1 + lam * r ^ 2) (2 * lam * s) s := by
    refine ((((hasDerivAt_id s).pow 2).const_mul lam).const_add 1).congr_deriv ?_
    simp only [id_eq]
    norm_num <;> ring
  refine (((hasDerivAt_id s).pow 3).div hd (scalarKato_den_pos hlam s).ne').congr_deriv ?_
  · simp only [scalarKatoTestRate, id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub]
    congr 1
    ring

theorem scalarKatoSquare_hasDerivAt {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    HasDerivAt (scalarKatoSquare lam) (scalarKatoSquareRate lam s) s := by
  have hd : HasDerivAt (fun r : ℝ => 1 + lam * r ^ 2) (2 * lam * s) s := by
    refine ((((hasDerivAt_id s).pow 2).const_mul lam).const_add 1).congr_deriv ?_
    simp only [id_eq]
    norm_num <;> ring
  have hp := scalarKato_den_pos hlam s
  have hr := Real.sqrt_pos.mpr hp
  have hs : HasDerivAt (fun r : ℝ => Real.sqrt (1 + lam * r ^ 2))
      (lam * s / Real.sqrt (1 + lam * s ^ 2)) s := by
    refine ((Real.hasDerivAt_sqrt hp.ne').comp s hd).congr_deriv ?_
    · field_simp
  have hsq := Real.sq_sqrt hp.le
  refine (((hasDerivAt_id s).pow 2).div hs hr.ne').congr_deriv ?_
  · simp only [scalarKatoSquareRate, id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [hsq]
    field_simp [hp.ne', hr.ne']
    have hsq' : Real.sqrt (1 + s ^ 2 * lam) ^ 2 = 1 + s ^ 2 * lam := by
      simpa only [mul_comm lam] using hsq
    nlinarith only [congrArg (fun r : ℝ => (2 * s) * r) hsq']

theorem scalarKatoTest_deriv {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    deriv (scalarKatoTest lam) s = scalarKatoTestRate lam s :=
  (scalarKatoTest_hasDerivAt hlam s).deriv

theorem scalarKatoSquare_deriv {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    deriv (scalarKatoSquare lam) s = scalarKatoSquareRate lam s :=
  (scalarKatoSquare_hasDerivAt hlam s).deriv

@[simp] theorem scalarKatoTest_zero (lam : ℝ) : scalarKatoTest lam 0 = 0 := by
  simp [scalarKatoTest]

@[simp] theorem scalarKatoSquare_zero (lam : ℝ) : scalarKatoSquare lam 0 = 0 := by
  simp [scalarKatoSquare]

theorem scalarKato_test_square {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    s * scalarKatoTest lam s = scalarKatoSquare lam s ^ 2 := by
  simp only [scalarKatoTest, scalarKatoSquare, div_pow,
    Real.sq_sqrt (scalarKato_den_pos hlam s).le]
  ring

theorem scalarKatoTest_abs_le {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    |scalarKatoTest lam s| ≤ lam⁻¹ * |s| := by
  rw [scalarKatoTest, abs_div, abs_pow, abs_of_pos (scalarKato_den_pos hlam s)]
  apply (div_le_iff₀ (scalarKato_den_pos hlam s)).mpr
  apply (mul_le_mul_iff_right₀ hlam).mp
  have hpow : |s| ^ 3 = |s| * s ^ 2 := by rw [pow_succ, sq_abs]; ring
  rw [hpow]
  field_simp [hlam.ne']
  nlinarith only [abs_nonneg s]

theorem scalarKatoSquare_sq_le {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    scalarKatoSquare lam s ^ 2 ≤ s ^ 4 := by
  rw [scalarKatoSquare, div_pow, Real.sq_sqrt (scalarKato_den_pos hlam s).le]
  calc
    (s ^ 2) ^ 2 / (1 + lam * s ^ 2) ≤ (s ^ 2) ^ 2 :=
      div_le_self (sq_nonneg _) (by nlinarith [mul_nonneg hlam.le (sq_nonneg s)])
    _ = s ^ 4 := by ring

theorem scalarKatoSquareRate_sq_le {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    scalarKatoSquareRate lam s ^ 2 ≤ 2 * scalarKatoTestRate lam s := by
  have hp := scalarKato_den_pos hlam s
  have hx : 0 ≤ lam * s ^ 2 := mul_nonneg hlam.le (sq_nonneg s)
  have hpoly : (2 + lam * s ^ 2) ^ 2 ≤ 2 * (3 + lam * s ^ 2) * (1 + lam * s ^ 2) := by
    nlinarith [sq_nonneg (lam * s ^ 2)]
  calc
    scalarKatoSquareRate lam s ^ 2 =
        (s ^ 2 * (2 + lam * s ^ 2) ^ 2) / ((1 + lam * s ^ 2) ^ 2 * (1 + lam * s ^ 2)) := by
      rw [scalarKatoSquareRate, div_pow, mul_pow, mul_pow, Real.sq_sqrt hp.le]
    _ ≤ (s ^ 2 * (2 * (3 + lam * s ^ 2) * (1 + lam * s ^ 2))) /
        ((1 + lam * s ^ 2) ^ 2 * (1 + lam * s ^ 2)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (sq_nonneg s))
        (by positivity)
    _ = 2 * scalarKatoTestRate lam s := by
      unfold scalarKatoTestRate
      field_simp [hp.ne']

theorem scalarKatoSquareRate_abs_le {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    |scalarKatoSquareRate lam s| ≤ 6 / lam + 1 := by
  have hs := scalarKatoSquareRate_sq_le hlam s
  have ht := scalarKatoTestRate_le hlam s
  have hq : 0 ≤ 6 / lam := by positivity
  have ht' : 2 * scalarKatoTestRate lam s ≤ 6 / lam := by
    calc
      _ ≤ 2 * (3 / lam) := mul_le_mul_of_nonneg_left ht (by norm_num)
      _ = _ := by ring
  have hsq := hs.trans ht'
  nlinarith only [hsq, hq, sq_abs (scalarKatoSquareRate lam s),
    sq_nonneg (|scalarKatoSquareRate lam s| - 1)]

theorem scalarKatoSquare_tendsto (s : ℝ) :
    Tendsto (fun lam : ℝ => scalarKatoSquare lam s) (𝓝 0) (𝓝 (s ^ 2)) := by
  have hd : Tendsto (fun lam : ℝ => Real.sqrt (1 + lam * s ^ 2)) (𝓝 0) (𝓝 1) := by
    have hi : Tendsto (fun lam : ℝ => 1 + lam * s ^ 2) (𝓝 0) (𝓝 1) := by
      have hh : Tendsto (fun lam : ℝ => lam * s ^ 2) (𝓝 0) (𝓝 0) := by
        simpa only [zero_mul, id_eq] using! (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).mul_const (s ^ 2)
      simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hh
    simpa only [Function.comp_def, Real.sqrt_one] using! (Real.continuous_sqrt.tendsto 1).comp hi
  simpa only [scalarKatoSquare, Pi.div_apply, div_one] using!
    tendsto_const_nhds.div hd one_ne_zero

/-- A uniform fourth-moment bound for the rational square tests gives the
eighth moment of the original function by Fatou's lemma. -/
theorem scalarKato_memLp_eight_of_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : AEStronglyMeasurable f μ)
    {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
    (hbound : ∀ lam : ℝ, 0 < lam →
      eLpNorm (fun x => scalarKatoSquare lam (f x)) 4 μ ≤ C) : MemLp f 8 μ := by
  let lam : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hlam (n : ℕ) : 0 < lam n := by dsimp [lam]; positivity
  have hlamlim : Tendsto lam atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => scalarKatoSquare (lam n) (f x))
      atTop (𝓝 (f x ^ 2)) :=
    Eventually.of_forall fun x => (scalarKatoSquare_tendsto (f x)).comp hlamlim
  have hsq : MemLp (fun x => f x ^ 2) 4 μ :=
    ⟨hf.pow 2, lt_of_le_of_lt (Lp.eLpNorm_le_of_ae_tendsto
      (Eventually.of_forall fun n => hbound (lam n) (hlam n))
      (fun n => (scalarKatoSquare_smooth (hlam n)).continuous.comp_aestronglyMeasurable hf) hlim) (lt_top_iff_ne_top.mpr hC)⟩
  have hexp : (8 : ℝ≥0∞) / 2 = 4 := by
    rw [show (8 : ℝ≥0∞) = 4 * 2 by norm_num]
    exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  apply (memLp_norm_rpow_iff (p := 8) (q := 2) hf (by norm_num) (by norm_num)).mp
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    hexp] using hsq

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem scalarH1_katoTest_exists (d : ParallelMetricData g μ) {lam : ℝ} (hlam : 0 < lam)
    (u : scalarH1 d) :
    ∃ v : scalarH1 d,
      (scalarH1Value d v : FrameBundle g → ℝ) =ᵐ[μ]
        (fun e => scalarKatoTest lam (scalarH1Value d u e)) ∧
      ∀ i : Fin 4, scalarH1Gradient d i v =ᵐ[μ]
        fun e => scalarKatoTestRate lam (scalarH1Value d u e) * scalarH1Gradient d i u e := by
  have hbound (s : ℝ) : |deriv (scalarKatoTest lam) s| ≤ 3 / lam := by
    rw [scalarKatoTest_deriv hlam, abs_of_nonneg (scalarKatoTestRate_nonneg hlam s)]
    exact scalarKatoTestRate_le hlam s
  obtain ⟨v, hv, hgrad⟩ := scalarH1_compose_exists_of_deriv_bound d (scalarKatoTest lam)
    (scalarKatoTest_smooth hlam) (scalarKatoTest_zero lam)
    (D := ⟨3 / lam, by positivity⟩) hbound u
  refine ⟨v, hv, ?_⟩
  intro i
  simpa only [scalarKatoTest_deriv hlam] using hgrad i

theorem scalarH1_katoSquare_exists (d : ParallelMetricData g μ) {lam : ℝ} (hlam : 0 < lam)
    (u : scalarH1 d) :
    ∃ v : scalarH1 d,
      (scalarH1Value d v : FrameBundle g → ℝ) =ᵐ[μ]
        (fun e => scalarKatoSquare lam (scalarH1Value d u e)) ∧
      ∀ i : Fin 4, scalarH1Gradient d i v =ᵐ[μ]
        fun e => scalarKatoSquareRate lam (scalarH1Value d u e) * scalarH1Gradient d i u e := by
  obtain ⟨v, hv, hgrad⟩ := scalarH1_compose_exists_of_deriv_bound d (scalarKatoSquare lam)
    (scalarKatoSquare_smooth hlam) (scalarKatoSquare_zero lam)
    (D := ⟨6 / lam + 1, by positivity⟩) (fun s => by
      rw [scalarKatoSquare_deriv hlam]
      exact scalarKatoSquareRate_abs_le hlam s) u
  refine ⟨v, hv, ?_⟩
  intro i
  simpa only [scalarKatoSquare_deriv hlam] using hgrad i

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth nonpositive test detecting the negative set, with nonnegative
bounded derivative. It is admissible in the actual H1 closure. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter
open scoped _root_.Topology ContDiff NNReal

noncomputable section

theorem scalarNegativeTest_zero : scalarNegativeTest 0 = 0 := by
  simp [scalarNegativeTest]

theorem scalarNegativeTest_deriv_bound :
    ∃ D : ℝ≥0, ∀ r : ℝ, |deriv scalarNegativeTest r| ≤ D := by
  have hc : Continuous (deriv scalarNegativeTest) :=
    scalarNegativeTest_smooth.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hc).isBounded.exists_norm_le
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro r
  by_cases hr : r ∈ Icc (-1 : ℝ) 0
  · exact (hC _ ⟨r, hr, rfl⟩).trans (le_max_left _ _)
  · have hout : r < -1 ∨ 0 < r := by
      simpa only [mem_Icc, not_and_or, not_le] using hr
    rcases hout with hr | hr
    · have he : scalarNegativeTest =ᶠ[𝓝 r] fun _ => (-1 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hr] with s hs
        have hs' : s < -1 := hs
        dsimp [scalarNegativeTest]
        rw [Real.smoothTransition.one_of_one_le (by linarith)]
      rw [he.deriv_eq, deriv_const, abs_zero]
      exact le_max_right _ _
    · have he : scalarNegativeTest =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
        exact scalarNegativeTest_eq_zero hs.le
      rw [he.deriv_eq, deriv_const, abs_zero]
      exact le_max_right _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth bounded-derivative approximations of the subcritical power
s ↦ |s|^q s, for 0 < q < 2. Their derivative growth is uniformly quadratic. -/

namespace PositiveEinsteinFour.Geometry

open Filter
open scoped _root_.Topology ContDiff

noncomputable section

theorem scalarNonlinearTruncation_hasDeriv (q : ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    HasDerivAt (scalarNonlinearTruncation q ε)
      (scalarNonlinearTruncationDerivative q ε s) s := by
  have ha : 0 < s ^ 2 + ε := by positivity
  have hb : 0 < 1 + ε * s ^ 2 := by positivity
  have hpow := (((hasDerivAt_id s).pow 2).add_const ε).rpow_const
    (p := q / 2) (Or.inl ha.ne')
  have h := ((hasDerivAt_id s).mul hpow).div
    (((hasDerivAt_id s).pow 2).const_mul ε |>.const_add 1) hb.ne'
  refine h.congr_deriv ?_
  · dsimp [scalarNonlinearTruncationDerivative]
    rw [Real.rpow_sub ha]
    simp only [Real.rpow_one]
    field_simp

theorem scalarNonlinearTruncation_deriv (q : ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    deriv (scalarNonlinearTruncation q ε) s = scalarNonlinearTruncationDerivative q ε s :=
  (scalarNonlinearTruncation_hasDeriv q hε s).deriv

theorem scalarNonlinearTruncation_zero (q ε : ℝ) :
    scalarNonlinearTruncation q ε 0 = 0 := by
  simp [scalarNonlinearTruncation]

theorem scalarNonlinearTruncation_deriv_growth {q ε : ℝ}
    (hq : 0 < q) (hq2 : q < 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    |deriv (scalarNonlinearTruncation q ε) s| ≤ 5 * (1 + s ^ 2) := by
  rw [scalarNonlinearTruncation_deriv q hε, scalarNonlinearTruncationDerivative, abs_mul]
  have hfrac : 0 ≤ (s ^ 2 + ε) ^ (q / 2) / (1 + ε * s ^ 2) := by positivity
  rw [abs_of_nonneg hfrac]
  have hf : (s ^ 2 + ε) ^ (q / 2) / (1 + ε * s ^ 2) ≤ 1 + s ^ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    exact (scalarNonlinearTruncation_power_bound hq hq2 hε hε1 s).trans
      (le_mul_of_one_le_right (by positivity) (by linarith [mul_nonneg hε.le (sq_nonneg s)]))
  exact (mul_le_mul hf (scalarNonlinearTruncation_bracket_bound hq hq2 hε s)
    (abs_nonneg _) (by positivity)).trans_eq (mul_comm _ _)

theorem scalarNonlinearTruncation_deriv_bounded {q ε : ℝ}
    (hq : 0 < q) (hq2 : q < 2) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℝ) :
    |deriv (scalarNonlinearTruncation q ε) s| ≤ 5 / ε := by
  rw [scalarNonlinearTruncation_deriv q hε, scalarNonlinearTruncationDerivative, abs_mul]
  have hfrac : 0 ≤ (s ^ 2 + ε) ^ (q / 2) / (1 + ε * s ^ 2) := by positivity
  rw [abs_of_nonneg hfrac]
  have hf : (s ^ 2 + ε) ^ (q / 2) / (1 + ε * s ^ 2) ≤ 1 / ε := by
    apply (div_le_iff₀ (by positivity)).mpr
    apply (scalarNonlinearTruncation_power_bound hq hq2 hε hε1 s).trans
    rw [div_mul_eq_mul_div, one_mul]
    apply (le_div_iff₀ hε).mpr
    nlinarith [sq_nonneg s]
  have h := mul_le_mul hf (scalarNonlinearTruncation_bracket_bound hq hq2 hε s)
    (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 1 / ε)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compactly supported smooth extension of the power on a positive
bounded interval. This is used only after the weak solution is positive. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter Metric
open scoped _root_.Topology ContDiff NNReal

noncomputable section

/-- The extension is smooth on all of R, vanishes at zero, and has bounded
first derivative. On the positive interval it is exactly the desired power. -/
theorem scalar_positive_power_extension (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ φ 0 = 0 ∧
      (∃ D : ℝ≥0, ∀ t, |deriv φ t| ≤ D) ∧
      ∀ t ∈ Icc a B, φ t = t ^ q ∧ deriv φ t = q * t ^ (q - 1) := by
  let φ := positivePowerExtension a B q ha hB
  have hφ : ContDiff ℝ ∞ φ := positivePowerExtension_smooth a B q ha hB
  have hc : HasCompactSupport φ := positivePowerExtension_compact a B q ha hB
  have hd := (hφ.continuous_deriv (by first | simp | exact_mod_cast le_top)).bounded_above_of_compact_support hc.deriv
  obtain ⟨D, hD⟩ := hd
  refine ⟨φ, hφ, hc, ?_, ⟨⟨max D 0, le_max_right _ _⟩, ?_⟩, ?_⟩
  · have hone : positivePowerInner a ha 0 = 1 :=
      (positivePowerInner a ha).one_of_mem_closedBall (mem_closedBall_self (by
        change 0 ≤ a / 4
        positivity))
    simp only [φ, positivePowerExtension, hone, sub_self, mul_zero, zero_mul]
  · intro t
    exact (show |deriv φ t| ≤ D by simpa only [Real.norm_eq_abs] using hD t).trans (le_max_left _ _)
  · intro t ht
    exact ⟨positivePowerExtension_eq a B q ha hB ht.1 ht.2,
      positivePowerExtension_deriv a B q ha hB ht.1 ht.2⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar Sobolev energy as a genuine Hilbert norm.  Only the four
first-derivative coordinates are rescaled; the value coordinate is unchanged. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

theorem scalarWeightedH1_closed (d : ParallelMetricData g μ) :
    IsClosed (scalarWeightedH1 d : Set (ScalarJetL2 g μ)) := by
  rw [scalarWeightedH1, Submodule.map_coe]
  exact (scalarWeightedJetEquiv g μ).isClosed_image.mpr
    (Submodule.isClosed_topologicalClosure _)

instance scalarWeightedH1_complete (d : ParallelMetricData g μ) :
    CompleteSpace (scalarWeightedH1 d) :=
  (scalarWeightedH1_closed d).isComplete.completeSpace_coe

/-- The exact weighted inner product, on arbitrary completed scalar jets. -/
theorem scalarWeightedH1_inner (d : ParallelMetricData g μ) (u v : scalarH1 d) :
    inner ℝ (scalarWeightedH1Equiv d u) (scalarWeightedH1Equiv d v) =
      inner ℝ (scalarH1Value d u) (scalarH1Value d v) +
        (1 / 2 : ℝ) * ∑ i : Fin 4,
          inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v) := by
  change (∑ j : Option (Fin 4),
    inner ℝ (scalarWeightedJetEquiv g μ u.val j)
      (scalarWeightedJetEquiv g μ v.val j)) = _
  rw [Fintype.sum_option]
  simp only [scalarWeightedJetEquiv_none, scalarWeightedJetEquiv_some,
    inner_smul_left, inner_smul_right, conj_trivial]
  have hs : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = (1 / 2 : ℝ) :=
    Real.mul_self_sqrt (by norm_num)
  change inner ℝ (scalarH1Value d u) (scalarH1Value d v) +
    (∑ i : Fin 4, Real.sqrt (1 / 2) *
      (Real.sqrt (1 / 2) * inner ℝ (scalarH1Gradient d i u)
        (scalarH1Gradient d i v))) = _
  simp only [← mul_assoc, hs, Finset.mul_sum]

theorem scalarWeightedH1_norm_sq (d : ParallelMetricData g μ) (u : scalarH1 d) :
    ‖scalarWeightedH1Equiv d u‖ ^ 2 = ‖scalarH1Value d u‖ ^ 2 +
      (1 / 2 : ℝ) * ∑ i : Fin 4, ‖scalarH1Gradient d i u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, scalarWeightedH1_inner]
  simp only [real_inner_self_eq_norm_sq]

theorem smoothScalarToWeightedH1_dense (d : ParallelMetricData g μ) :
    DenseRange (smoothScalarToWeightedH1 d) := by
  have hd : DenseRange (fun a : SmoothScalar (M := M) => smoothScalarToH1 d a) := by
    change Dense (range (fun a : SmoothScalar (M := M) => smoothScalarToH1 d a))
    rw [Topology.IsInducing.subtypeVal.dense_iff]
    intro u
    apply closure_mono (s := range (smoothScalarFirstJet d)) ?_ u.property
    rintro v ⟨a, rfl⟩
    exact ⟨smoothScalarToH1 d a, ⟨a, rfl⟩, rfl⟩
  exact (scalarWeightedH1Equiv d).surjective.denseRange.comp hd
    (scalarWeightedH1Equiv d).continuous

section Canonical

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarWeighted_baseProbability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end Canonical
end
end PositiveEinsteinFour.Geometry
end


section

/-! Dominated convergence for the two regularized moments in the Weyl
gap argument. All bounds are uniform in the smoothing parameter. -/
namespace PositiveEinsteinFour.Geometry
open MeasureTheory Filter Set
open scoped _root_.Topology
noncomputable section

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integral_weyl_regularized_power_tendsto (v w : C(Ω, ℝ))
    (p : ℝ) (hp : 0 ≤ p) :
    Tendsto (fun n => ∫ x, w x * (v x ^ 2 + weylGapEpsilon n ^ 2) ^ p ∂μ) atTop
      (𝓝 (∫ x, w x * (v x ^ 2) ^ p ∂μ)) := by
  have hpow : Continuous (fun x : Ω => (v x ^ 2 + 1) ^ p) :=
    ((v.continuous.pow 2).add continuous_const).rpow_const (fun _ => Or.inr hp)
  apply tendsto_integral_of_dominated_convergence (fun x => |w x| * (v x ^ 2 + 1) ^ p)
  · intro n
    exact (w.continuous.mul (((v.continuous.pow 2).add continuous_const).rpow_const
      (fun _ => Or.inr hp))).aestronglyMeasurable
  · exact (w.continuous.abs.mul hpow).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · intro n
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) p)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.rpow_le_rpow (by positivity) _ hp
    have h0 := weylGapEpsilon_pos n
    have h1 := weylGapEpsilon_le_one n
    nlinarith
  · filter_upwards [] with x
    have ht : Tendsto (fun n => v x ^ 2 + weylGapEpsilon n ^ 2) atTop (𝓝 (v x ^ 2)) := by
      simpa using (tendsto_const_nhds (x := v x ^ 2)).add (weylGapEpsilon_tendsto.pow 2)
    exact tendsto_const_nhds.mul (ht.rpow_const (Or.inr hp))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive smooth approximations of the absolute value, with the exact
value error and contraction of the scalar Dirichlet energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def smoothScalarAbsRegularized (a : SmoothScalar (M := M)) (ε : ℝ) (hε : 0 < ε) :
    SmoothScalar (M := M) := by
  refine ⟨fun x => Real.sqrt (a.val x ^ 2 + ε ^ 2), ?_⟩
  intro x
  exact (Real.contDiffAt_sqrt (ne_of_gt (add_pos_of_nonneg_of_pos
    (sq_nonneg _) (sq_pos_of_pos hε)))).comp_contMDiffAt
      (f := fun x : M => a.val x ^ 2 + ε ^ 2)
      ((a.property.pow 2).add contMDiff_const).contMDiffAt

omit [IsManifold I4 ∞ M] in
theorem smoothScalarAbsRegularized_pos (a : SmoothScalar (M := M))
    (ε : ℝ) (hε : 0 < ε) (x : M) :
    0 < (smoothScalarAbsRegularized a ε hε).val x :=
  Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε))

omit [IsManifold I4 ∞ M] in
theorem smoothScalarAbsRegularized_sq (a : SmoothScalar (M := M))
    (ε : ℝ) (hε : 0 < ε) (x : M) :
    (smoothScalarAbsRegularized a ε hε).val x ^ 2 = a.val x ^ 2 + ε ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

omit [IsManifold I4 ∞ M] in
theorem smoothScalarAbsRegularized_error (a : SmoothScalar (M := M))
    (ε : ℝ) (hε : 0 < ε) (x : M) :
    |(smoothScalarAbsRegularized a ε hε).val x - (|a.val x|)| ≤ ε := by
  have hlo : |a.val x| ≤ (smoothScalarAbsRegularized a ε hε).val x := by
    change |a.val x| ≤ Real.sqrt (a.val x ^ 2 + ε ^ 2)
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε, sq_abs (a.val x)])
  have hup : (smoothScalarAbsRegularized a ε hε).val x ≤ |a.val x| + ε := by
    apply (sq_le_sq₀ (smoothScalarAbsRegularized_pos a ε hε x).le (by positivity)).mp
    rw [smoothScalarAbsRegularized_sq]
    nlinarith [abs_nonneg (a.val x), sq_abs (a.val x)]
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

theorem smoothScalarAbsRegularized_gradient {g : SmoothMetric M}
    {μ : Measure (FrameBundle g)} (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (ε : ℝ) (hε : 0 < ε)
    (e : FrameBundle g) (i : Fin 4) :
    scalarGradient g (smoothScalarAbsRegularized a ε hε).val e i =
      (a.val e.base / (smoothScalarAbsRegularized a ε hε).val e.base) *
        scalarGradient g a.val e i := by
  obtain ⟨f, hf⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
  change (d.toMetricGreenData.flow i).map 0 f = e at hf
  let sa := Classical.choice (d.scalarCalculus.toPetersenInput a.val a.property)
  let b := smoothScalarAbsRegularized a ε hε
  let sb := Classical.choice (d.scalarCalculus.toPetersenInput b.val b.property)
  have hp : 0 < a.val e.base ^ 2 + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  have houter : HasDerivAt (fun r : ℝ => Real.sqrt (r ^ 2 + ε ^ 2))
      (a.val e.base / b.val e.base) (a.val e.base) := by
    refine ((Real.hasDerivAt_sqrt hp.ne').comp (a.val e.base)
      (((hasDerivAt_id (a.val e.base)).pow 2).add_const (ε ^ 2))).congr_deriv ?_
    · symm
      change a.val e.base / Real.sqrt (a.val e.base ^ 2 + ε ^ 2) = _
      simp only [id_eq]
      ring
  have hd := sa.derivativeValue i 0 f
  rw [hf] at hd
  have hb := sb.derivativeValue i 0 f
  rw [hf] at hb
  have hc := HasDerivAt.comp
    (h₂ := fun r : ℝ => Real.sqrt (r ^ 2 + ε ^ 2))
    (h := fun t : ℝ => a.val (((d.toMetricGreenData.flow i).map t) f).base)
    0 (by simpa only [hf] using houter) hd
  exact hb.unique hc

theorem smoothScalarAbsRegularized_gradient_sq_le {g : SmoothMetric M}
    {μ : Measure (FrameBundle g)} (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (ε : ℝ) (hε : 0 < ε)
    (e : FrameBundle g) (i : Fin 4) :
    scalarGradient g (smoothScalarAbsRegularized a ε hε).val e i ^ 2 ≤
      scalarGradient g a.val e i ^ 2 := by
  have hr := smoothScalarAbsRegularized_pos a ε hε e.base
  have hc : (a.val e.base / (smoothScalarAbsRegularized a ε hε).val e.base) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (sq_pos_of_pos hr), smoothScalarAbsRegularized_sq]
    linarith [sq_nonneg ε]
  rw [smoothScalarAbsRegularized_gradient d, mul_pow]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (sq_nonneg (scalarGradient g a.val e i))

variable [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance scalarAbs_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance scalarAbs_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The L² tail absorption in the rational Brezis--Kato estimate.  All
constants are independent of the rational truncation parameter. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped _root_.Topology ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

local instance katoTail_four : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance katoTail_realFour : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 4) := ⟨by norm_num⟩

theorem scalarLp_four_norm_sq (f : Lp ℝ 4 μ) :
    ‖f‖ ^ 2 = Real.sqrt (∫ x, f x ^ 4 ∂μ) := by
  have hfn := scalarLp_norm_sq_eq_moment (μ := μ) (p := 4) (by norm_num)
  rw [show ENNReal.ofReal (4 : ℝ) = (4 : ℝ≥0∞) by norm_num] at hfn
  have h := hfn f
  have hi : (∫ x, |f x| ^ (4 : ℝ) ∂μ) = ∫ x, f x ^ 4 ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change |f x| ^ (4 : ℝ) = f x ^ 4
      rw [Real.rpow_ofNat, ← abs_pow, abs_of_nonneg (show 0 ≤ f x ^ 4 by positivity)]
  rw [hi, show (2 : ℝ) / 4 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow] at h
  exact h

theorem scalarKato_square_memLp {f : X → ℝ} (hf : MemLp f 4 μ) :
    MemLp (fun x => f x ^ 2) 2 μ := by
  have h := hf.norm_rpow_div 2
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h
  have he : (4 : ℝ≥0∞) / 2 = 2 := by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
    exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  simpa only [he] using h

/-- The multiplication estimate used for the tail, in ordinary real integrals. -/
theorem scalarKato_tail_pairing {V W : X → ℝ} (hV : MemLp V 2 μ)
    (hW : MemLp W 4 μ) (n : ℕ) :
    (∫ x, scalarKatoTail V n x * W x ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, scalarKatoTail V n x ^ 2 ∂μ) *
        Real.sqrt (∫ x, W x ^ 4 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => le_max_right (V x - (n : ℝ)) 0)
    (Eventually.of_forall fun x => sq_nonneg (W x))
    (by
      rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num]
      change MemLp (scalarKatoTail V n) 2 μ
      exact scalarKatoTail_memLp hV n)
    (by
      rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num]
      exact scalarKato_square_memLp hW)
  simpa only [scalarKatoTail, ENNReal.ofReal_ofNat, Real.rpow_two, ← Real.sqrt_eq_rpow,
    show (fun x => (W x ^ 2) ^ 2) = (fun x => W x ^ 4) by funext x; ring] using h

/-- A fixed Sobolev estimate and the tested energy bound imply the eighth
moment.  The potential only needs its genuine L² integrability. -/
theorem scalarKato_memLp_eight_of_energy [IsFiniteMeasure μ] {f V : X → ℝ}
    (hf : MemLp f 4 μ) (hV : MemLp V 2 μ) {C : ℝ} (hC : 0 < C)
    (hW : ∀ lam : ℝ, 0 < lam → MemLp (fun x => scalarKatoSquare lam (f x)) 4 μ)
    (henergy : ∀ lam : ℝ, 0 < lam →
      Real.sqrt (∫ x, scalarKatoSquare lam (f x) ^ 4 ∂μ) ≤ C *
        ((∫ x, f x ^ 4 ∂μ) +
          4 * ∫ x, V x * scalarKatoSquare lam (f x) ^ 2 ∂μ)) :
    MemLp f 8 μ := by
  let A := ∫ x, f x ^ 4 ∂μ
  have hA : 0 ≤ A := integral_nonneg fun x => by positivity
  obtain ⟨n, hn⟩ := scalarKatoTail_small hV (show 0 < 1 / (8 * C) by positivity)
  let D := 2 * C * (1 + 4 * n) * A
  have hD : 0 ≤ D := by dsimp [D]; positivity
  apply scalarKato_memLp_eight_of_bound hf.aestronglyMeasurable
    (C := ENNReal.ofReal (D + 1)) ENNReal.ofReal_ne_top
  intro lam hlam
  let W := fun x => scalarKatoSquare lam (f x)
  have hi4 : Integrable (fun x => f x ^ 4) μ := by
    have h := hf.integrable_norm_pow (by decide : (4 : ℕ) ≠ 0)
    have he : (fun x => ‖f x‖ ^ 4) = (fun x => f x ^ 4) := by
      funext x
      rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
    rwa [he] at h
  have hW2 := scalarKato_square_memLp (hW lam hlam)
  have hvw : Integrable (fun x => V x * W x ^ 2) μ := hV.integrable_mul hW2
  have htw : Integrable (fun x => scalarKatoTail V n x * W x ^ 2) μ :=
    (scalarKatoTail_memLp hV n).integrable_mul hW2
  have hi2 : Integrable (fun x => W x ^ 2) μ := hW2.integrable (by norm_num)
  have hpair : (∫ x, V x * W x ^ 2 ∂μ) ≤
      (n : ℝ) * A + Real.sqrt (∫ x, scalarKatoTail V n x ^ 2 ∂μ) *
        Real.sqrt (∫ x, W x ^ 4 ∂μ) := by
    calc
      _ ≤ ∫ x, (n : ℝ) * W x ^ 2 + scalarKatoTail V n x * W x ^ 2 ∂μ := by
        apply integral_mono hvw ((hi2.const_mul _).add htw)
        intro x
        have hv : V x ≤ (n : ℝ) + scalarKatoTail V n x := by
          dsimp [scalarKatoTail]
          linarith [le_max_left (V x - (n : ℝ)) 0]
        change V x * W x ^ 2 ≤ (n : ℝ) * W x ^ 2 + scalarKatoTail V n x * W x ^ 2
        nlinarith [sq_nonneg (W x)]
      _ = (n : ℝ) * (∫ x, W x ^ 2 ∂μ) +
          ∫ x, scalarKatoTail V n x * W x ^ 2 ∂μ := by
        rw [integral_add (hi2.const_mul _) htw, integral_const_mul]
      _ ≤ (n : ℝ) * A + Real.sqrt (∫ x, scalarKatoTail V n x ^ 2 ∂μ) *
          Real.sqrt (∫ x, W x ^ 4 ∂μ) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
          exact integral_mono hi2 hi4 (fun x => scalarKatoSquare_sq_le hlam (f x))
        · exact scalarKato_tail_pairing hV (hW lam hlam) n
  have hx := henergy lam hlam
  have hX : 0 ≤ Real.sqrt (∫ x, W x ^ 4 ∂μ) := Real.sqrt_nonneg _
  have hsmall : 4 * C * Real.sqrt (∫ x, scalarKatoTail V n x ^ 2 ∂μ) < 1 / 2 := by
    apply (lt_div_iff₀ (show 0 < 8 * C by positivity)).mp at hn
    nlinarith
  have hb : Real.sqrt (∫ x, W x ^ 4 ∂μ) ≤ D := by
    dsimp [D]
    nlinarith [mul_le_mul_of_nonneg_left hpair (show 0 ≤ 4 * C by positivity),
      mul_le_mul_of_nonneg_right hsmall.le hX]
  let w : Lp ℝ 4 μ := (hW lam hlam).toLp W
  have he : w =ᵐ[μ] W := MemLp.coeFn_toLp _
  have hnorm : ‖w‖ ^ 2 ≤ D := by
    rw [scalarLp_four_norm_sq]
    have hi : (∫ x, w x ^ 4 ∂μ) = ∫ x, W x ^ 4 ∂μ :=
      integral_congr_ae (he.fun_comp fun r : ℝ => r ^ 4)
    rwa [hi]
  have hnw : ‖w‖ ≤ D + 1 := by nlinarith [norm_nonneg w, sq_nonneg (‖w‖ - 1)]
  have hen : eLpNorm W 4 μ = ENNReal.ofReal ‖w‖ := by
    rw [← eLpNorm_congr_ae he, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top w)]
  rw [hen]
  exact ENNReal.ofReal_le_ofReal hnw

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact weak minimum principle in the actual H1 space. A smooth
bounded monotone test detects every negative value without presupposing
pointwise second derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

omit [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ] in
theorem scalarWeakMinimum_inner (a b : ScalarL2 g μ) :
    inner ℝ a b = ∫ e, a e * b e ∂μ := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply', conj_trivial]

/-- Strict negativity of the weak Laplacian wherever the scalar value is
negative forces nonnegativity almost everywhere. -/
theorem scalarH1_nonneg_of_negative_source (d : ParallelMetricData g μ)
    (u : scalarH1 d) (F : ScalarL2 g μ)
    (heq : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ F (scalarH1Value d v)))
    (hneg : ∀ᵐ e ∂μ, scalarH1Value d u e < 0 → F e < 0) :
    ∀ᵐ e ∂μ, 0 ≤ scalarH1Value d u e := by
  obtain ⟨D, hD⟩ := scalarNegativeTest_deriv_bound
  obtain ⟨v, hv, hgrad⟩ := scalarH1_compose_exists_of_deriv_bound d
    scalarNegativeTest scalarNegativeTest_smooth scalarNegativeTest_zero hD u
  have hG (i : Fin 4) : 0 ≤ inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v) := by
    rw [scalarWeakMinimum_inner]
    apply integral_nonneg_of_ae
    filter_upwards [hgrad i] with e he
    change 0 ≤ scalarH1Gradient d i u e * scalarH1Gradient d i v e
    rw [he]
    have h := scalarNegativeTest_deriv_nonneg (scalarH1Value d u e)
    convert mul_nonneg h (sq_nonneg (scalarH1Gradient d i u e)) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hp : ∀ᵐ e ∂μ, 0 ≤ F e * scalarH1Value d v e := by
    filter_upwards [hneg, hv] with e he hve
    rw [hve]
    by_cases hu : scalarH1Value d u e < 0
    · exact mul_nonneg_of_nonpos_of_nonpos (he hu).le (scalarNegativeTest_nonpos _)
    · rw [scalarNegativeTest_eq_zero (le_of_not_gt hu), mul_zero]
  have hint : Integrable (fun e => F e * scalarH1Value d v e) μ :=
    (Lp.memLp F).integrable_mul (Lp.memLp (scalarH1Value d v))
  have hi : (∫ e, F e * scalarH1Value d v e ∂μ) = 0 := by
    have h := heq v
    rw [scalarWeakMinimum_inner] at h
    have hsum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hG i)
    have hpos := integral_nonneg_of_ae hp
    linarith
  have hz := (integral_eq_zero_iff_of_nonneg_ae hp hint).mp hi
  filter_upwards [hneg, hv, hz] with e he hve hze
  by_contra hu
  have hu' : scalarH1Value d u e < 0 := lt_of_not_ge hu
  have hpos := mul_pos_of_neg_of_neg (he hu') (scalarNegativeTest_neg hu')
  rw [hve] at hze
  exact (ne_of_gt hpos) hze

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M]

/-- A continuous base representative which is nonnegative almost everywhere
on the canonical frames is nonnegative at every base point. -/
theorem scalar_continuous_base_nonneg_of_frame_ae (g : SmoothMetric M)
    (o : FrameOrientation g) (u : M → ℝ) (hu : Continuous u)
    (hae : ∀ᵐ e ∂canonicalFrameMeasure g o, 0 ≤ u e.base) : ∀ x, 0 ≤ u x := by
  let := normalizedVolume_isOpenPosMeasure g
  have hb : ∀ᵐ x ∂normalizedVolume g, 0 ≤ u x := by
    rw [← (canonicalFrameMeasure_base g o).map_eq]
    exact (ae_map_iff (canonicalFrameMeasure_base g o).measurable.aemeasurable
      (isClosed_le continuous_const hu).measurableSet).mpr hae
  have heq : (fun x => min (u x) 0) =ᵐ[normalizedVolume g] fun _ => (0 : ℝ) := by
    filter_upwards [hb] with x hx
    exact min_eq_right hx
  have hfun := Measure.eq_of_ae_eq heq (hu.min continuous_const) continuous_const
  intro x
  exact min_eq_right_iff.mp (congrFun hfun x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Equality in the Weyl norm gap forces its continuous norm to be one.
The equality argument uses only the two limiting scalar moments. -/
namespace PositiveEinsteinFour.Geometry
open MeasureTheory Filter Set
open scoped _root_.Topology
noncomputable section
variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω] [PreconnectedSpace Ω]
  [Nonempty Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] [Measure.IsOpenPosMeasure μ]

theorem weyl_gap_equality_constant (v : C(Ω, ℝ)) (hv : ∀ x, 0 ≤ v x)
    (hnorm : (∫ x, v x ^ 2 ∂μ) = 1)
    (hgap : Real.sqrt (∫ x, ((v x ^ 2) ^ (1 / 3 : ℝ)) ^ 2 ∂μ) ≤
      ∫ x, v x * (v x ^ 2) ^ (1 / 3 : ℝ) ∂μ) : ∀ x, v x = 1 := by
  let u : C(Ω, ℝ) := ⟨fun x => (v x ^ 2) ^ (1 / 3 : ℝ),
    (v.continuous.pow 2).rpow_const (fun _ => Or.inr (by norm_num))⟩
  let A := ∫ x, u x ^ 2 ∂μ
  let c := Real.sqrt A
  have hi (f : C(Ω, ℝ)) : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hun (x : Ω) : 0 ≤ u x := Real.rpow_nonneg (sq_nonneg _) _
  have hA : 0 ≤ A := integral_nonneg (fun x => sq_nonneg (u x))
  have hc : c ^ 2 = A := Real.sq_sqrt hA
  have hcs : (∫ x, v x * u x ∂μ) ≤ c := by
    have hvLp : MemLp (fun x => v x) (ENNReal.ofReal (2 : ℝ)) μ :=
      v.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have huLp : MemLp (fun x => u x) (ENNReal.ofReal (2 : ℝ)) μ :=
      u.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall hv) (Filter.Eventually.of_forall hun)
      hvLp huLp
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, hnorm, Real.sqrt_one, one_mul] using h
  have hI : (∫ x, v x * u x ∂μ) = c := le_antisymm hcs hgap
  have hz : (∫ x, (c * v x - u x) ^ 2 ∂μ) = 0 := by
    calc
      _ = c ^ 2 * (∫ x, v x ^ 2 ∂μ) -
          2 * c * (∫ x, v x * u x ∂μ) + ∫ x, u x ^ 2 ∂μ := by
        have hpoint : (fun x => (c * v x - u x) ^ 2) =
            fun x => c ^ 2 * v x ^ 2 - (2 * c) * (v x * u x) + u x ^ 2 := by
          funext x; ring
        have hvI : Integrable (fun x => v x ^ 2) μ :=
          (v.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        have huI : Integrable (fun x => u x ^ 2) μ :=
          (u.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        have hvuI : Integrable (fun x => v x * u x) μ :=
          (v.continuous.mul u.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        rw [hpoint]
        calc
          _ = (∫ x, c ^ 2 * v x ^ 2 - (2 * c) * (v x * u x) ∂μ) +
              ∫ x, u x ^ 2 ∂μ :=
            integral_add ((hvI.const_mul (c ^ 2)).sub (hvuI.const_mul (2 * c))) huI
          _ = ((∫ x, c ^ 2 * v x ^ 2 ∂μ) -
              ∫ x, (2 * c) * (v x * u x) ∂μ) + ∫ x, u x ^ 2 ∂μ :=
            congrArg (fun z => z + ∫ x, u x ^ 2 ∂μ)
              (integral_sub (hvI.const_mul (c ^ 2)) (hvuI.const_mul (2 * c)))
          _ = _ := by rw [integral_const_mul, integral_const_mul]

      _ = 0 := by
        rw [hnorm, hI]
        change c ^ 2 * 1 - 2 * c * c + A = 0
        nlinarith only [hc]
  have hrel (x : Ω) : c * v x = u x := by
    have hcont : Continuous (fun x => (c * v x - u x) ^ 2) :=
      ((continuous_const.mul v.continuous).sub u.continuous).pow 2
    by_contra h
    have hp := integral_pos_of_integrable_nonneg_nonzero (μ := μ) hcont
      (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (fun x => sq_nonneg (c * v x - u x))
      (pow_ne_zero 2 (sub_ne_zero.mpr h))
    linarith
  have hfinite : (range v).Finite := by
    apply (Set.toFinite ({0, 1 / c ^ 3} : Set ℝ)).subset
    rintro _ ⟨x,rfl⟩
    by_cases hx : v x = 0
    · simp [hx]
    · have hu : u x ^ 3 = v x ^ 2 := by
        dsimp only [u, ContinuousMap.coe_mk]
        rw [← Real.rpow_mul_natCast (sq_nonneg _)]
        norm_num
      rw [← hrel x] at hu
      have hf : v x ^ 2 * (c ^ 3 * v x - 1) = 0 := by nlinarith only [hu]
      have he : c ^ 3 * v x = 1 := sub_eq_zero.mp
        ((mul_eq_zero.mp hf).resolve_left (pow_ne_zero 2 hx))
      have hc0 : c ^ 3 ≠ 0 := by intro h; rw [h,zero_mul] at he; norm_num at he
      have hx' : v x = 1 / c ^ 3 := (eq_div_iff hc0).mpr (by linarith only [he])
      simp [hx']
  have hsub : (range v).Subsingleton := by
    by_contra h
    exact hfinite.not_infinite ((isPreconnected_range v.continuous).infinite_of_nontrivial
      (not_subsingleton_iff.mp h))
  let x₀ : Ω := Classical.choice inferInstance
  have hconst (x : Ω) : v x = v x₀ := hsub ⟨x,rfl⟩ ⟨x₀,rfl⟩
  have hsquare : v x₀ ^ 2 = 1 := by simpa only [hconst, integral_const, probReal_univ, smul_eq_mul, one_mul] using hnorm
  intro x
  rw [hconst]
  nlinarith [hv x₀]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Once positivity is known, real powers preserve the actual H1 closure.
A compact positive range permits the bounded smooth chain rule at every
real exponent, including negative exponents used in the rigidity argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

section CompactRange

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

theorem scalar_positive_continuous_range (f : X → ℝ) (hf : Continuous f)
    (hpos : ∀ x, 0 < f x) :
    ∃ a B : ℝ, 0 < a ∧ 0 ≤ B ∧ ∀ x, f x ∈ Icc a B := by
  obtain ⟨x₀, _, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  obtain ⟨x₁, _, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf.continuousOn
  exact ⟨f x₀, f x₁, hpos x₀, (hpos x₁).le,
    fun x => ⟨hmin (mem_univ x), hmax (mem_univ x)⟩⟩

end CompactRange

end
end PositiveEinsteinFour.Geometry
end


section

/-! Barrier comparison for the actual H1 solution with a continuous base
representative. Only the barrier is required to be smooth. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

local instance weakBarrier_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Inverting the base-coordinate family while retaining the initial
frame as a parameter. The spatial derivative alone supplies invertibility. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilyBaseAugment (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (z : HeatRadialFrameSpace) : HeatRadialFrameSpace := ((P z).1, z.2)

theorem heatFamilyBaseAugment_local_inverse
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (q : CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 12 P (0, q)) (A : FourSpace ≃L[ℝ] FourSpace)
    (hA : HasFDerivAt (fun x : FourSpace => (P (x, q)).1) (A : FourSpace →L[ℝ] FourSpace) 0) :
    ∃ H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace,
      (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P ∧
      ((0 : FourSpace), q) ∈ H.source ∧
      ContDiffAt ℝ 12 H.symm (heatFamilyBaseAugment P (0, q)) := by
  let B := (ContinuousLinearMap.fst ℝ FourSpace Mat4).comp
    ((fderiv ℝ P (0, q)).comp (ContinuousLinearMap.inr ℝ FourSpace CoordinateFrameSpace))
  let E : HeatRadialFrameSpace ≃L[ℝ] HeatRadialFrameSpace :=
    (ContinuousLinearEquiv.prodComm ℝ FourSpace CoordinateFrameSpace).trans
      (((ContinuousLinearEquiv.refl ℝ CoordinateFrameSpace).skewProd A B).trans
        (ContinuousLinearEquiv.prodComm ℝ CoordinateFrameSpace FourSpace))
  have hdP := (hP.differentiableAt (by norm_num)).hasFDerivAt
  have hd : HasFDerivAt (heatFamilyBaseAugment P)
      (((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (0, q))).prod
        (ContinuousLinearMap.snd ℝ FourSpace CoordinateFrameSpace)) (0, q) :=
    hdP.fst.prodMk hasFDerivAt_snd
  have hfirst : HasFDerivAt (fun z : HeatRadialFrameSpace => (P z).1)
      ((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (0, q))) (0, q) := hdP.fst
  have harg : HasFDerivAt (fun x : FourSpace => (x, q))
      ((ContinuousLinearMap.id ℝ FourSpace).prod
        (0 : FourSpace →L[ℝ] CoordinateFrameSpace)) 0 :=
    (hasFDerivAt_id (0 : FourSpace)).prodMk (hasFDerivAt_const q 0)
  have hs : HasFDerivAt (fun x : FourSpace => (P (x, q)).1)
      (((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (0, q))).comp
        ((ContinuousLinearMap.id ℝ FourSpace).prod
          (0 : FourSpace →L[ℝ] CoordinateFrameSpace))) 0 := HasFDerivAt.comp (f := fun x : FourSpace => (x, q))
      (g := fun z : HeatRadialFrameSpace => (P z).1) 0 hfirst harg
  have hsame := hs.unique hA
  have hsp (v : FourSpace) : (fderiv ℝ P (0, q) (v, 0)).1 = A v :=
    congrArg (fun L : FourSpace →L[ℝ] FourSpace => L v) hsame
  have hE : (((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P (0, q))).prod
        (ContinuousLinearMap.snd ℝ FourSpace CoordinateFrameSpace)) =
      (E : HeatRadialFrameSpace →L[ℝ] HeatRadialFrameSpace) := by
    apply ContinuousLinearMap.ext
    intro z
    change ((fderiv ℝ P (0, q) z).1, z.2) = (A z.1 + B z.2, z.2)
    have hz : z = (z.1, (0 : CoordinateFrameSpace)) + ((0 : FourSpace), z.2) := by simp
    apply Prod.ext
    · change (fderiv ℝ P (0, q) z).1 = A z.1 + B z.2
      calc
        (fderiv ℝ P (0, q) z).1 =
            (fderiv ℝ P (0, q) ((z.1, 0) + (0, z.2))).1 := congrArg (fun w : HeatRadialFrameSpace => (fderiv ℝ P (0, q) w).1) hz
        _ = (fderiv ℝ P (0, q) (z.1, 0)).1 +
            (fderiv ℝ P (0, q) (0, z.2)).1 := by rw [map_add]; rfl
        _ = A z.1 + B z.2 := by rw [hsp]; rfl
    · rfl
  rw [hE] at hd
  have hf : ContDiffAt ℝ 12 (heatFamilyBaseAugment P) (0, q) :=
    hP.fst.prodMk contDiffAt_snd
  let H := hf.toOpenPartialHomeomorph (heatFamilyBaseAugment P) hd (by norm_num)
  refine ⟨H, rfl, hf.mem_toOpenPartialHomeomorph_source hd (by norm_num), ?_⟩
  exact hf.to_localInverse hd (by norm_num)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Slicing the joint inverse while holding the initial frame fixed gives
an actual open coordinate chart, with an explicit inverse. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilySliceChart (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace)
    (hH : (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P)
    (q : CoordinateFrameSpace) : OpenPartialHomeomorph FourSpace FourSpace := by
  have he (z : HeatRadialFrameSpace) : H z = ((P z).1, z.2) := congrFun hH z
  have hi (z : HeatRadialFrameSpace) (hz : z ∈ H.target) : (H.symm z).2 = z.2 := by
    have hh := congrArg Prod.snd (H.right_inv hz)
    rw [he] at hh
    exact hh
  have hip (y : FourSpace) (hy : (y, q) ∈ H.target) :
      ((H.symm (y, q)).1, q) = H.symm (y, q) := by
    apply Prod.ext
    · rfl
    · exact (hi (y, q) hy).symm
  exact {
    toFun := fun x => (P (x, q)).1
    invFun := fun y => (H.symm (y, q)).1
    source := {x | (x, q) ∈ H.source}
    target := {y | (y, q) ∈ H.target}
    map_source' := fun x hx => by
      have hh := H.map_source hx
      rw [he] at hh
      exact hh
    map_target' := fun y hy => by
      change ((H.symm (y, q)).1, q) ∈ H.source
      rw [hip y hy]
      exact H.map_target hy
    left_inv' := fun x hx => by
      have hh := congrArg Prod.fst (H.left_inv hx)
      rw [he] at hh
      exact hh
    right_inv' := fun y hy => by
      have hh := congrArg Prod.fst (H.right_inv hy)
      rw [he, ← hip y hy] at hh
      exact hh
    open_source := H.open_source.preimage (continuous_id.prodMk continuous_const)
    open_target := H.open_target.preimage (continuous_id.prodMk continuous_const)
    continuousOn_toFun := by
      have hc : ContinuousOn (fun x : FourSpace => H (x, q)) {x | (x, q) ∈ H.source} :=
        H.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun x hx => hx)
      simpa only [hH, heatFamilyBaseAugment] using hc.fst
    continuousOn_invFun :=
      (H.symm.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun y hy => hy)).fst }

theorem heatFamilySliceChart_inverse_regular
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace)
    (hH : (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P)
    (q : CoordinateFrameSpace) (x : FourSpace)
    (hi : ContDiffAt ℝ 4 H.symm ((P (x, q)).1, q)) :
    ContDiffAt ℝ 4 (heatFamilySliceChart P H hH q).symm (P (x, q)).1 := by
  change ContDiffAt ℝ 4 (fun y => (H.symm (y, q)).1) (P (x, q)).1
  exact (ContDiffAt.comp (f := fun y : FourSpace => (y, q)) (g := H.symm)
    (P (x, q)).1 hi (contDiffAt_id.prodMk contDiffAt_const)).fst

theorem heatFamilySliceChart_uniform
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (q₀ : CoordinateFrameSpace)
    (H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace)
    (hH : (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P)
    (h0 : ((0 : FourSpace), q₀) ∈ H.source)
    (hP : ContDiffAt ℝ 12 P (0, q₀))
    (hi : ContDiffAt ℝ 12 H.symm (heatFamilyBaseAugment P (0, q₀))) :
    ∃ r > (0 : ℝ), ∀ q ∈ ball q₀ r, ∀ x ∈ ball (0 : FourSpace) r,
      x ∈ (heatFamilySliceChart P H hH q).source ∧
      ContDiffAt ℝ 4 (heatFamilySliceChart P H hH q).symm (P (x, q)).1 := by
  have hp : ContinuousAt (heatFamilyBaseAugment P) (0, q₀) :=
    hP.continuousAt.fst.prodMk continuousAt_snd
  have hreg := hp.tendsto.eventually ((hi.of_le (show (4 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num))
  have hn : ∀ᶠ z in 𝓝 ((0 : FourSpace), q₀), z ∈ H.source ∧
      ContDiffAt ℝ 4 H.symm (heatFamilyBaseAugment P z) :=
    Filter.Eventually.and (H.open_source.mem_nhds h0) hreg
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, ?_⟩
  intro q hq x hx
  have hmem : (x, q) ∈ ball ((0 : FourSpace), q₀) r := by
    change max (dist x 0) (dist q q₀) < r
    exact max_lt hx hq
  obtain ⟨hs, hdiff⟩ := hb hmem
  exact ⟨hs, heatFamilySliceChart_inverse_regular P H hH q x hdiff⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer a slice of the joint inverse to the manifold on a prescribed
common ball. No new inverse or regularity assumption enters the geometry. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatFamily_manifold_chart {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hpoint : D.point = fun x => P (x, frameCoordinateState g c e))
    (H : OpenPartialHomeomorph HeatRadialFrameSpace HeatRadialFrameSpace)
    (hH : (H : HeatRadialFrameSpace → HeatRadialFrameSpace) = heatFamilyBaseAugment P)
    (r : ℝ) (_hr : 0 < r) (hrD : r ≤ D.radius)
    (hsource : ∀ x ∈ ball (0 : FourSpace) r,
      frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hs : ∀ x ∈ ball (0 : FourSpace) r,
      x ∈ (heatFamilySliceChart P H hH (frameCoordinateState g c e)).source)
    (hi : ∀ x ∈ ball (0 : FourSpace) r, ContDiffAt ℝ 4
      (heatFamilySliceChart P H hH (frameCoordinateState g c e)).symm
        (P (x, frameCoordinateState g c e)).1) :
    ∃ C : OpenPartialHomeomorph FourSpace M,
      C.source = ball 0 r ∧ EqOn C (frameExponential g o e) C.source ∧
      C.target ⊆ (chartAt FourSpace c).source ∧ ContMDiffOn I4 I4 4 C.symm C.target := by
  let q := frameCoordinateState g c e
  let S₀ := heatFamilySliceChart P H hH q
  let S := S₀.restrOpen (ball 0 r) isOpen_ball
  have hS : S.source = ball 0 r := inter_eq_right.mpr (fun x hx => hs x hx)
  have hxD {x : FourSpace} (hx : x ∈ ball 0 r) : x ∈ ball 0 D.radius :=
    ball_subset_ball hrD hx
  have hchart {x : FourSpace} (hx : x ∈ ball 0 r) : S x ∈ (chartAt FourSpace c).target := by
    have hh := D.in_chart x (hxD hx)
    change (P (x, q)).1 ∈ (chartAt FourSpace c).target
    simpa only [hpoint] using hh
  let C := S.trans (chartAt FourSpace c).symm
  have hC : C.source = ball 0 r := by
    apply Set.ext
    intro x
    change (x ∈ S.source ∧ S x ∈ (chartAt FourSpace c).target) ↔ x ∈ ball 0 r
    rw [hS]
    exact ⟨And.left, fun hx => ⟨hx, hchart hx⟩⟩
  have heq : EqOn C (frameExponential g o e) C.source := by
    intro x hx
    have hb : x ∈ ball 0 r := hC ▸ hx
    have hd := D.exponential x (hxD hb)
    rw [hpoint] at hd
    change (chartAt FourSpace c).symm (P (x, q)).1 = _
    rw [hd]
    exact (chartAt FourSpace c).left_inv (hsource x hb)
  have htarget : C.target ⊆ (chartAt FourSpace c).source := by
    intro y hy
    let x := C.symm y
    have hx : x ∈ ball 0 r := hC ▸ C.map_target hy
    have h := (chartAt FourSpace c).map_target (hchart hx)
    change C x ∈ (chartAt FourSpace c).source at h
    rwa [C.right_inv hy] at h
  refine ⟨C, hC, heq, htarget, ?_⟩
  intro y hy
  let x := C.symm y
  have hx : x ∈ ball 0 r := hC ▸ C.map_target hy
  have hexp : frameExponential g o e x = y := (heq (C.map_target hy)).symm.trans (C.right_inv hy)
  have hd : (P (x, q)).1 = chartAt FourSpace c y := by
    have hh := D.exponential x (hxD hx)
    simpa only [hpoint, hexp] using hh
  have hInv : ContDiffAt ℝ 4 S₀.symm (chartAt FourSpace c y) := hd ▸ hi x hx
  have hch : ContMDiffAt I4 I4 4 (chartAt FourSpace c) y :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) (htarget hy)
  have hh := hInv.contMDiffAt.comp y hch
  change ContMDiffAt I4 I4 4 C.symm y at hh
  exact hh.contMDiffWithinAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! The kernel of the actual smooth scalar Laplacian.  The proof uses
the actual parallel-flow Green formula, full support of base volume, and
constancy along the complete geodesics.  No elliptic kernel theorem is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem scalar_eq_along_parallelFlow_of_gradient_eq_zero (g : SmoothMetric M)
    {a : M → ℝ} (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a)
    (hgrad : ∀ e : FrameBundle g, ∀ i, scalarGradient g a e i = 0)
    (e : FrameBundle g) (i : Fin 4) (t : ℝ) :
    a (parallelFrameFlowMap g i t e).base = a e.base := by
  have hd (r : ℝ) : HasDerivAt (fun s => a (parallelFrameFlowMap g i s e).base) 0 r := by
    simpa only [hgrad] using actual_scalarValue_parallel_derivative g ha
      (fun s => parallelFrameFlowMap g i s e) r i
      (parallelFrameFlowMap_curve_continuous g i e).continuousAt
      (parallelFrameFlowMap_primitive g i e r)
  have h := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t 0
  simpa only [parallelFrameFlowMap_zero] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The zeroth de Rham space is exactly the constant smooth functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

abbrev ZeroFormDeRhamCohomology (g : SmoothMetric M) :=
  (smoothScalarDifferentialLinear g).ker

local instance instAddCommGroupSubtypeSmoothScalarMemSubmoduleRealZeroFormDeRhamCohomology_r9d9562_1 : AddCommGroup (ZeroFormDeRhamCohomology g) := Submodule.addCommGroup _
def scalarConstantLinear : ℝ →ₗ[ℝ] SmoothScalar (M := M) where
  toFun := smoothScalarConst
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The reverse area inequality on an injective exponential ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [MeasurableSpace M] [BorelSpace M] [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def exponentialBallAreaMeasure (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (r : ℝ) : Measure M :=
  riemannianChartFactor • Measure.map (frameExponential g o e)
    ((volume.restrict (ball 0 r)).withDensity
      (fun v => ENNReal.ofReal (frameExponentialJacobian g o e v)))

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Averaging the actual polar bound over the canonical frame probability.
Right invariance under each oriented rotation removes the angular average;
Tonelli then puts the time and frame integrals in the manuscript's order. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Jacobi MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance instIsProbabilityMeasureDirectionsSphereMeasure_5_r9d9562_1 : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability
def actualRadialMass (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : ℝ≥0∞ :=
  ∫⁻ r in Icc (0 : ℝ) Real.pi,
    ENNReal.ofReal (actualRegularJacobi g hRic e r).truncatedDensity

end
end PositiveEinsteinFour.Geometry
end


section

/-! Discharge of the published polar-volume input for the actual metric,
actual Jacobi solution and canonical frame measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Jacobi MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem actualJacobi_average_nonneg (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
      ∂canonicalFrameMeasure g o := by
  apply integral_nonneg
  intro e
  exact (actualRegularJacobi g hRic e r).truncatedDensity_nonneg hr

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exponential barrier and its actual metric Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def smoothScalarExponentialBarrier (a : SmoothScalar (M := M)) (k c : ℝ) :
    SmoothScalar (M := M) :=
  smoothScalarCompose (fun r => Real.exp (-k * r) - c)
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).sub contDiff_const) a

theorem smoothScalarExponentialBarrier_gradient (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (k c : ℝ) (e : FrameBundle g) (i : Fin 4) :
    scalarGradient g (smoothScalarExponentialBarrier a k c).val e i =
      -k * Real.exp (-k * a.val e.base) * scalarGradient g a.val e i := by
  rw [smoothScalarExponentialBarrier, smoothScalarCompose_gradient d]
  have hd : HasDerivAt (fun r : ℝ => Real.exp (-k * r) - c)
      (Real.exp (-k * a.val e.base) * -k) (a.val e.base) :=
    by simpa only [id_eq, mul_one] using
      (((hasDerivAt_id (a.val e.base)).const_mul (-k)).exp).sub_const c
  rw [hd.deriv]
  ring

theorem smoothScalarExponentialBarrier_hessian (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (k c : ℝ) (e : FrameBundle g) (i j : Fin 4) :
    scalarHessian g (smoothScalarExponentialBarrier a k c).val e i j =
      Real.exp (-k * a.val e.base) *
        (k ^ 2 * scalarGradient g a.val e i * scalarGradient g a.val e j -
          k * scalarHessian g a.val e i j) := by
  let sa := Classical.choice (d.scalarCalculus.toPetersenInput a.val a.property)
  let b := smoothScalarExponentialBarrier a k c
  let sb := Classical.choice (d.scalarCalculus.toPetersenInput b.val b.property)
  obtain ⟨f, hf⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
  have h := sb.derivativeGradient i j 0 f
  have h' := (((sa.derivativeValue i 0 f).const_mul (-k)).exp.const_mul (-k)).mul
    (sa.derivativeGradient i j 0 f)
  have heq : (fun t => scalarGradient g b.val ((d.toMetricGreenData.flow i).map t f) j) =
      (fun t => -k * Real.exp (-k * a.val ((d.toMetricGreenData.flow i).map t f).base) *
        scalarGradient g a.val ((d.toMetricGreenData.flow i).map t f) j) :=
    funext (fun t => smoothScalarExponentialBarrier_gradient d a k c _ j)
  rw [heq] at h
  have hu := h.unique h'
  rw [hf] at hu
  change scalarHessian g (smoothScalarExponentialBarrier a k c).val e i j = _ at hu
  rw [hu]
  ring

theorem smoothScalarExponentialBarrier_laplacian (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) (k c : ℝ) (e : FrameBundle g) :
    scalarLaplacian g (smoothScalarExponentialBarrier a k c).val e =
      Real.exp (-k * a.val e.base) *
        (k ^ 2 * (∑ i, scalarGradient g a.val e i ^ 2) - k * scalarLaplacian g a.val e) := by
  simp only [scalarLaplacian, smoothScalarExponentialBarrier_hessian d]
  calc
    _ = Real.exp (-k * a.val e.base) *
        (∑ i, (k ^ 2 * scalarGradient g a.val e i ^ 2 - k * scalarHessian g a.val e i i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Choice and verification of the large parameter in the exponential
barrier on an annulus where the radial differential does not vanish. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem scalar_exponential_barrier_strict (d : ParallelMetricData g μ)
    (a : SmoothScalar (M := M)) {k c η B c₀ : ℝ} (hk : 0 ≤ k) (hc : 0 ≤ c)
    (hc₀ : 0 ≤ c₀) (e : FrameBundle g)
    (hgrad : η ≤ ∑ i, scalarGradient g a.val e i ^ 2)
    (hlap : scalarLaplacian g a.val e ≤ B)
    (hlarge : c₀ < k ^ 2 * η - k * B) :
    c₀ * (smoothScalarExponentialBarrier a k c).val e.base <
      scalarLaplacian g (smoothScalarExponentialBarrier a k c).val e := by
  have hQ := mul_le_mul_of_nonneg_left hgrad (sq_nonneg k)
  have hD := mul_le_mul_of_nonneg_left hlap hk
  have hinside : c₀ < k ^ 2 * (∑ i, scalarGradient g a.val e i ^ 2) -
      k * scalarLaplacian g a.val e :=
    hlarge.trans_le (sub_le_sub hQ hD)
  rw [smoothScalarExponentialBarrier_laplacian d]
  change c₀ * (Real.exp (-k * a.val e.base) - c) < _
  calc
    _ ≤ c₀ * Real.exp (-k * a.val e.base) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ hc) hc₀
    _ = Real.exp (-k * a.val e.base) * c₀ := mul_comm _ _
    _ < _ := mul_lt_mul_of_pos_left hinside (Real.exp_pos _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine smooth global radial function that agrees with squared
Euclidean chart distance on the inner ball. Outside that ball its value
stays above the inner squared radius, so it can localize a Hopf barrier. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M]

def scalarRadialChartCorrection (y : FourSpace) (χ : ContDiffBump y) : FourSpace → ℝ :=
  fun z => χ z * (‖z - y‖ ^ 2 - χ.rOut ^ 2)

theorem scalarRadialChartCorrection_smooth (y : FourSpace) (χ : ContDiffBump y) :
    ContDiff ℝ ∞ (scalarRadialChartCorrection y χ) := by
  have h : ContDiff ℝ ∞ (fun z : FourSpace => z - y) :=
    contDiff_id.sub contDiff_const
  exact χ.contDiff.mul ((h.norm_sq ℝ).sub contDiff_const)

theorem scalarRadialChartCorrection_compact (y : FourSpace) (χ : ContDiffBump y) :
    HasCompactSupport (scalarRadialChartCorrection y χ) := χ.hasCompactSupport.mul_right

omit [IsManifold I4 ∞ M] [T2Space M] in
theorem scalarRadialChartCorrection_support (c : M) (y : FourSpace)
    (χ : ContDiffBump y) (hs : closedBall y χ.rOut ⊆ (chartAt FourSpace c).target) :
    tsupport (scalarRadialChartCorrection y χ) ⊆ (chartAt FourSpace c).target := by
  change tsupport ((χ : FourSpace → ℝ) * (fun z => ‖z - y‖ ^ 2 - χ.rOut ^ 2)) ⊆ _
  exact tsupport_mul_subset_left.trans (by simpa only [χ.tsupport_eq] using hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous weak supersolution is positive inside a radial barrier.
The comparison barrier stays positive at the alleged zero, so no
pointwise derivative of the weak solution is needed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance continuousRadial_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! A positive Euclidean ball tangent to the zero set near a boundary
point. The radius is obtained from a compact nearest-point argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped _root_.Topology

noncomputable section

theorem scalar_euclidean_positive_contact_ball
    (f : FourSpace → ℝ) (x y : FourSpace) {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (closedBall x (R / 2)))
    (hn : ∀ z ∈ closedBall x (R / 2), 0 ≤ f z)
    (hx : f x = 0) (hy : dist y x < R / 4) (hfy : 0 < f y) :
    ∃ (r : ℝ) (z : FourSpace), 0 < r ∧ r ≤ dist y x ∧ dist z y = r ∧ f z = 0 ∧
      closedBall y r ⊆ ball x (R / 2) ∧ ∀ w ∈ ball y r, 0 < f w := by
  let Z := closedBall x (R / 2) ∩ f ⁻¹' Iic 0
  have hZ : IsCompact Z :=
    hf.lowerSemicontinuousOn.isCompact_inter_preimage_Iic (isCompact_closedBall _ _) 0
  have hxZ : x ∈ Z := by
    exact ⟨mem_closedBall_self (by positivity), by
      simpa only [mem_preimage, mem_Iic, hx] using (le_refl (0 : ℝ))⟩
  obtain ⟨z, hz, hmin⟩ := hZ.exists_isMinOn ⟨x, hxZ⟩
    (show Continuous (fun z : FourSpace => dist z y) from
      continuous_id.dist continuous_const).continuousOn
  let r := dist z y
  have hr : 0 < r := by
    apply dist_pos.mpr
    intro he
    have hh : f y ≤ 0 := by simpa only [he, mem_preimage, mem_Iic] using hz.2
    exact (not_le_of_gt hfy) hh
  have hrx : r ≤ dist y x := by
    exact (hmin hxZ).trans_eq (dist_comm x y)
  have hsub : closedBall y r ⊆ ball x (R / 2) := by
    intro w hw
    have hw' : dist w y ≤ r := mem_closedBall.mp hw
    have ht := dist_triangle w y x
    apply mem_ball.mpr
    linarith
  refine ⟨r, z, hr, hrx, rfl, le_antisymm hz.2 (hn z hz.1), hsub, ?_⟩
  intro w hw
  have hwK : w ∈ closedBall x (R / 2) := ball_subset_closedBall (hsub (ball_subset_closedBall hw))
  by_contra hbad
  have hwZ : w ∈ Z := ⟨hwK, le_of_not_gt hbad⟩
  have hle : r ≤ dist w y := hmin hwZ
  exact (not_lt_of_ge hle) (mem_ball.mp hw)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Absolute coordinate estimates for an arbitrary orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_chart_gram_bounded (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ j k, |chartGramMatrix g c 1 z j k| ≤ C := by
  have hb (j k : Fin 4) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ z ∈ K, |chartGramMatrix g c 1 z j k| ≤ B := by
    have hc : ContinuousOn (fun z => chartGramMatrix g c 1 z j k) K :=
      fun z hz => (chartGramMatrix_contDiffAt g c 1 z (hKt hz) j k).continuousAt.continuousWithinAt
    obtain ⟨B, hB⟩ := (hK.image_of_continuousOn hc).isBounded.exists_norm_le
    exact ⟨max B 0, le_max_right _ _, fun z hz =>
      (hB _ ⟨z, hz, rfl⟩).trans (le_max_left _ _)⟩
  choose B hB0 hB using hb
  refine ⟨∑ j, ∑ k, B j k,
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hB0 j k)), ?_⟩
  intro z hz j k
  exact (hB j k z hz).trans
    ((Finset.single_le_sum (fun k _ => hB0 j k) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun k _ => hB0 j k))
        (Finset.mem_univ j)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact annular bounds for the actual smooth radial chart function. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

local instance radialAnnulus_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

omit [T3Space M] in
theorem scalar_positive_annular_gradient_bound (g : SmoothMetric M)
    (q : SmoothScalar (M := M)) {a r : ℝ}
    (hne : ∃ e : FrameBundle g, a ≤ q.val e.base ∧ q.val e.base ≤ r)
    (hpos : ∀ e : FrameBundle g, a ≤ q.val e.base → q.val e.base ≤ r →
      0 < ∑ i, scalarGradient g q.val e i ^ 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ e : FrameBundle g, a ≤ q.val e.base → q.val e.base ≤ r →
      η ≤ ∑ i, scalarGradient g q.val e i ^ 2 := by
  let K : Set (FrameBundle g) := {e | a ≤ q.val e.base ∧ q.val e.base ≤ r}
  have hq : Continuous (fun e : FrameBundle g => q.val e.base) :=
    q.property.continuous.comp (continuous_frameBase g)
  have hK : IsCompact K :=
    ((isClosed_le continuous_const hq).inter (isClosed_le hq continuous_const)).isCompact
  have hE : Continuous (fun e : FrameBundle g => ∑ i, scalarGradient g q.val e i ^ 2) :=
    continuous_finsetSum _ (fun i _ => (actual_scalarGradient_continuous g q.property i).pow 2)
  obtain ⟨e, he, hmin⟩ := hK.exists_isMinOn hne hE.continuousOn
  exact ⟨_, hpos e he.1 he.2, fun z hz₁ hz₂ => hmin ⟨hz₁, hz₂⟩⟩

omit [T3Space M] in
theorem scalar_laplacian_uniform_upper (g : SmoothMetric M) (q : SmoothScalar (M := M)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ e : FrameBundle g, scalarLaplacian g q.val e ≤ B := by
  have hL : Continuous (fun e : FrameBundle g => scalarLaplacian g q.val e) :=
    continuous_finsetSum _ (fun i _ => actual_scalarHessian_continuous g q.property i i)
  obtain ⟨B, hB⟩ := (isCompact_univ.image hL).isBounded.exists_norm_le
  refine ⟨max B 0, le_max_right _ _, fun e => ?_⟩
  exact (le_abs_self _).trans ((hB _ ⟨e, mem_univ _, rfl⟩).trans (le_max_left _ _))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual local strong minimum principle, using a Euclidean ball
inside one chart and the weak radial barrier. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

local instance localContinuousPositive_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strict positivity of a nonzero nonnegative weak supersolution on the
connected manifold, from the actual chart contact-ball argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [PreconnectedSpace M]

local instance continuousStrongMin_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Strong bounded-times-L2 products for the higher weak derivative limits. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped ENNReal _root_.Topology

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "Linf" => Lp ℝ ∞ (volume : Measure V)

def scalarLinfL2Product : Linf →L[ℝ] L2 →L[ℝ] L2 :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL volume ∞ 2 2

theorem scalarLinfL2Product_coe (f : Linf) (g : L2) :
    scalarLinfL2Product f g =ᵐ[volume] fun x => f x * g x :=
  (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder f g

theorem scalarLinfL2Product_tendsto {f : ℕ → Linf} {g : ℕ → L2} {F : Linf} {G : L2}
    (hf : Tendsto f atTop (𝓝 F)) (hg : Tendsto g atTop (𝓝 G)) :
    Tendsto (fun k => scalarLinfL2Product (f k) (g k)) atTop
      (𝓝 (scalarLinfL2Product F G)) := by
  have hB : Continuous (fun z : Linf × L2 => scalarLinfL2Product z.1 z.2) :=
    scalarLinfL2Product.continuous₂
  simpa only [Function.comp_def] using (hB.tendsto (F, G)).comp (hf.prodMk_nhds hg)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Explicit first and second coordinate derivatives of a compactly
localized scalar composition. These are the formulas whose terms will
converge in L2 in the nonlinear elliptic bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

theorem scalar_partial_scalar_comp (f : FourSpace → ℝ) (φ : ℝ → ℝ) (x : FourSpace)
    (hf : DifferentiableAt ℝ f x) (hφ : DifferentiableAt ℝ φ (f x)) (i : Fin 4) :
    partialDeriv (fun y => φ (f y)) i x = deriv φ (f x) * partialDeriv f i x := by
  have h := hφ.hasDerivAt.comp_hasFDerivAt x hf.hasFDerivAt
  have he := congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) h.fderiv
  simpa only [partialDeriv, _root_.smul_apply, smul_eq_mul, Function.comp_def] using he

theorem scalar_partial_smooth (f : FourSpace → ℝ) (hf : ContDiff ℝ ∞ f) (i : Fin 4) :
    ContDiff ℝ ∞ (fun x => partialDeriv f i x) :=
  (hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := coordinateVector i))

theorem scalar_partial_scalar_comp_second (f : FourSpace → ℝ) (φ : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ) (x : FourSpace) (i j : Fin 4) :
    partialDeriv (fun y => partialDeriv (fun z => φ (f z)) j y) i x =
      deriv (deriv φ) (f x) * partialDeriv f i x * partialDeriv f j x +
        deriv φ (f x) * partialDeriv (fun y => partialDeriv f j y) i x := by
  have hφ' : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hd := hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he (y : FourSpace) := scalar_partial_scalar_comp f φ y hd.differentiableAt
    (hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt j
  simp_rw [he]
  rw [scalar_partial_product (fun y => deriv φ (f y)) (fun y => partialDeriv f j y) x
    (by simpa only [Function.comp_def] using ((hφ'.comp hf).differentiable (by simp)).differentiableAt)
    ((scalar_partial_smooth f hf j).differentiable (by simp)).differentiableAt i,
    scalar_partial_scalar_comp f (deriv φ) x hd.differentiableAt
      (hφ'.differentiable (by simp)).differentiableAt i]

theorem scalar_partial_local_composition (χ f : FourSpace → ℝ) (φ : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ)
    (x : FourSpace) (i : Fin 4) :
    partialDeriv (fun y => χ y * φ (f y)) i x =
      partialDeriv χ i x * φ (f x) + χ x * (deriv φ (f x) * partialDeriv f i x) := by
  rw [scalar_partial_product χ (fun y => φ (f y)) x
    (hχ.differentiable (by simp)).differentiableAt
    (by simpa only [Function.comp_def] using ((hφ.comp hf).differentiable (by simp)).differentiableAt) i,
    scalar_partial_scalar_comp f φ x (hf.differentiable (by simp)).differentiableAt
      (hφ.differentiable (by simp)).differentiableAt i]

theorem scalar_partial_local_composition_second (χ f : FourSpace → ℝ) (φ : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ)
    (x : FourSpace) (i j : Fin 4) :
    partialDeriv (fun y => partialDeriv (fun z => χ z * φ (f z)) j y) i x =
      partialDeriv (fun y => partialDeriv χ j y) i x * φ (f x) +
      partialDeriv χ j x * (deriv φ (f x) * partialDeriv f i x) +
      partialDeriv χ i x * (deriv φ (f x) * partialDeriv f j x) +
      χ x * (deriv (deriv φ) (f x) * partialDeriv f i x * partialDeriv f j x +
        deriv φ (f x) * partialDeriv (fun y => partialDeriv f j y) i x) := by
  let F : FourSpace → ℝ := fun y => φ (f y)
  have hg : ContDiff ℝ ∞ F := by simpa only [F, Function.comp_def] using hφ.comp hf
  have hpχ := scalar_partial_smooth χ hχ j
  have hpF := scalar_partial_smooth F hg j
  have he (y : FourSpace) := scalar_partial_product χ F y
    (hχ.differentiable (by simp)).differentiableAt
    (hg.differentiable (by simp)).differentiableAt j
  change partialDeriv (fun y => partialDeriv (fun z => χ z * F z) j y) i x = _
  simp_rw [he]
  have hadd : partialDeriv (fun y => partialDeriv χ j y * F y + χ y * partialDeriv F j y) i x =
      partialDeriv (fun y => partialDeriv χ j y * F y) i x +
        partialDeriv (fun y => χ y * partialDeriv F j y) i x := by
    have he := congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i))
      (fderiv_fun_add (x := x) ((hpχ.mul hg).differentiable (by simp)).differentiableAt
        ((hχ.mul hpF).differentiable (by simp)).differentiableAt)
    simpa only [partialDeriv, _root_.add_apply] using! he
  rw [hadd, scalar_partial_product (fun y => partialDeriv χ j y) F x
    (hpχ.differentiable (by simp)).differentiableAt
    (hg.differentiable (by simp)).differentiableAt i,
    scalar_partial_product χ (fun y => partialDeriv F j y) x
      (hχ.differentiable (by simp)).differentiableAt
      (hpF.differentiable (by simp)).differentiableAt i]
  dsimp only [F]
  rw [scalar_partial_scalar_comp_second f φ hf hφ x i j,
    scalar_partial_scalar_comp f φ x (hf.differentiable (by simp)).differentiableAt
      (hφ.differentiable (by simp)).differentiableAt i,
    scalar_partial_scalar_comp f φ x (hf.differentiable (by simp)).differentiableAt
      (hφ.differentiable (by simp)).differentiableAt j]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual H1 coordinate jet agrees with the L4 derivatives supplied by H2. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped Manifold ContDiff SchwartzMap ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance cutoffH2_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Fixed real Schwartz multipliers on L2 and actual compact localizations
of a smooth scalar composition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped SchwartzMap ENNReal ContDiff LineDeriv NNReal

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "S" => 𝓢(V, ℝ)

def scalarRealSchwartzMultiply (a : S) : L2 →L[ℝ] L2 :=
  scalarL2BoundedMultiplier a a.continuous.aestronglyMeasurable
    (C := SchwartzMap.seminorm ℝ 0 0 a) (fun x => by
      simpa only [Real.norm_eq_abs] using SchwartzMap.norm_le_seminorm ℝ a x)

theorem scalarRealSchwartzMultiply_coe (a : S) (f : L2) :
    scalarRealSchwartzMultiply a f =ᵐ[volume] fun x => a x * f x :=
  scalarL2BoundedMultiplier_coe _ _ _ f

def scalarLocalizedCompose (χ : S) (hc : HasCompactSupport (χ : V → ℝ))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (f : S) : S :=
  hc.mul_right.toSchwartzMap ((χ.smooth' : ContDiff ℝ ∞ χ).mul (hφ.comp f.smooth'))

theorem scalarLocalizedCompose_valueLp (χ : S) (hc : HasCompactSupport (χ : V → ℝ))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) {C : ℝ≥0} (hLip : LipschitzWith C φ)
    (hzero : φ 0 = 0) (f : S) :
    (scalarLocalizedCompose χ hc φ hφ f).toLp 2 volume =
      scalarRealSchwartzMultiply χ (hLip.compLp hzero (f.toLp 2 volume)) := by
  apply Lp.ext
  filter_upwards [(scalarLocalizedCompose χ hc φ hφ f).coeFn_toLp 2 volume,
    scalarRealSchwartzMultiply_coe χ (hLip.compLp hzero (f.toLp 2 volume)),
    hLip.coeFn_compLp hzero (f.toLp 2 volume), f.coeFn_toLp 2 volume]
      with x hs hm hp hf
  rw [hs, hm, hp, Function.comp_apply, hf]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! An actual chart H2 representative is the existing intrinsic cutoff value. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Filter
open scoped Manifold ContDiff SchwartzMap ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance cutoffH2Realization_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The localized first derivative identity as an identity of actual L2
functions. The multiplier is uniformly bounded by the scalar derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped SchwartzMap ENNReal ContDiff LineDeriv NNReal

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "S" => 𝓢(V, ℝ)
local notation "D" => fun (i : Fin 4) (φ : S) => ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} φ

theorem scalarRealSchwartzDerivative_apply (f : S) (i : Fin 4) (x : V) :
    D i f x = partialDeriv f i x := by
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, partialDeriv,
    coordinateVector, EuclideanSpace.basisFun_apply]

def scalarDerivativeMultiplier (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {C : ℝ} (hC : ∀ s, |deriv φ s| ≤ C)
    (u : V → ℝ) (hu : AEStronglyMeasurable u (volume : Measure V)) : L2 →L[ℝ] L2 :=
  scalarL2BoundedMultiplier (fun x => deriv φ (u x))
    ((hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable hu) (fun x => hC (u x))

theorem scalarDerivativeMultiplier_coe (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {C : ℝ} (hC : ∀ s, |deriv φ s| ≤ C)
    (u : V → ℝ) (hu : AEStronglyMeasurable u (volume : Measure V)) (f : L2) :
    scalarDerivativeMultiplier φ hφ hC u hu f =ᵐ[volume] fun x => deriv φ (u x) * f x :=
  scalarL2BoundedMultiplier_coe _ _ _ _

theorem scalarLocalizedCompose_first_L2 (χ : S) (hc : HasCompactSupport (χ : V → ℝ))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) {C : ℝ≥0} (hLip : LipschitzWith C φ)
    (hzero : φ 0 = 0) {B : ℝ} (hB : ∀ s, |deriv φ s| ≤ B)
    (f : S) (i : Fin 4) :
    (D i (scalarLocalizedCompose χ hc φ hφ f)).toLp 2 volume =
      scalarRealSchwartzMultiply (D i χ) (hLip.compLp hzero (f.toLp 2 volume)) +
      scalarRealSchwartzMultiply χ
        (scalarDerivativeMultiplier φ hφ hB f f.continuous.aestronglyMeasurable
          ((D i f).toLp 2 volume)) := by
  apply Lp.ext
  let v := hLip.compLp hzero (f.toLp 2 volume)
  let w := scalarDerivativeMultiplier φ hφ hB f f.continuous.aestronglyMeasurable
    ((D i f).toLp 2 volume)
  filter_upwards [(D i (scalarLocalizedCompose χ hc φ hφ f)).coeFn_toLp 2 volume,
    Lp.coeFn_add (scalarRealSchwartzMultiply (D i χ) v) (scalarRealSchwartzMultiply χ w),
    scalarRealSchwartzMultiply_coe (D i χ) v, scalarRealSchwartzMultiply_coe χ w,
    scalarDerivativeMultiplier_coe φ hφ hB f f.continuous.aestronglyMeasurable
      ((D i f).toLp 2 volume),
    hLip.coeFn_compLp hzero (f.toLp 2 volume), f.coeFn_toLp 2 volume,
    (D i f).coeFn_toLp 2 volume] with x hf' hadd hχ' hχ hw hv hfv hdf
  simp only [Pi.add_apply] at hadd
  rw [hf', hadd, hχ', hχ, hw, hv, Function.comp_apply, hfv, hdf,
    scalarRealSchwartzDerivative_apply, scalarRealSchwartzDerivative_apply,
    scalarRealSchwartzDerivative_apply]
  exact scalar_partial_local_composition χ f φ χ.smooth' f.smooth' hφ x i

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual base H1 value remains L4 on compact metric charts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance chartValueL4_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded derivative multipliers converge strongly on moving L2 fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped ContDiff _root_.Topology

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem scalarDerivativeMultiplier_tendsto (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    {B : ℝ} (hB : ∀ s, |deriv φ s| ≤ B) (u : ℕ → V → ℝ) (v : V → ℝ)
    (hu : ∀ n, AEStronglyMeasurable (u n) (volume : Measure V))
    (hv : AEStronglyMeasurable v (volume : Measure V))
    (huv : ∀ᵐ x ∂(volume : Measure V), Tendsto (fun n => u n x) atTop (𝓝 (v x)))
    (f : ℕ → L2) (g : L2) (hfg : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => scalarDerivativeMultiplier φ hφ hB (u n) (hu n) (f n)) atTop
      (𝓝 (scalarDerivativeMultiplier φ hφ hB v hv g)) := by
  have hp : ∀ᵐ x ∂(volume : Measure V), Tendsto (fun n => deriv φ (u n x)) atTop
      (𝓝 (deriv φ (v x))) := by
    filter_upwards [huv] with x hx
    exact (hφ.continuous_deriv (by simp)).continuousAt.tendsto.comp hx
  exact scalarCompositionL2Multiply_tendsto
    (fun n => (hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable (hu n))
    ((hφ.continuous_deriv (by simp)).comp_aestronglyMeasurable hv)
    ((abs_nonneg (deriv φ 0)).trans (hB 0)) (fun n x => hB (u n x))
    (fun x => hB (v x)) hp hfg

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local coordinate derivatives control the intrinsic weak frame derivatives.
Both sides are continuous L2 maps, so the smooth estimate passes to H1. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance frameLocalization_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

/-- Actual frame gradient multiplied by a smooth base cutoff. -/
def scalarH1LocalizedFrame (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (ρ : SmoothScalar (M := M)) {B : ℝ} (hB : ∀ x, |ρ.val x| ≤ B) (i : Fin 4) :
    scalarH1 d →L[ℝ] ScalarL2 g (canonicalFrameMeasure g o) :=
  (scalarL2BoundedMultiplier (fun e : FrameBundle g => ρ.val e.base)
    (ρ.property.continuous.comp (continuous_frameBase g)).aestronglyMeasurable
    (fun e => hB e.base)).comp (scalarH1Gradient d i)

theorem scalarH1LocalizedFrame_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (ρ : SmoothScalar (M := M)) {B : ℝ} (hB : ∀ x, |ρ.val x| ≤ B) (i : Fin 4)
    (a : SmoothScalar (M := M)) :
    scalarH1LocalizedFrame g o d ρ hB i (smoothScalarToH1 d a) =ᵐ[canonicalFrameMeasure g o]
      fun e => ρ.val e.base * scalarGradient g a.val e i := by
  have hc := scalarL2BoundedMultiplier_coe (fun e : FrameBundle g => ρ.val e.base)
    (ρ.property.continuous.comp (continuous_frameBase g)).aestronglyMeasurable
    (fun e => hB e.base) (scalarH1Gradient d i (smoothScalarToH1 d a))
  have hg : scalarH1Gradient d i (smoothScalarToH1 d a) =ᵐ[canonicalFrameMeasure g o]
      fun e => scalarGradient g a.val e i := by
    rw [scalarH1Gradient_smooth]
    exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) _ (smoothScalarGradient d i a)
  exact hc.trans (hg.mono (fun e he => congrArg (ρ.val e.base * ·) he))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The explicit localized Hessian formula in L2. Every product on the
right is an actual bounded multiplier or an L4-times-L4 product. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped SchwartzMap ENNReal ContDiff LineDeriv NNReal

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℝ)
local notation "D" => fun (i : Fin 4) (φ : S) => ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} φ

local instance instFactLeENNRealOfNat_solutions_9_r9d9562_1 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
theorem scalarRealSchwartzSecond_apply (f : S) (i j : Fin 4) (x : V) :
    D i (D j f) x = partialDeriv (fun y => partialDeriv f j y) i x := by
  rw [scalarRealSchwartzDerivative_apply]
  rw [show ((D j f : S) : V → ℝ) = (fun y => partialDeriv f j y) by
    funext y
    exact scalarRealSchwartzDerivative_apply f j y]

theorem scalarLocalizedCompose_second_L2 (χ : S) (hc : HasCompactSupport (χ : V → ℝ))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) {C : ℝ≥0} (hLip : LipschitzWith C φ)
    (hzero : φ 0 = 0) {B₁ B₂ : ℝ} (h₁ : ∀ s, |deriv φ s| ≤ B₁)
    (h₂ : ∀ s, |deriv (deriv φ) s| ≤ B₂) (f : S) (i j : Fin 4) :
    (D i (D j (scalarLocalizedCompose χ hc φ hφ f))).toLp 2 volume =
      scalarRealSchwartzMultiply (D i (D j χ)) (hLip.compLp hzero (f.toLp 2 volume)) +
      scalarRealSchwartzMultiply (D j χ)
        (scalarDerivativeMultiplier φ hφ h₁ f f.continuous.aestronglyMeasurable
          ((D i f).toLp 2 volume)) +
      scalarRealSchwartzMultiply (D i χ)
        (scalarDerivativeMultiplier φ hφ h₁ f f.continuous.aestronglyMeasurable
          ((D j f).toLp 2 volume)) +
      scalarRealSchwartzMultiply χ
        (scalarCompositionHessian φ hφ h₁ h₂ f f.continuous.aestronglyMeasurable
          ((D i f).toLp 4 volume) ((D j f).toLp 4 volume) ((D i (D j f)).toLp 2 volume)) := by
  let v := hLip.compLp hzero (f.toLp 2 volume)
  let t₁ := scalarDerivativeMultiplier φ hφ h₁ f f.continuous.aestronglyMeasurable
    ((D i f).toLp 2 volume)
  let t₂ := scalarDerivativeMultiplier φ hφ h₁ f f.continuous.aestronglyMeasurable
    ((D j f).toLp 2 volume)
  let q := scalarCompositionHessian φ hφ h₁ h₂ f f.continuous.aestronglyMeasurable
    ((D i f).toLp 4 volume) ((D j f).toLp 4 volume) ((D i (D j f)).toLp 2 volume)
  let A := scalarRealSchwartzMultiply (D i (D j χ)) v
  let B := scalarRealSchwartzMultiply (D j χ) t₁
  let C := scalarRealSchwartzMultiply (D i χ) t₂
  let E := scalarRealSchwartzMultiply χ q
  apply Lp.ext
  filter_upwards [(D i (D j (scalarLocalizedCompose χ hc φ hφ f))).coeFn_toLp 2 volume,
    Lp.coeFn_add (A + B + C) E, Lp.coeFn_add (A + B) C, Lp.coeFn_add A B,
    scalarRealSchwartzMultiply_coe (D i (D j χ)) v,
    scalarRealSchwartzMultiply_coe (D j χ) t₁,
    scalarRealSchwartzMultiply_coe (D i χ) t₂,
    scalarRealSchwartzMultiply_coe χ q,
    scalarDerivativeMultiplier_coe φ hφ h₁ f f.continuous.aestronglyMeasurable
      ((D i f).toLp 2 volume),
    scalarDerivativeMultiplier_coe φ hφ h₁ f f.continuous.aestronglyMeasurable
      ((D j f).toLp 2 volume),
    scalarCompositionHessian_coe φ hφ h₁ h₂ f f.continuous.aestronglyMeasurable
      ((D i f).toLp 4 volume) ((D j f).toLp 4 volume) ((D i (D j f)).toLp 2 volume),
    hLip.coeFn_compLp hzero (f.toLp 2 volume), f.coeFn_toLp 2 volume,
    (D i f).coeFn_toLp 2 volume, (D j f).coeFn_toLp 2 volume,
    (D i f).coeFn_toLp 4 volume, (D j f).coeFn_toLp 4 volume,
    (D i (D j f)).coeFn_toLp 2 volume] with x hL hs₃ hs₂ hs₁ hA hB hC hE ht₁ ht₂ hq hv hf hgi hgj hgi₄ hgj₄ hh
  simp only [Pi.add_apply] at hs₁ hs₂ hs₃
  change _ = (A + B + C + E) x
  rw [hL, hs₃, hs₂, hs₁, hA, hB, hC, hE, ht₁, ht₂, hq, hv,
    Function.comp_apply, hf, hgi, hgj, hgi₄, hgj₄, hh]
  simp only [scalarRealSchwartzSecond_apply]
  simp only [scalarRealSchwartzDerivative_apply]
  exact scalar_partial_local_composition_second χ f φ χ.smooth' f.smooth' hφ x i j

end
end PositiveEinsteinFour.Geometry
end


section

/-! Passing the smooth coordinate-to-frame gradient estimate to actual H1. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance frameControl_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rescaled forcing is H1 whenever its intrinsic source is H1. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped Manifold ContDiff SchwartzMap ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance h1Source_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual local H2 regularity of intrinsic weak solutions with L2 forcing.
The metric coefficients, source, scaling and cutoffs are all constructed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance localL2Regularity_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual products of smooth approximants and their first two jets. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory LineDeriv
open scoped SchwartzMap ENNReal LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℝ)
local notation "D" => fun (i : Fin 4) (f : S) => ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} f

local instance instFactLeENNRealOfNat_solutions_12_r9d9562_1 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
def scalarRealSchwartzProduct (f g : S) : S := SchwartzMap.smulLeftCLM ℝ f g

theorem scalarRealSchwartzProduct_apply (f g : S) (x : V) :
    scalarRealSchwartzProduct f g x = f x * g x := by
  exact SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth g x

theorem scalarRealSchwartzProduct_first (f g : S) (i : Fin 4) :
    D i (scalarRealSchwartzProduct f g) =
      scalarRealSchwartzProduct (D i f) g + scalarRealSchwartzProduct f (D i g) := by
  ext x
  simp only [add_apply, scalarRealSchwartzDerivative_apply,
    scalarRealSchwartzProduct_apply]
  have he : (scalarRealSchwartzProduct f g : V → ℝ) = fun y => f y * g y :=
    funext (scalarRealSchwartzProduct_apply f g)
  rw [he]
  exact scalar_partial_product f g x f.differentiableAt g.differentiableAt i

theorem scalarRealSchwartzProduct_second (f g : S) (i j : Fin 4) :
    D i (D j (scalarRealSchwartzProduct f g)) =
      scalarRealSchwartzProduct (D i (D j f)) g +
      scalarRealSchwartzProduct (D j f) (D i g) +
      scalarRealSchwartzProduct (D i f) (D j g) +
      scalarRealSchwartzProduct f (D i (D j g)) := by
  calc
    D i (D j (scalarRealSchwartzProduct f g)) =
        D i (scalarRealSchwartzProduct (D j f) g + scalarRealSchwartzProduct f (D j g)) :=
      congrArg (fun h : S => D i h) (scalarRealSchwartzProduct_first f g j)
    _ = D i (scalarRealSchwartzProduct (D j f) g) +
        D i (scalarRealSchwartzProduct f (D j g)) :=
      (lineDerivOpCLM ℝ S (EuclideanSpace.basisFun (Fin 4) ℝ i)).map_add _ _
    _ = (scalarRealSchwartzProduct (D i (D j f)) g +
        scalarRealSchwartzProduct (D j f) (D i g)) +
        (scalarRealSchwartzProduct (D i f) (D j g) +
        scalarRealSchwartzProduct f (D i (D j g))) :=
      congrArg₂ (fun a b : S => a + b) (scalarRealSchwartzProduct_first (D j f) g i)
        (scalarRealSchwartzProduct_first f (D j g) i)
    _ = _ := by abel

theorem realSchwartz_toLp_add (f g : S) :
    (f + g).toLp 2 volume = f.toLp 2 volume + g.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℝ ℝ 2 volume).map_add f g

theorem scalarRealSchwartzProduct_L2_top (f g : S) :
    (scalarRealSchwartzProduct f g).toLp 2 volume =
      scalarLinfL2Product (g.toLp ∞ volume) (f.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(scalarRealSchwartzProduct f g).coeFn_toLp 2 volume,
    scalarLinfL2Product_coe (g.toLp ∞ volume) (f.toLp 2 volume),
    f.coeFn_toLp 2 volume, g.coeFn_toLp ∞ volume] with x hfg hmul hf hg
  rw [hfg, hmul, hf, hg, scalarRealSchwartzProduct_apply, mul_comm]

theorem scalarRealSchwartzProduct_L2_four (f g : S) :
    (scalarRealSchwartzProduct f g).toLp 2 volume =
      scalarL4Product (f.toLp 4 volume) (g.toLp 4 volume) := by
  apply Lp.ext
  filter_upwards [(scalarRealSchwartzProduct f g).coeFn_toLp 2 volume,
    scalarL4Product_coe (f.toLp 4 volume) (g.toLp 4 volume),
    f.coeFn_toLp 4 volume, g.coeFn_toLp 4 volume] with x hfg hmul hf hg
  rw [hfg, hmul, hf, hg, scalarRealSchwartzProduct_apply]

theorem scalarRealSchwartzProduct_first_L2 (f g : S) (i : Fin 4) :
    (D i (scalarRealSchwartzProduct f g)).toLp 2 volume =
      scalarL4Product ((D i f).toLp 4 volume) (g.toLp 4 volume) +
      scalarL4Product (f.toLp 4 volume) ((D i g).toLp 4 volume) := by
  calc
    _ = (scalarRealSchwartzProduct (D i f) g + scalarRealSchwartzProduct f (D i g)).toLp 2 volume :=
      congrArg (fun h : S => h.toLp 2 volume) (scalarRealSchwartzProduct_first f g i)
    _ = (scalarRealSchwartzProduct (D i f) g).toLp 2 volume +
        (scalarRealSchwartzProduct f (D i g)).toLp 2 volume := realSchwartz_toLp_add _ _
    _ = _ := congrArg₂ (fun a b : Lp ℝ 2 (volume : Measure V) => a + b)
      (scalarRealSchwartzProduct_L2_four (D i f) g)
      (scalarRealSchwartzProduct_L2_four f (D i g))

theorem realSchwartz_toLp_four_add (a b c d : S) :
    (a + b + c + d).toLp 2 volume =
      a.toLp 2 volume + b.toLp 2 volume + c.toLp 2 volume + d.toLp 2 volume := by
  rw [realSchwartz_toLp_add, realSchwartz_toLp_add, realSchwartz_toLp_add]

theorem scalarRealSchwartzProduct_second_L2 (f g : S) (i j : Fin 4) :
    (D i (D j (scalarRealSchwartzProduct f g))).toLp 2 volume =
      scalarLinfL2Product (g.toLp ∞ volume) ((D i (D j f)).toLp 2 volume) +
      scalarL4Product ((D j f).toLp 4 volume) ((D i g).toLp 4 volume) +
      scalarL4Product ((D i f).toLp 4 volume) ((D j g).toLp 4 volume) +
      scalarL4Product (f.toLp 4 volume) ((D i (D j g)).toLp 4 volume) := by
  calc
    _ = (scalarRealSchwartzProduct (D i (D j f)) g +
        scalarRealSchwartzProduct (D j f) (D i g) +
        scalarRealSchwartzProduct (D i f) (D j g) +
        scalarRealSchwartzProduct f (D i (D j g))).toLp 2 volume :=
      congrArg (fun h : S => h.toLp 2 volume) (scalarRealSchwartzProduct_second f g i j)
    _ = (scalarRealSchwartzProduct (D i (D j f)) g).toLp 2 volume +
        (scalarRealSchwartzProduct (D j f) (D i g)).toLp 2 volume +
        (scalarRealSchwartzProduct (D i f) (D j g)).toLp 2 volume +
        (scalarRealSchwartzProduct f (D i (D j g))).toLp 2 volume :=
      realSchwartz_toLp_four_add _ _ _ _
    _ = _ := congrArg₂ (fun a b : Lp ℝ 2 (volume : Measure V) => a + b)
      (congrArg₂ (fun a b : Lp ℝ 2 (volume : Measure V) => a + b)
        (congrArg₂ (fun a b : Lp ℝ 2 (volume : Measure V) => a + b)
          (scalarRealSchwartzProduct_L2_top (D i (D j f)) g)
          (scalarRealSchwartzProduct_L2_four (D j f) (D i g)))
        (scalarRealSchwartzProduct_L2_four (D i f) (D j g)))
      (scalarRealSchwartzProduct_L2_four f (D i (D j g)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Fourth-power integrability transfers through compact chart reconstruction
and the closed coordinate-to-frame domination inequality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter Function
open scoped Manifold ContDiff ENNReal BigOperators

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance l4Transfer_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual local H3 regularity of intrinsic weak solutions with H1 forcing.
The metric coefficients, source, scaling and cutoffs are all constructed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance localH1Regularity_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strong subcritical convergence for bounded intrinsic H¹ sequences,
using the actual manifold L² compactness and the L²/L⁴ interpolation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_15
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance subcriticalCompactness_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance subcriticalCompactness_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local H2 yields fourth-power integrability of the actual frame gradient,
including the lower-order correction from differentiating the cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter TemperedDistribution
open scoped Manifold ContDiff ENNReal SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance chartGradientL4_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! A finite smooth partition assembles local fourth-power weak gradient bounds. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

variable [Nonempty M] [MeasurableSpace M] [BorelSpace M]

local instance gradientAssembly_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local Euler power is H2 after positivity. The density-weighted
weak solution is first divided by its actual smooth positive density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal ContDiff NNReal

noncomputable section

local notation "V" => FourSpace

theorem scalar_half_ball_cutoff_of_compact {K : Set V} (hK : IsCompact K)
    (hKs : K ⊆ ball 0 (1 / 2)) :
    ∃ χ : V → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ ball 0 (1 / 2) ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨t, ht, hbound⟩ := hK.exists_forall_le'
    continuous_norm.neg.continuousOn (a := -(1 / 2 : ℝ)) (by
      intro x hx
      have h : ‖x‖ < (1 / 2 : ℝ) := by
        simpa only [mem_ball, dist_zero_right] using hKs hx
      change -(1 / 2 : ℝ) < -‖x‖
      linarith)
  let r : ℝ := max (-t) (1 / 4)
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hrh : r < 1 / 2 := max_lt (by linarith) (by norm_num)
  let χ : ContDiffBump (0 : V) :=
    { rIn := r
      rOut := (r + 1 / 2) / 2
      rIn_pos := hr
      rIn_lt_rOut := by linarith }
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, ?_, ?_⟩
  · rw [χ.tsupport_eq]
    apply closedBall_subset_ball
    change (r + 1 / 2) / 2 < 1 / 2
    linarith
  · intro x hx
    apply χ.one_of_mem_closedBall
    have hb : ‖x‖ ≤ -t := by
      have hb := hbound x hx
      change t ≤ -‖x‖ at hb
      linarith
    simpa only [mem_closedBall, dist_zero_right] using hb.trans (le_max_left (-t) (1 / 4))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Existence of an extremizer for the actual subcritical scalar Sobolev
operator, using compactness and the exact weighted Hilbert norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance variationalMinimum_frameCompact_r9d9562_1 (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g
local instance variationalMinimum_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The reciprocal-variable Hessian identity in the subcritical scalar
equation used to prove the sharp four-dimensional Sobolev inequality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} {a : M → ℝ}

theorem scalar_inverse_cube_gradient (s : ScalarCovariantData d a)
    (ha : ∀ x, a x ≠ 0)
    (v : ScalarCovariantData d (fun x => (a x ^ 3)⁻¹))
    (e : FrameBundle g) (i : Fin 4) :
    scalarGradient g (fun x => (a x ^ 3)⁻¹) e i =
      (-3 / a e.base ^ 4) * scalarGradient g a e i := by
  obtain ⟨e₀, he⟩ := ((d.flow i).map 0).surjective e
  have h := v.derivativeValue i 0 e₀
  have h' := ((s.derivativeValue i 0 e₀).pow 3).inv
    (pow_ne_zero 3 (ha _))
  simp only [Pi.pow_apply] at h'
  have heq := h.unique h'
  rw [he] at heq
  rw [heq]
  field_simp [ha e.base]
  ring

theorem scalar_reciprocal_equation_derivative (s : ScalarCovariantData d a)
    (p : ℝ) (ha : ∀ x, 0 < a x)
    (hEq : ∀ e : FrameBundle g,
      a e.base * scalarLaplacian g a e -
        2 * (∑ i, scalarGradient g a e i ^ 2) + 2 * a e.base ^ 2 =
          2 * (a e.base) ^ (4 - p))
    (e : FrameBundle g) (j : Fin 4) :
    a e.base * (∑ i, scalarThird g a e j i i) -
        4 * (∑ i, scalarGradient g a e i * scalarHessian g a e i j) +
        scalarLaplacian g a e * scalarGradient g a e j +
        4 * a e.base * scalarGradient g a e j =
      2 * (4 - p) * (a e.base) ^ (3 - p) * scalarGradient g a e j := by
  obtain ⟨e₀, he⟩ := ((d.flow j).map 0).surjective e
  have hL := (((s.derivativeValue j 0 e₀).mul (s.derivativeLaplacian j 0 e₀)).sub
    ((HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
      (s.derivativeGradient j i 0 e₀).pow 2)).const_mul 2)).add
        (((s.derivativeValue j 0 e₀).pow 2).const_mul 2)
  have hR := ((s.derivativeValue j 0 e₀).rpow_const
    (p := 4 - p) (Or.inl (ne_of_gt (ha _)))).const_mul 2
  have hf : (fun t => a ((d.flow j).map t e₀).base *
      scalarLaplacian g a ((d.flow j).map t e₀) -
        2 * (∑ i, scalarGradient g a ((d.flow j).map t e₀) i ^ 2) +
          2 * a ((d.flow j).map t e₀).base ^ 2) =
        (fun t => 2 * (a ((d.flow j).map t e₀).base) ^ (4 - p)) :=
    funext (fun t => hEq _)
  change HasDerivAt (fun t => a ((d.flow j).map t e₀).base *
      scalarLaplacian g a ((d.flow j).map t e₀) -
        2 * (∑ i, scalarGradient g a ((d.flow j).map t e₀) i ^ 2) +
          2 * a ((d.flow j).map t e₀).base ^ 2) _ 0 at hL
  rw [hf] at hL
  have h := hL.unique hR
  rw [he] at h
  have hexp : 4 - p - 1 = 3 - p := by ring
  simp only [hexp, Nat.cast_ofNat, Nat.reduceSub, pow_one] at h
  have hs : (∑ i, 2 * scalarGradient g a e i * scalarHessian g a e j i) =
      2 * (∑ i, scalarGradient g a e i * scalarHessian g a e i j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [s.hessianSymmetric e j i]
    ring
  rw [hs] at h
  linarith only [h]

theorem scalar_inverse_hessian_algebra (x L D : ℝ) (hx : x ≠ 0)
    (v : Fin 4 → ℝ) (H : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    (∑ i, ((-3 / x ^ 4) * v i) *
      (H i j - if i = j then L / 4 else 0)) +
      (3 / 4 : ℝ) * (x ^ 3)⁻¹ * (D + 4 * v j) =
        (3 / 4 : ℝ) / x ^ 4 *
          (x * D - 4 * (∑ i, v i * H i j) + L * v j + 4 * x * v j) := by
  have hs : (∑ i, v i * (if i = j then L / 4 else 0)) = v j * L / 4 := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
    ring
  simp_rw [mul_sub, mul_assoc, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hs]
  field_simp [hx]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normalization and the actual energy minimum for the subcritical scalar
Sobolev quotient.  The constant function gives the upper bound one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance normalizedMinimum_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance normalizedMinimum_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The critical limit in the scalar Sobolev inequality.  The limit is
taken for each actual smooth test function under an integrable bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance scalarCritical_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance scalarCritical_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Absolute values in actual Lp and the convergence of positive smooth
regularizations of an approximating scalar sequence. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance scalarLpAbs_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance scalarLpAbs_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive reciprocal solutions of the subcritical scalar equation
are constant. This supplies the rigidity step in the normalized
Sobolev minimization argument, independently of minimizer existence. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} {a : M → ℝ}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [PreconnectedSpace M]

local instance nonlinearRigidity_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual first and second covariant derivatives of a reciprocal scalar,
for the substitution in the subcritical Euler equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  {d : MetricGreenData g μ} {a : M → ℝ}

theorem scalar_reciprocal_gradient (s : ScalarCovariantData d a)
    (ha : ∀ x, a x ≠ 0) (v : ScalarCovariantData d (fun x => (a x)⁻¹))
    (e : FrameBundle g) (i : Fin 4) :
    scalarGradient g (fun x => (a x)⁻¹) e i =
      -scalarGradient g a e i / a e.base ^ 2 := by
  obtain ⟨e₀, he⟩ := ((d.flow i).map 0).surjective e
  have h := v.derivativeValue i 0 e₀
  have h' := (s.derivativeValue i 0 e₀).inv (ha _)
  have heq := h.unique h'
  rwa [he] at heq

theorem scalar_reciprocal_hessian (s : ScalarCovariantData d a)
    (ha : ∀ x, a x ≠ 0) (v : ScalarCovariantData d (fun x => (a x)⁻¹))
    (e : FrameBundle g) (i j : Fin 4) :
    scalarHessian g (fun x => (a x)⁻¹) e i j =
      2 / a e.base ^ 3 * scalarGradient g a e i * scalarGradient g a e j -
        scalarHessian g a e i j / a e.base ^ 2 := by
  obtain ⟨e₀, he⟩ := ((d.flow i).map 0).surjective e
  have h := v.derivativeGradient i j 0 e₀
  have h' := (s.derivativeGradient i j 0 e₀).neg.div
    ((s.derivativeValue i 0 e₀).pow 2) (pow_ne_zero 2 (ha _))
  have hf : (fun t => scalarGradient g (fun x => (a x)⁻¹) ((d.flow i).map t e₀) j) =
      (fun t => -scalarGradient g a ((d.flow i).map t e₀) j /
        a ((d.flow i).map t e₀).base ^ 2) :=
    funext (fun t => scalar_reciprocal_gradient s ha v _ j)
  rw [hf] at h
  simp only [Pi.pow_apply, Pi.neg_apply] at h'
  have heq := h.unique h'
  rw [he] at heq
  rw [heq]
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [ha e.base]
  ring

theorem scalar_reciprocal_laplacian (s : ScalarCovariantData d a)
    (ha : ∀ x, a x ≠ 0) (v : ScalarCovariantData d (fun x => (a x)⁻¹))
    (e : FrameBundle g) :
    scalarLaplacian g (fun x => (a x)⁻¹) e =
      2 / a e.base ^ 3 * (∑ i, scalarGradient g a e i ^ 2) -
        scalarLaplacian g a e / a e.base ^ 2 := by
  unfold scalarLaplacian
  simp_rw [scalar_reciprocal_hessian s ha v, Finset.sum_sub_distrib]
  rw [Finset.sum_div, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem scalar_reciprocal_gradient_energy (s : ScalarCovariantData d a)
    (ha : ∀ x, a x ≠ 0) (v : ScalarCovariantData d (fun x => (a x)⁻¹))
    (e : FrameBundle g) :
    (∑ i, scalarGradient g (fun x => (a x)⁻¹) e i ^ 2) =
      (∑ i, scalarGradient g a e i ^ 2) / a e.base ^ 4 := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [scalar_reciprocal_gradient s ha v]
  field_simp [ha e.base]

theorem scalar_reciprocal_euler_equation (s : ScalarCovariantData d a)
    (ha : ∀ x, 0 < a x) (v : ScalarCovariantData d (fun x => (a x)⁻¹))
    (p : ℝ)
    (hEq : ∀ e : FrameBundle g, -scalarLaplacian g a e + 2 * a e.base =
      2 * a e.base ^ (p - 1)) (e : FrameBundle g) :
    (a e.base)⁻¹ * scalarLaplacian g (fun x => (a x)⁻¹) e -
        2 * (∑ i, scalarGradient g (fun x => (a x)⁻¹) e i ^ 2) +
          2 * ((a e.base)⁻¹) ^ 2 = 2 * ((a e.base)⁻¹) ^ (4 - p) := by
  have hn := fun x => ne_of_gt (ha x)
  rw [scalar_reciprocal_laplacian s hn v, scalar_reciprocal_gradient_energy s hn v]
  have hpow : a e.base ^ (p - 1) = a e.base ^ (p - 4) * a e.base ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (ha _)]
    congr 1
    ring
  have hInv : ((a e.base)⁻¹) ^ (4 - p) = a e.base ^ (p - 4) := by
    rw [Real.inv_rpow (ha _).le, ← Real.rpow_neg (ha _).le]
    congr 1
    ring
  rw [hInv]
  have h := hEq e
  rw [hpow] at h
  field_simp [hn e.base]
  linear_combination (a e.base) * h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Euler identity for a normalized Hilbert-energy minimum. -/

namespace PositiveEinsteinFour.Geometry

open Filter
open scoped _root_.Topology

noncomputable section

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance scalarEuler_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance scalarEuler_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The rational Kato test is an admissible actual Sobolev variation of the
normalized minimum.  Its Euler identity is derived directly from that
minimum, with no additional extension of the weak equation assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance katoTesting_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

local instance katoTesting_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Recovery of the full actual Sobolev jet from its scalar Lp representative,
and the weighted pairing on smooth scalar functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance scalarSmoothRep_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The fixed space of the actual scalar shifted resolvent is precisely the
constant functions on the connected manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

local instance scalarFixed_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Rescaling the normalized positive Euler minimizer to the already proved
unit-coefficient rigidity theorem. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem smoothScalarHessian_const_smul (d : ParallelMetricData g μ)
    (c : ℝ) (a : SmoothScalar (M := M)) (e : FrameBundle g) (i j : Fin 4) :
    scalarHessian g (c • a).val e i j = c * scalarHessian g a.val e i j := by
  let sa := Classical.choice (d.scalarCalculus.toPetersenInput a.val a.property)
  let sb := Classical.choice (d.scalarCalculus.toPetersenInput (c • a).val (c • a).property)
  obtain ⟨f, hf⟩ := ((d.toMetricGreenData.flow i).map 0).surjective e
  change (d.toMetricGreenData.flow i).map 0 f = e at hf
  have hg (z : FrameBundle g) : scalarGradient g (c • a).val z j =
      c * scalarGradient g a.val z j := by
    change (smoothScalarGradient d j (c • a)) z = _
    rw [map_smul]
    rfl
  have h := sb.derivativeGradient i j 0 f
  have h' := (sa.derivativeGradient i j 0 f).const_mul c
  have heq : (fun t => scalarGradient g (c • a).val ((d.toMetricGreenData.flow i).map t f) j) =
      fun t => c * scalarGradient g a.val ((d.toMetricGreenData.flow i).map t f) j :=
    funext (fun t => hg _)
  rw [heq] at h
  have hu := h.unique h'
  rwa [hf] at hu

theorem smoothScalarLaplacian_const_smul (d : ParallelMetricData g μ)
    (c : ℝ) (a : SmoothScalar (M := M)) (e : FrameBundle g) :
    scalarLaplacian g (c • a).val e = c * scalarLaplacian g a.val e := by
  simp only [scalarLaplacian, smoothScalarHessian_const_smul d, Finset.mul_sum]

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [PreconnectedSpace M]

local instance scalarEulerScaling_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual rational-test energy and the resulting L⁸ gain for the
subcritical minimizing scalar. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal BigOperators

noncomputable section

theorem kato_gradient_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {lam : ℝ} (hlam : 0 < lam) (f : X → ℝ)
    (a b c : Lp ℝ 2 μ)
    (hb : b =ᵐ[μ] fun x => scalarKatoTestRate lam (f x) * a x)
    (hc : c =ᵐ[μ] fun x => scalarKatoSquareRate lam (f x) * a x) :
    ‖c‖ ^ 2 ≤ 2 * inner ℝ a b := by
  rw [scalarL2_norm_sq, kato_real_inner, ← integral_const_mul]
  apply integral_mono_ae (Lp.memLp c).integrable_sq
    (((Lp.memLp a).integrable_mul (Lp.memLp b)).const_mul 2)
  filter_upwards [hb, hc] with x hbx hcx
  change c x ^ 2 ≤ 2 * (a x * b x)
  rw [hbx, hcx, mul_pow]
  have h := mul_le_mul_of_nonneg_right (scalarKatoSquareRate_sq_le hlam (f x))
    (sq_nonneg (a x))
  nlinarith only [h]

/-- The subcritical nonlinear potential is in L² because the actual H¹
value is already in L⁴. -/
theorem scalarKato_potential_memLp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ} (hf : MemLp f 4 μ)
    {p : ℝ} (hp : 2 < p) (hp4 : p < 4) :
    MemLp (fun x => |f x| ^ (p - 2)) 2 μ := by
  have hs := scalarKato_square_memLp hf
  have hdom : MemLp (fun x => 1 + f x ^ 2) 2 μ :=
    (memLp_const (1 : ℝ)).add hs
  have hc : Continuous (fun s : ℝ => |s| ^ (p - 2)) :=
    continuous_abs.rpow_const (fun _ => Or.inr (by linarith : 0 ≤ p - 2))
  apply hdom.mono' (hc.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖|f x| ^ (p - 2)‖ ≤ 1 + f x ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    by_cases hx : |f x| ≤ 1
    · exact (Real.rpow_le_one (abs_nonneg _) hx (by linarith)).trans (by nlinarith [sq_nonneg (f x)])
    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx)
        (show p - 2 ≤ 2 by linarith)
      rw [Real.rpow_two, sq_abs] at h
      exact h.trans (by linarith)


attribute [local instance] OAI.PositiveEinsteinFour.Geometry.katoEnergy_four
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance katoEnergy_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

local instance katoEnergy_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Once the nonlinear source belongs to L2, the proved smooth-test Euler
equation extends to every actual H1 test by density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

local instance scalarWeakEulerL2_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance scalarWeakEulerL2_probability_r9d9562_1 (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
theorem scalar_weighted_euler_to_weak_poisson
    (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (w : scalarWeightedH1 d) (Z : ScalarL2 g (canonicalFrameMeasure g o)) (m : ℝ)
    (hweak : ∀ v : scalarWeightedH1 d, inner ℝ w v = m * inner ℝ Z
      (scalarH1Value d (scalarWeightedH1ToH1 d v))) (v : scalarH1 d) :
    (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i (scalarWeightedH1ToH1 d w))
      (scalarH1Gradient d i v)) =
      -(inner ℝ ((2 : ℝ) • scalarH1Value d (scalarWeightedH1ToH1 d w) - (2 * m) • Z)
        (scalarH1Value d v)) := by
  have h := hweak (scalarWeightedH1Equiv d v)
  rw [scalarWeightedH1ToH1_equiv] at h
  have hw : w = scalarWeightedH1Equiv d (scalarWeightedH1ToH1 d w) :=
    ((scalarWeightedH1Equiv d).apply_symm_apply w).symm
  conv_lhs at h => rw [hw, scalarWeightedH1_inner]
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weak minimum equation becomes the pointwise geometric Euler
equation once its actual representative is smooth and positive. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def smoothScalarPositivePower (a : SmoothScalar (M := M))
    (ha : ∀ x, 0 < a.val x) (q : ℝ) : SmoothScalar (M := M) := by
  refine ⟨fun x => a.val x ^ q, ?_⟩
  intro x
  exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt (ha x))).comp_contMDiffAt
    a.property.contMDiffAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint finite smooth extensions for the normal coefficient family.
The leading amplitude remains strictly positive away from the chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatFamilyCutoff_contDiff (n : ℕ) (χ f : HeatRadialFrameSpace → ℝ)
    (hχ : ContDiff ℝ n χ) (hf : ∀ z ∈ tsupport χ, ContDiffAt ℝ n f z) :
    ContDiff ℝ n (fun z => χ z * f z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hf z hz)
  · have he : (fun y => χ y * f y) =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Construction of the actual L2 source and weak Poisson equation from
the eighth-moment gain of the normalized subcritical minimizer. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

local instance scalarMinimumSource_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance scalarMinimumSource_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous representative of the actual nonnegative normalized subcritical
minimum is strictly positive, using its proved L2 weak equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff BigOperators NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [PreconnectedSpace M]

local instance continuousMinimum_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual variational minimum has local second Sobolev derivatives,
without any assumed smoothness or positivity of its representative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff BigOperators SchwartzMap ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

local instance minimumH2_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The subcritical nonlinear chain rule on the actual H1 closure. Smooth
bounded-derivative truncations converge strongly in the value and all four
weak derivatives, using L8 values and L4 gradients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

theorem nonlinear_derivative_tendsto {q : ℝ} (hq : 0 < q) (s : ℝ) :
    Tendsto (fun n => deriv (scalarNonlinearTruncation q (nonlinearEpsilon n)) s)
      atTop (𝓝 ((q + 1) * |s| ^ q)) := by
  simp_rw [scalarNonlinearTruncation_deriv q (nonlinearEpsilon_pos _)]
  by_cases hs : s = 0
  · subst s
    simpa only [scalarNonlinearTruncationDerivative, zero_pow (by decide : 2 ≠ 0),
      zero_add, mul_zero, zero_mul, div_one, zero_div, add_zero, sub_zero, mul_one,
      abs_zero, Real.zero_rpow hq.ne', mul_zero] using nonlinear_power_tendsto hq 0
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero _ hs
  have ha : Tendsto (fun n => s ^ 2 + nonlinearEpsilon n) atTop (𝓝 (s ^ 2)) := by
    simpa using tendsto_const_nhds.add nonlinearEpsilon_tendsto
  have hb : Tendsto (fun n => 1 + nonlinearEpsilon n * s ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add (nonlinearEpsilon_tendsto.mul_const (s ^ 2))
  have hc : Tendsto (fun n => q * s ^ 2 / (s ^ 2 + nonlinearEpsilon n))
      atTop (𝓝 q) := by
    have hn : Tendsto (fun _ : ℕ => q * s ^ 2) atTop (𝓝 (q * s ^ 2)) :=
      tendsto_const_nhds
    simpa only [Pi.div_apply, mul_div_cancel_right₀ _ hs2] using! hn.div ha hs2
  have hd : Tendsto (fun n => 2 * nonlinearEpsilon n * s ^ 2 /
      (1 + nonlinearEpsilon n * s ^ 2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Pi.div_apply, zero_mul, mul_zero, zero_div] using!
      ((nonlinearEpsilon_tendsto.const_mul 2).mul_const (s ^ 2)).div hb one_ne_zero
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h := ((nonlinear_power_tendsto hq s).div hb one_ne_zero).mul
    ((h1.add hc).sub hd)
  simpa only [scalarNonlinearTruncationDerivative, Pi.div_apply, Pi.add_apply, Pi.sub_apply,
    div_one, sub_zero, mul_comm, add_comm] using! h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

/-- The subcritical power has an actual H1 first jet once its value is L8
and its four weak derivatives are L4. -/
theorem scalarH1_subcritical_compose (d : ParallelMetricData g μ) (u : scalarH1 d)
    {p : ℝ} (hp : 2 < p) (hp4 : p < 4)
    (hu : MemLp (scalarH1Value d u : FrameBundle g → ℝ) 8 μ)
    (hDu : ∀ i, MemLp (scalarH1Gradient d i u : FrameBundle g → ℝ) 4 μ) :
    ∃ v : scalarH1 d,
      (scalarH1Value d v : FrameBundle g → ℝ) =ᵐ[μ]
        (fun x => |scalarH1Value d u x| ^ (p - 2) * scalarH1Value d u x) ∧
      ∀ i, (scalarH1Gradient d i v : FrameBundle g → ℝ) =ᵐ[μ]
        (fun x => (p - 1) * |scalarH1Value d u x| ^ (p - 2) * scalarH1Gradient d i u x) := by
  let f : FrameBundle g → ℝ := scalarH1Value d u
  let F : FrameBundle g → ℝ := fun x => |f x| ^ (p - 2) * f x
  let G : Fin 4 → FrameBundle g → ℝ := fun i x =>
    (p - 1) * |f x| ^ (p - 2) * scalarH1Gradient d i u x
  have hF : MemLp F 2 μ := scalar_nonlinear_memLp_two_of_eight hu hp hp4
  have hG (i : Fin 4) : MemLp (G i) 2 μ :=
    scalar_subcritical_nonlinear_gradient_memLp_two hu (hDu i) hp hp4
  have hvn (n : ℕ) : ∃ v : scalarH1 d,
      (scalarH1Value d v : FrameBundle g → ℝ) =ᵐ[μ]
        (fun x => scalarNonlinearTruncation (p - 2) (nonlinearEpsilon n) (f x)) ∧
      ∀ i, (scalarH1Gradient d i v : FrameBundle g → ℝ) =ᵐ[μ]
        (fun x => deriv (scalarNonlinearTruncation (p - 2) (nonlinearEpsilon n)) (f x) *
          scalarH1Gradient d i u x) := by
    let D : ℝ≥0 := ⟨5 / nonlinearEpsilon n,
      le_of_lt (div_pos (by norm_num) (nonlinearEpsilon_pos n))⟩
    exact scalarH1_compose_exists_of_deriv_bound d _
      (scalarNonlinearTruncation_smooth _ (nonlinearEpsilon_pos n))
      (scalarNonlinearTruncation_zero _ _) (D := D)
      (scalarNonlinearTruncation_deriv_bounded (by linarith) (by linarith)
        (nonlinearEpsilon_pos n) (nonlinearEpsilon_le_one n)) u
  choose vn hvn hDn using hvn
  let V : ScalarL2 g μ := hF.toLp F
  let W : Fin 4 → ScalarL2 g μ := fun i => (hG i).toLp (G i)
  have hV : Tendsto (fun n => scalarH1Value d (vn n)) atTop (𝓝 V) := by
    apply nonlinear_L2_tendsto _ V _ (nonlinear_value_dominator hu)
    · intro n
      filter_upwards [hvn n] with x hx
      rw [hx]
      exact nonlinear_value_bound (by linarith) (by linarith)
        (nonlinearEpsilon_pos n) (nonlinearEpsilon_le_one n) _
    · filter_upwards [hF.coeFn_toLp] with x hx
      rw [hx]
      exact le_of_tendsto (nonlinear_value_tendsto (by linarith : 0 < p - 2) (f x) |>.norm)
        (Eventually.of_forall fun n => by
          simpa only [Real.norm_eq_abs] using nonlinear_value_bound (by linarith) (by linarith)
            (nonlinearEpsilon_pos n) (nonlinearEpsilon_le_one n) (f x))
    · filter_upwards [ae_all_iff.mpr hvn, hF.coeFn_toLp] with x hx hFx
      simp_rw [hx]
      rw [hFx]
      exact nonlinear_value_tendsto (by linarith) (f x)
  have hW (i : Fin 4) : Tendsto (fun n => scalarH1Gradient d i (vn n)) atTop (𝓝 (W i)) := by
    apply nonlinear_L2_tendsto _ (W i) _ (nonlinear_gradient_dominator hu (hDu i))
    · intro n
      filter_upwards [hDn n i] with x hx
      rw [hx, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (scalarNonlinearTruncation_deriv_growth (by linarith) (by linarith)
          (nonlinearEpsilon_pos n) (nonlinearEpsilon_le_one n) (f x)) (abs_nonneg _)
    · filter_upwards [(hG i).coeFn_toLp] with x hx
      rw [hx]
      have ht := (nonlinear_derivative_tendsto (by linarith : 0 < p - 2) (f x)).mul_const
        (scalarH1Gradient d i u x)
      have he : p - 2 + 1 = p - 1 := by ring
      rw [he] at ht
      exact le_of_tendsto ht.norm (Eventually.of_forall fun n => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (scalarNonlinearTruncation_deriv_growth (by linarith) (by linarith)
            (nonlinearEpsilon_pos n) (nonlinearEpsilon_le_one n) (f x)) (abs_nonneg _))
    · filter_upwards [ae_all_iff.mpr (fun n => hDn n i), (hG i).coeFn_toLp] with x hx hGx
      simp_rw [hx]
      rw [hGx]
      have ht := (nonlinear_derivative_tendsto (by linarith : 0 < p - 2) (f x)).mul_const
        (scalarH1Gradient d i u x)
      simpa only [show p - 2 + 1 = p - 1 by ring] using ht
  obtain ⟨v, hv, hgrad⟩ := scalarH1_jet_limit d vn V W hV hW
  refine ⟨v, ?_, fun i => ?_⟩
  · rw [hv]
    exact hF.coeFn_toLp
  · rw [hgrad i]
    exact (hG i).coeFn_toLp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual local smooth Sobolev regularity for a positive continuous weak Euler solution.
All coefficients, density factors and localized nonlinear sources are constructed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance positiveEulerAllOrders_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive continuous weak Euler solutions have actual smooth representatives.
Local regularity of all orders, Fourier embedding and chart unweighting
give the representatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance positiveEulerSmooth_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual minimizing scalar has fourth-power integrable weak gradients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped Manifold ContDiff SchwartzMap ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance minimumGradientL4_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! A quantitative second-order bound from a bounded Hessian on a ball.
This will be applied uniformly to the signed first heat coefficient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped ContDiff _root_.Topology

noncomputable section

theorem fourHeat_quadratic_bound_of_hessian (f : FourSpace → ℝ)
    (hf : ContDiff ℝ 2 f) (f0 : f 0 = 0) (D0 : fderiv ℝ f 0 = 0)
    (R C : ℝ) (hC : 0 ≤ C)
    (hess : ∀ y ∈ closedBall (0 : FourSpace) R, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ C)
    (x : FourSpace) (hx : x ∈ closedBall 0 R) : ‖f x‖ ≤ C * ‖x‖ ^ 2 := by
  let S := closedBall (0 : FourSpace) ‖x‖
  have hS : Convex ℝ S := convex_closedBall _ _
  have hsR : S ⊆ closedBall (0 : FourSpace) R := by
    apply closedBall_subset_closedBall
    simpa only [mem_closedBall_zero_iff] using hx
  have h0S : (0 : FourSpace) ∈ S := mem_closedBall_self (norm_nonneg x)
  have hxS : x ∈ S := by simp [S]
  have hd : ∀ y ∈ S, ‖fderiv ℝ f y‖ ≤ C * ‖x‖ := by
    intro y hy
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero z)
      (fun z hz => hess z (hsR hz)) hS h0S hy
    rw [D0, sub_zero, sub_zero] at hh
    have hy' : ‖y‖ ≤ ‖x‖ := by simpa only [S, mem_closedBall_zero_iff] using hy
    exact hh.trans (mul_le_mul_of_nonneg_left hy' hC)
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hf.differentiable two_ne_zero y) hd hS h0S hxS
  simpa only [f0, sub_zero, pow_two, mul_assoc] using hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constant scalar heat mode has multiplicity exactly one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_9 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual minimizing scalar has intrinsic H1 forcing. This is the
pre-positivity bootstrap from its proved L8 values and L4 weak gradients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance minimumH1Source_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform quadratic control of a joint family whose spatial first jet
vanishes at the normal center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

local instance heatFamilyHessianDualNormedGroup : NormedAddCommGroup (FourSpace →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance heatFamilyHessianDualNormedSpace : NormedSpace ℝ (FourSpace →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance heatFamilyHessianBilinearNormedGroup_r9d9562_1 :
    NormedAddCommGroup (FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance heatFamilyHessianBilinearNormedSpace_r9d9562_1 :
    NormedSpace ℝ (FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
def heatFamilySpatialFDeriv (F : HeatRadialFrameSpace → ℝ)
    (z : HeatRadialFrameSpace) : FourSpace →L[ℝ] ℝ :=
  (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ FourSpace CoordinateFrameSpace)

theorem heatFamilySpatialFDeriv_slice (F : HeatRadialFrameSpace → ℝ)
    (z : HeatRadialFrameSpace) (hF : DifferentiableAt ℝ F z) :
    fderiv ℝ (fun x : FourSpace => F (x, z.2)) z.1 = heatFamilySpatialFDeriv F z := by
  have harg : HasFDerivAt (fun x : FourSpace => (x, z.2))
      (ContinuousLinearMap.inl ℝ FourSpace CoordinateFrameSpace) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  exact (hF.hasFDerivAt.comp z.1 harg).fderiv

theorem heatFamily_quadratic_bound (F : HeatRadialFrameSpace → ℝ)
    (hF : ContDiff ℝ 2 F) (R : ℝ) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ q ∈ K,
      F (0, q) = 0 → fderiv ℝ (fun x : FourSpace => F (x, q)) 0 = 0 →
      ∀ x ∈ closedBall (0 : FourSpace) R, ‖F (x, q)‖ ≤ C * ‖x‖ ^ 2 := by
  let L : FourSpace →L[ℝ] HeatRadialFrameSpace := ContinuousLinearMap.inl ℝ _ _
  let G := heatFamilySpatialFDeriv F
  have hG : ContDiff ℝ 1 G := (hF.fderiv_right (m := 1) (by norm_num)).clm_comp contDiff_const
  let H := fun z : HeatRadialFrameSpace => (fderiv ℝ G z).comp L
  have hH : Continuous H := (hG.continuous_fderiv one_ne_zero).clm_comp_const L
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : FourSpace) R).prod hK).bddAbove_image
    hH.norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q hq hf0 hd0 x hx
  have hslice : ContDiff ℝ 2 (fun x : FourSpace => F (x, q)) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  apply fourHeat_quadratic_bound_of_hessian _ hslice hf0 hd0 R (max C 0) (le_max_right _ _) _ x hx
  intro y hy
  have he : (fun x : FourSpace => fderiv ℝ (fun u : FourSpace => F (u, q)) x) =
      fun x => G (x, q) := by
    funext x
    exact heatFamilySpatialFDeriv_slice F (x, q) (hF.differentiable two_ne_zero _)
  have harg : HasFDerivAt (fun x : FourSpace => (x, q)) L y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const q y)
  have hGd : HasFDerivAt G (fderiv ℝ G (y, q)) (y, q) :=
    (hG.differentiable one_ne_zero (y, q)).hasFDerivAt
  have hd : fderiv ℝ (fun x : FourSpace => G (x, q)) y = H (y, q) :=
    (HasFDerivAt.comp (f := fun x : FourSpace => (x, q)) (g := G) y hGd harg).fderiv
  change ‖fderiv ℝ (fun z : FourSpace => fderiv ℝ (fun u : FourSpace => F (u, q)) z) y‖ ≤ _
  rw [he, hd]
  exact (hC (mem_image_of_mem _ (show (y, q) ∈ closedBall (0 : FourSpace) R ×ˢ K from ⟨hy, hq⟩))).trans (le_max_left _ _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The polynomial and its first spatial derivatives are jointly
continuous in time, normal vector and initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

theorem heatFamilyPolynomial_continuous (u : Fin 4 → HeatRadialFrameSpace → ℝ)
    (hu : ∀ m, Continuous (u m)) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      fourHeatPolynomial (fun m x => u m (x, z.2.2)) z.1 z.2.1) := by
  have h0 := (hu 0).comp (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  have h1 := (hu 1).comp (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  have h2 := (hu 2).comp (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  have h3 := (hu 3).comp (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  exact ((h0.add (continuous_fst.mul h1)).add ((continuous_fst.pow 2).mul h2)).add
    ((continuous_fst.pow 3).mul h3)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar heat kernel is obtained from actual evaluation columns.
Its integral action, symmetry and diagonal follow from the semigroup law. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance scalarKernel_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuity and strict positivity of the actual subcritical minimizer.
Its H1 forcing is constructed, then local H3 and Fourier inversion give the
continuous representative needed by the proved strong minimum principle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance minimumContinuity_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual nonnegative normalized subcritical minimum has a strictly
positive smooth representative; continuity and all source regularity are proved. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local instance minimumSmoothness_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sharp scalar Sobolev inequality and the two Weyl gaps follow from
actual variational minima, their proved positive smooth regularity, Euler
rigidity and the critical exponent limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local instance sharpScalar_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual regularized Weyl energy and sharp scalar inequality give
the limiting Holder inequality needed for equality rigidity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance gapLimitFrameCompact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
local instance gapLimitProbability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory09
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The exact/coexact differential identities underlying cancellation of
the nonzero two-form spectrum in the signed trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothTwoFormDDeltaLinear : smoothTwoForms o →ₗ[ℝ] smoothTwoForms o :=
  smoothOneFormExteriorLinear.comp smoothTwoFormCodifferentialLinear

end
end PositiveEinsteinFour.Geometry
end


section

/-! The cokernel of actual smooth divergence is measured exactly by the
scalar integral. No upper-degree index identity is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M}

local instance divergenceMeanCompactFrames : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

def smoothScalarMean (g : SmoothMetric M) (o : FrameOrientation g) :
    SmoothScalar (M := M) →ₗ[ℝ] ℝ where
  toFun f := ∫ e, f.val e.base ∂canonicalFrameMeasure g o
  map_add' f h := integral_add
    ((f.property.continuous.comp (continuous_frameBase g)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((h.property.continuous.comp (continuous_frameBase g)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  map_smul' r f := by
    change (∫ e, r * f.val e.base ∂canonicalFrameMeasure g o) = _
    exact integral_const_mul r _

theorem smoothScalarMean_const (o : FrameOrientation g) (r : ℝ) :
    smoothScalarMean g o (smoothScalarConst r) = r := by
  simp [smoothScalarMean, smoothScalarConst]

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

/-! Integration of the genuine one-form diagonal recovers the spectral heat trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance instIsProbabilityMeasureNormalizedVolume_3 : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The de Rham heat density has the Euler index as its integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance instIsProbabilityMeasureNormalizedVolume_4 : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! A common actual normal chart and cutoff for all three Euler heat degrees. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

variable {D : HeatNormalFrameData g o c e}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance heatEulerCommon_probability : MeasureTheory.IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar members have uniform quadratic spectral error. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric MeasureTheory
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
local instance scalarUniform_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The proved signature integral in the original metric-volume convention.
The numerical Hausdorff normalization is displayed, not assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

omit [CompactSpace M] [Nonempty M] in
theorem normalizedChartFactor_inv_toReal (g : SmoothMetric M) :
    ((normalizedChartFactor g).toReal)⁻¹ = totalVolume g / riemannianChartFactor.toReal := by
  rw [normalizedChartFactor, ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((totalVolume g)⁻¹ * riemannianChartFactor.toReal)⁻¹ = _
  rw [mul_inv, inv_inv, div_eq_mul_inv]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry11
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The radial determinant estimate with the actual volume factor retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instNormedAddCommGroupMat3_5
local instance instNormedSpaceRealMat3_3_r9d9562_1 : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace
/-- The two time-zero energies and the parallel-frame/Jacobi/polar construction give
the manuscript's upper-volume deficit. -/
theorem normalized_volume_ratio_upper_of_frame_flow
    (g : SmoothMetric M) [CompactSpace (FrameBundle g)]
    {μ : Measure (FrameBundle g)} [IsProbabilityMeasure μ]
    (φ : FrameFlow g μ)
    (hC : Continuous (frameCurvatureField g))
    (hH : Continuous (frameCurvatureDerivative g))
    (hpoint : ∀ t e, HasDerivAt
      (fun r => frameCurvatureField g (φ.map r e))
      (frameCurvatureDerivative g (φ.map t e)) t)
    {s : ℝ}
    (hCmean : (∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂μ) = (3 / 2) * s)
    (hHmean : (∫ e, ‖frameCurvatureDerivative g e‖ ^ 2 ∂μ) ≤ (9 / 4) * s)
    (d : (u : ℝ) → FrameBundle g → Jacobi.RegularJacobi (Real.pi * u))
    (hR : ∀ u e r, (d u e).R r = 1 + frameCurvatureField g (φ.map r e))
    (hpos : ∀ u e r, ((d u e).R r).PosSemidef)
    (htrace : ∀ u e r, ((d u e).R r).trace = 3)
    (hD : ∀ u, 0 < u → u < 1 → Integrable (fun e => (d u e).truncatedDensity) μ)
    (hD0 : IntervalIntegrable (fun u => ∫ e, (d u e).truncatedDensity ∂μ)
      volume 0 (5 / 8))
    (hD1 : IntervalIntegrable (fun u => ∫ e, (d u e).truncatedDensity ∂μ)
      volume (5 / 8) 1)
    (hpolar : volumeRatio g / riemannianChartFactor.toReal ≤ (3 * Real.pi / 4) *
      ((∫ u in (0 : ℝ)..(5 / 8), ∫ e, (d u e).truncatedDensity ∂μ) +
        ∫ u in (5 / 8 : ℝ)..1, ∫ e, (d u e).truncatedDensity ∂μ)) :
    volumeRatio g / riemannianChartFactor.toReal ≤ 1 - (3 / 40) * s := by
  have hs : 0 ≤ s := by
    have hnonneg : 0 ≤ ∫ e, ‖frameCurvatureField g e‖ ^ 2 ∂μ :=
      integral_nonneg (fun _ => sq_nonneg _)
    rw [hCmean] at hnonneg
    linarith
  have hLip (u : ℝ) (_hu : 0 < u) (_hu1 : u < 1) (e : FrameBundle g) :
      ∃ L : ℝ, 0 ≤ L ∧ ∀ a b,
        ‖Averages.sineWeight a • Jacobi.radialCurvature (d u e).R (Real.pi * u) a -
          Averages.sineWeight b • Jacobi.radialCurvature (d u e).R (Real.pi * u) b‖ ≤
            L * |a - b| := by
    obtain ⟨L, hL, hbound⟩ := frameWeighted_lipschitz φ hC hH hpoint (Real.pi * u) e
    refine ⟨L, hL, ?_⟩
    intro a b
    simpa only [Jacobi.radialCurvature, hR, add_sub_cancel_left, mul_comm]
      using hbound a b
  exact Jacobi.volume_ratio_upper_of_jacobi d hs
    (curvatureCurve_hasDerivAt φ hC hH hpoint)
    (curvatureCurve_energy φ hC hCmean)
    (curvatureDerivativeCurve_energy φ hH hHmean)
    hR hpos htrace hLip hD hD0 hD1 hpolar

end

end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Averaging the lower polar integral over the actual frame probability. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Matrix MeasureTheory Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def actualBallRadialMass (g : SmoothMetric M) (hRic : RicciThree g) (R : ℝ)
    (e : FrameBundle g) : ℝ≥0∞ :=
  ∫⁻ r in Ioo (0 : ℝ) R, ENNReal.ofReal |((actualJacobiSolution g hRic e).J r).det|

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Dominated convergence for the actual averaged lower Jacobi comparison. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Jacobi Filter
open scoped Manifold ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M]

def actualFlatKernelDeterminant (g : SmoothMetric M) (t : ℝ) (N : ℕ)
    (e : FrameBundle g) : ℝ :=
  (1 - curvatureKernel (scaledFlatGreen t N)
    (fun i => actualJacobiCurvature g e (((i.val + 1 : ℕ) : ℝ) * meshStep t N))).det

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact classification with only the published half-conformally-flat
model identification left explicit. The Hodge/index, analytic and covering
inputs are all supplied by their actual proofs. -/

namespace PositiveEinsteinFour
open EinsteinFour _root_.OAI.PositiveEinsteinFour.Geometry
open scoped Manifold ContDiff
noncomputable section
universe u

/-- The Derdzinski--Hitchin special case applies after establishing
Weyl vanishing. -/
def ModelOrientedInputs (X : ClosedOrientedMetricFour.{u}) : Prop :=
  let : MeasurableSpace X.manifold := borel X.manifold
  let : BorelSpace X.manifold := ⟨rfl⟩
  ∀ (g : SmoothMetric X.manifold) (o : FrameOrientation g),
    RicciThree g → DerdzinskiHitchinInput g o

structure ModelClassificationInputs (_M : Type u) : Prop where
  oriented : ∀ X : ClosedOrientedMetricFour.{u}, ModelOrientedInputs X

end
end PositiveEinsteinFour
end


section

/-! Radial projection onto the sphere of radius pi and its tangent
identity, used to descend the round exponential through its boundary. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology InnerProductSpace
noncomputable section

def roundBoundaryProjection (v : FourSpace) : FourSpace := Real.pi • (‖v‖⁻¹ • v)

theorem roundBoundaryProjection_norm (v : FourSpace) (hv : v ≠ 0) :
    ‖roundBoundaryProjection v‖ = Real.pi := by
  rw [roundBoundaryProjection, norm_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv), mul_one]

theorem roundBoundaryProjection_differentiableAt (v : FourSpace) (hv : v ≠ 0) :
    DifferentiableAt ℝ roundBoundaryProjection v := by
  have hn : DifferentiableAt ℝ (fun x : FourSpace => ‖x‖) v :=
    (contDiffAt_norm ℝ hv : ContDiffAt ℝ 1 (fun x : FourSpace => ‖x‖) v).differentiableAt one_ne_zero
  exact ((hn.inv (norm_ne_zero_iff.mpr hv)).smul differentiableAt_id).const_smul Real.pi

theorem roundBoundaryProjection_derivative_tangent (v : FourSpace) (hv : v ≠ 0)
    (w : FourSpace) :
    inner ℝ (‖v‖⁻¹ • v) (fderiv ℝ roundBoundaryProjection v w) = 0 := by
  have hd := (hasStrictFDerivAt_norm_sq (roundBoundaryProjection v)).hasFDerivAt.comp v
    (roundBoundaryProjection_differentiableAt v hv).hasFDerivAt
  have heq : (fun x : FourSpace => ‖roundBoundaryProjection x‖ ^ 2) =ᶠ[𝓝 v]
      (fun _ => Real.pi ^ 2) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hv] with x hx
    rw [roundBoundaryProjection_norm x hx]
  have hc : HasFDerivAt (fun x : FourSpace => ‖roundBoundaryProjection x‖ ^ 2)
      (0 : FourSpace →L[ℝ] ℝ) v :=
    (hasFDerivAt_const (Real.pi ^ 2) v).congr_of_eventuallyEq heq
  have hzero := hd.unique hc
  have hz := congrArg (fun A : FourSpace →L[ℝ] ℝ => A w) hzero
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    innerSL_apply_apply, zero_apply] at hz
  rw [roundBoundaryProjection, real_inner_smul_left, two_smul] at hz
  nlinarith [Real.pi_pos]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Explicit polar coordinates on the actual round four-sphere. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped BigOperators
noncomputable section

theorem roundPolarPoint_zero (q : Directions) : roundPolarPoint 0 q = roundNorth := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [roundNorth, roundPolarPoint, roundPolarVector]
  · simp [roundNorth, roundPolarPoint, roundPolarVector]

theorem roundPolarPoint_pi (q : Directions) :
    roundPolarPoint Real.pi q = antipode roundNorth := by
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [roundNorth, roundPolarPoint, roundPolarVector]
  · simp [roundNorth, roundPolarPoint, roundPolarVector]

def roundTail (p : RoundSphere4) : FourSpace :=
  WithLp.toLp 2 (fun i => p.val i.succ)

theorem roundTail_norm_sq (p : RoundSphere4) :
    ‖roundTail p‖ ^ 2 = 1 - (p.val 0) ^ 2 := by
  have hp := congrArg (fun r : ℝ => r ^ 2) p.property
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] at hp
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i : Fin 4, (p.val i.succ) ^ 2) = _
  nlinarith only [hp]

theorem roundFirst_bounds (p : RoundSphere4) : p.val 0 ∈ Icc (-1 : ℝ) 1 := by
  have hn := sq_nonneg ‖roundTail p‖
  rw [roundTail_norm_sq] at hn
  constructor <;> nlinarith [sq_nonneg (p.val 0 + 1), sq_nonneg (p.val 0 - 1)]

theorem roundTail_norm_arccos (p : RoundSphere4) :
    Real.sin (Real.arccos (p.val 0)) = ‖roundTail p‖ := by
  rw [Real.sin_arccos, ← roundTail_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem exists_roundPolarPoint (p : RoundSphere4) :
    ∃ t ∈ Icc (0 : ℝ) Real.pi, ∃ q : Directions, p = roundPolarPoint t q := by
  let t := Real.arccos (p.val 0)
  have ht : t ∈ Icc (0 : ℝ) Real.pi := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hcos : Real.cos t = p.val 0 := Real.cos_arccos (roundFirst_bounds p).1 (roundFirst_bounds p).2
  have hsin : Real.sin t = ‖roundTail p‖ := roundTail_norm_arccos p
  by_cases hn : roundTail p = 0
  · refine ⟨t, ht, firstDirection, ?_⟩
    have hs : Real.sin t = 0 := by rw [hsin, hn, norm_zero]
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hcos.symm
    · have hi := congrArg (fun w : FourSpace => w i) hn
      change p.val i.succ = Real.sin t * firstDirection.val i
      rw [hs, zero_mul]
      exact hi
  · let q : Directions := ⟨‖roundTail p‖⁻¹ • roundTail p, by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)]⟩
    refine ⟨t, ht, q, ?_⟩
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hcos.symm
    · change p.val i.succ = Real.sin t * (‖roundTail p‖⁻¹ * p.val i.succ)
      rw [hsin, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hn), one_mul]

theorem roundTail_zero_cases (p : RoundSphere4) (hp : roundTail p = 0) :
    p = roundNorth ∨ p = antipode roundNorth := by
  have hsq := roundTail_norm_sq p
  rw [hp, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hsq
  have heq : (p.val 0 - 1) * (p.val 0 + 1) = 0 := by nlinarith only [hsq]
  rcases mul_eq_zero.mp heq with hpos | hneg
  · left
    have hzero : p.val 0 = 1 := by linarith only [hpos]
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [roundNorth] using hzero
    · have hi := congrArg (fun v : FourSpace => v i) hp
      simpa [roundNorth, roundTail] using hi
  · right
    have hzero : p.val 0 = -1 := by linarith only [hneg]
    apply Subtype.ext
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [roundNorth] using hzero
    · have hi := congrArg (fun v : FourSpace => v i) hp
      simpa [roundNorth, roundTail] using hi

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local chart argument needed to turn zero boundary derivatives
into a single endpoint of the round exponential. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

omit [IsManifold I4 ∞ M] in
theorem zero_chart_derivative_locally_constant (F : FourSpace → M) (U : Set FourSpace)
    (hU : IsOpen U) (hF : ContinuousOn F U)
    (hD : ∀ x ∈ U, ∀ c : M, F x ∈ (chartAt FourSpace c).source →
      HasFDerivAt (fun y => chartAt FourSpace c (F y)) (0 : FourSpace →L[ℝ] FourSpace) x) :
    IsLocallyConstant (fun x : U => F x.val) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  let c := F x.val
  have hc : F x.val ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  have hn : U ∩ F ⁻¹' (chartAt FourSpace c).source ∈ 𝓝 x.val :=
    inter_mem (hU.mem_nhds x.property)
      ((hF x.val x.property).continuousAt (hU.mem_nhds x.property) |>.preimage_mem_nhds
        ((chartAt FourSpace c).open_source.mem_nhds hc))
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hn
  have hzero (y : FourSpace) (hy : y ∈ ball x.val r) :
      HasFDerivAt (fun z => chartAt FourSpace c (F z)) (0 : FourSpace →L[ℝ] FourSpace) y :=
    hD y (hb hy).1 c (hb hy).2
  have hconst (y : FourSpace) (hy : y ∈ ball x.val r) :
      chartAt FourSpace c (F y) = chartAt FourSpace c (F x.val) := by
    apply (convex_ball x.val r).is_const_of_fderivWithin_eq_zero
      (fun z hz => (hzero z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => ?_) hy (mem_ball_self hr)
    rw [fderivWithin_of_isOpen isOpen_ball hz, (hzero z hz).fderiv]
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
    (ball_mem_nhds x.val hr)] with y hy
  exact (chartAt FourSpace c).injOn (hb hy).2 hc (hconst y.val hy)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two eigenvalues of unit parallel Weyl curvature are expressed by
an actual orthogonal projection, without choosing eigenvectors. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian Matrix
open scoped BigOperators
noncomputable section

theorem unitWeylProjection_trace (A : Mat) (ht : traceFree A) :
    Matrix.trace (unitWeylProjection A) = 1 := by
  have ht' : Matrix.trace A = 0 := ht
  simp only [unitWeylProjection, Matrix.trace_smul, Matrix.trace_add, ht',
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  norm_num

theorem unitWeyl_upper_posSemidef (A : Mat) (hs : symmetric A)
    (hp : A * A = A + (2 : ℝ) • (1 : Mat)) :
    ((2 : ℝ) • (1 : Mat) - A).PosSemidef := by
  let P := unitWeylProjection A
  have hP : P.IsHermitian := unitWeylProjection_symmetric A hs
  have hQ : (1 - P : Mat).IsHermitian := Matrix.isHermitian_one.sub hP
  have hid : IsIdempotentElem (1 - P) := (unitWeylProjection_idempotent A hp).one_sub
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 - P)
  rw [hQ.eq, hid.eq] at h
  have h' := h.smul (show (0 : ℝ) ≤ 3 by norm_num)
  convert h' using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  simp only [P, unitWeylProjection, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.add_apply, smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Vanishing angular derivatives imply that every radial geodesic in the
round branch reaches the same point at time pi. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def roundBoundaryEndpoint (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) : M :=
  frameExponential g o e (roundBoundaryProjection v)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous manifold curve with zero derivative in each chart is
constant. Only the one-dimensional statement needed for boundary circles. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem zero_chart_curve_constant (F : ℝ → M) (hF : Continuous F)
    (hD : ∀ t (c : M), F t ∈ (chartAt FourSpace c).source →
      HasDerivAt (fun s => chartAt FourSpace c (F s)) (0 : FourSpace) t)
    (s t : ℝ) : F s = F t := by
  have hLC : IsLocallyConstant F := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    let c := F x
    have hc : F x ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
    have hn : F ⁻¹' (chartAt FourSpace c).source ∈ 𝓝 x :=
      hF.continuousAt.preimage_mem_nhds ((chartAt FourSpace c).open_source.mem_nhds hc)
    obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp hn
    have heq (y : ℝ) (hy : y ∈ ball x r) : chartAt FourSpace c (F y) = chartAt FourSpace c (F x) := by
      exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball x r).isPreconnected
        (fun z hz => (hD z c (hb hz)).differentiableAt.differentiableWithinAt)
        (fun z hz => (hD z c (hb hz)).deriv) hy (mem_ball_self hr)
    filter_upwards [ball_mem_nhds x hr] with y hy
    exact (chartAt FourSpace c).injOn (hb hy) hc (heq y hy)
  exact hLC.apply_eq_of_preconnectedSpace s t

end
end PositiveEinsteinFour.Geometry
end


section

/-! The round-sphere covering map, with its polar values
and surjectivity supplied by global exponential coverage. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped BigOperators Manifold ContDiff _root_.Topology
noncomputable section

def roundLog (p : RoundSphere4) : FourSpace :=
  if roundTail p = 0 then Real.arccos (p.val 0) • coordinateVector 0
  else (Real.arccos (p.val 0) / ‖roundTail p‖) • roundTail p

theorem roundTail_polar (t : ℝ) (q : Directions) :
    roundTail (roundPolarPoint t q) = Real.sin t • q.val := by
  ext i
  rfl

theorem roundLog_polar_interior (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) Real.pi) (q : Directions) :
    roundLog (roundPolarPoint t q) = t • q.val := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hn : roundTail (roundPolarPoint t q) ≠ 0 := by
    rw [roundTail_polar]
    exact smul_ne_zero hs.ne' (unitSphere_ne_zero q)
  rw [roundLog, ite_eq_right hn, roundPolarPoint_first, Real.arccos_cos ht.1.le ht.2.le,
    roundTail_polar, norm_smul, Real.norm_eq_abs, abs_of_pos hs, q.property, mul_one,
    smul_smul, div_mul_cancel₀ _ hs.ne']

theorem roundLog_polar_zero (q : Directions) : roundLog (roundPolarPoint 0 q) = 0 := by
  rw [roundLog, roundTail_polar, Real.sin_zero, zero_smul, ite_eq_left rfl,
    roundPolarPoint_first, Real.cos_zero, Real.arccos_one, zero_smul]

theorem roundLog_polar_pi (q : Directions) :
    roundLog (roundPolarPoint Real.pi q) = Real.pi • coordinateVector 0 := by
  rw [roundLog, roundTail_polar, Real.sin_pi, zero_smul, ite_eq_left rfl,
    roundPolarPoint_first, Real.cos_pi, Real.arccos_neg_one]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def roundSphereMap (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (p : RoundSphere4) : M := frameExponential g o e (roundLog p)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Endpoint distance estimates for the actual sphere map. These also
control its continuity at both polar-coordinate singularities. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section

theorem roundLog_norm (p : RoundSphere4) : ‖roundLog p‖ = Real.arccos (p.val 0) := by
  unfold roundLog
  split_ifs with hp
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.arccos_nonneg _)]
    simp [coordinateVector]
  · rw [norm_smul, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (Real.arccos_nonneg _), abs_of_nonneg (norm_nonneg _),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hp)]

theorem roundLog_north : roundLog roundNorth = 0 := by
  rw [← roundPolarPoint_zero firstDirection]
  exact roundLog_polar_zero firstDirection

theorem roundLog_south : roundLog (antipode roundNorth) = Real.pi • coordinateVector 0 := by
  rw [← roundPolarPoint_pi firstDirection]
  exact roundLog_polar_pi firstDirection

def roundAntipodalPoint {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
    (g : SmoothMetric M) (o : FrameOrientation g) (e : FrameBundle g) : M :=
  frameExponential g o e (Real.pi • coordinateVector 0)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem roundSphereMap_north (e : FrameBundle g) :
    roundSphereMap g o e roundNorth = e.base := by
  rw [roundSphereMap, roundLog_north, frameExponential_zero]

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem roundSphereMap_south (e : FrameBundle g) :
    roundSphereMap g o e (antipode roundNorth) = roundAntipodalPoint g o e := by
  rw [roundSphereMap, roundLog_south]
  rfl

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem roundSphereMap_distance_north (e : FrameBundle g) (p : RoundSphere4) :
    metricEDistance g e.base (roundSphereMap g o e p) ≤
      ENNReal.ofReal (Real.arccos (p.val 0)) := by
  simpa only [roundLog_norm, roundSphereMap] using frameExponential_distance g o e (roundLog p)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A parallel two-form has constant norm on the actual compact connected
manifold. This uses the existing global geodesics, not a holonomy premise. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem parallel_twoForm_along_flow (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0)
    (e : FrameBundle g) (i : Fin 4) (t : ℝ) :
    twoFormFramedValue o u.val (parallelFrameFlowMap g i t e) = twoFormFramedValue o u.val e := by
  ext a
  have hd (r : ℝ) : HasDerivAt (fun s =>
      twoFormFramedValue o u.val (parallelFrameFlowMap g i s e) a) 0 r := by
    have h := u.property.framedValue_parallel_derivative
      (fun s => parallelFrameFlowMap g i s e) r i
      (parallelFrameFlowMap_curve_continuous g i e).continuousAt
      (parallelFrameFlowMap_primitive g i e r) a
    rw [hz] at h
    exact h
  have h := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t 0
  simpa only [parallelFrameFlowMap_zero] using h

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem parallel_twoForm_norm_along_flow (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0)
    (e : FrameBundle g) (i : Fin 4) (t : ℝ) :
    ‖u.val (parallelFrameFlowMap g i t e).base‖ = ‖u.val e.base‖ := by
  have h := congrArg frameTensorSquareNorm (parallel_twoForm_along_flow u hz e i t)
  rw [twoFormFramedValue_norm, twoFormFramedValue_norm] at h
  nlinarith [norm_nonneg (u.val (parallelFrameFlowMap g i t e).base), norm_nonneg (u.val e.base)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sphere map is continuous at both poles as well as in the ordinary
polar chart; the south-pole bound uses the proved common endpoint. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Bundle Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem roundTail_continuous : Continuous roundTail := by
  unfold roundTail
  fun_prop

theorem roundLog_continuousAt {p : RoundSphere4} (hp : roundTail p ≠ 0) :
    ContinuousAt roundLog p := by
  have h := (roundPolarAngle_continuous.continuousAt.div
    roundTail_continuous.norm.continuousAt (norm_ne_zero_iff.mpr hp)).smul
      roundTail_continuous.continuousAt
  apply h.congr_of_eventuallyEq
  filter_upwards [roundTail_continuous.continuousAt.preimage_mem_nhds
    (isOpen_compl_singleton.mem_nhds hp)] with q hq
  exact ite_eq_right hq

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual sphere exponential and its continuous ambient formula.
This fixes the topology at the center of polar coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped _root_.Topology
noncomputable section

def roundSphereExponential (v : FourSpace) : RoundSphere4 :=
  if hv : v = 0 then roundNorth else
    roundPolarPoint ‖v‖ ⟨‖v‖⁻¹ • v, by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩

theorem roundSphereExponential_zero : roundSphereExponential 0 = roundNorth := by
  simp [roundSphereExponential]

theorem roundSphereExponential_radial (t : ℝ) (ht : 0 ≤ t) (q : Directions) :
    roundSphereExponential (t • q.val) = roundPolarPoint t q := by
  by_cases hz : t = 0
  · subst t
    simp [roundSphereExponential_zero, roundPolarPoint_zero]
  have hn : ‖t • q.val‖ = t := by
    rw [norm_smul, q.property, mul_one, Real.norm_eq_abs, abs_of_nonneg ht]
  have hv : t • q.val ≠ 0 := smul_ne_zero hz (unitSphere_ne_zero q)
  rw [roundSphereExponential, dite_eq_right hv]
  congr 1
  apply Subtype.ext
  change ‖t • q.val‖⁻¹ • (t • q.val) = q.val
  rw [hn, smul_smul, inv_mul_cancel₀ hz, one_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A self-dual two-form of norm sqrt(2) is an orthogonal complex structure
in each positively oriented orthonormal frame. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators
noncomputable section

theorem selfDual_twoFormMatrix_square (a : TwoFormFour)
    (ha : twoFormHodge a = a) (hn : ‖a‖ ^ 2 = 2) :
    twoFormMatrix a * twoFormMatrix a = -(1 : Mat4) := by
  have h3 : a 3 = a 2 := congrArg (fun v : TwoFormFour => v 2) ha
  have h4 : a 4 = -a 1 := by
    have h := congrArg (fun v : TwoFormFour => v 1) ha
    change -a 4 = a 1 at h
    linarith
  have h5 : a 5 = a 0 := congrArg (fun v : TwoFormFour => v 0) ha
  have hs : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1 := by
    have he := EuclideanSpace.real_norm_sq_eq a
    simp [Fin.sum_univ_succ, h3, h4, h5] at he
    nlinarith only [he, hn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoFormMatrix, Matrix.mul_apply, Fin.sum_univ_succ, h3, h4, h5] <;>
    nlinarith only [hs]

theorem selfDual_twoFormMatrix_orthogonal (a : TwoFormFour)
    (ha : twoFormHodge a = a) (hn : ‖a‖ ^ 2 = 2) :
    (twoFormMatrix a)ᵀ * twoFormMatrix a = 1 := by
  rw [twoFormMatrix_skew, Matrix.neg_mul, selfDual_twoFormMatrix_square a ha hn, neg_neg]

open scoped Manifold ContDiff
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem unit_selfDual_frame_complex (w : smoothTwoForms o)
    (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hnorm : ∀ x, ‖w.val x‖ ^ 2 = 2) (e : FrameBundle g) (he : e ∈ o.positive) :
    twoFormMatrix (twoFormFrameValue o w.val e) * twoFormMatrix (twoFormFrameValue o w.val e) =
      -(1 : Mat4) ∧
    (twoFormMatrix (twoFormFrameValue o w.val e))ᵀ *
      twoFormMatrix (twoFormFrameValue o w.val e) = 1 := by
  have hs : twoFormHodge (twoFormFrameValue o w.val e) = twoFormFrameValue o w.val e := by
    rw [← twoFormFrameValue_hodge o w.val e he]
    congr 1
    funext x
    exact hstar x
  have hn : ‖twoFormFrameValue o w.val e‖ ^ 2 = 2 := by
    rw [twoFormFrameValue_norm, hnorm]
  exact ⟨selfDual_twoFormMatrix_square _ hs hn, selfDual_twoFormMatrix_orthogonal _ hs hn⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! An explicit open polar chart on the standard sphere, including the
north pole and excluding precisely the south pole. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set Filter
open scoped _root_.Topology
noncomputable section

theorem roundSphereExponential_log (p : RoundSphere4) :
    roundSphereExponential (roundLog p) = p := by
  obtain ⟨t, ht, q, rfl⟩ := exists_roundPolarPoint p
  by_cases h0 : t = 0
  · subst t
    rw [roundLog_polar_zero, roundSphereExponential_zero, roundPolarPoint_zero]
  by_cases hπ : t = Real.pi
  · subst t
    rw [roundLog_polar_pi]
    change roundSphereExponential (Real.pi • firstDirection.val) = _
    rw [roundSphereExponential_radial _ Real.pi_pos.le,
      roundPolarPoint_pi, roundPolarPoint_pi]
  · rw [roundLog_polar_interior t
      ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 hπ⟩,
      roundSphereExponential_radial t ht.1]

theorem roundLog_norm_lt_pi {p : RoundSphere4} (hp : p ≠ antipode roundNorth) :
    ‖roundLog p‖ < Real.pi := by
  obtain ⟨t, ht, q, rfl⟩ := exists_roundPolarPoint p
  rw [roundLog_norm, roundPolarPoint_first, Real.arccos_cos ht.1 ht.2]
  apply lt_of_le_of_ne ht.2
  intro heq
  exact hp (heq ▸ roundPolarPoint_pi q)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The real circle action generated by an orthogonal complex structure. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
noncomputable section

def complexCircleMatrix (J : Mat4) (t : ℝ) : Mat4 :=
  Real.cos t • (1 : Mat4) + Real.sin t • J

theorem complexCircleMatrix_orthogonal (J : Mat4) (hsk : Jᵀ = -J)
    (hsq : J * J = -(1 : Mat4)) (t : ℝ) :
    (complexCircleMatrix J t)ᵀ * complexCircleMatrix J t = 1 := by
  simp only [complexCircleMatrix, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_one, hsk, smul_neg, Matrix.add_mul, Matrix.mul_add,
    Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, hsq]
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination ((1 : Mat4) i j) * Real.sin_sq_add_cos_sq t

def complexCircleVector (J : Mat4) (q : FourSpace) (t : ℝ) : FourSpace :=
  Real.cos t • q + Real.sin t • (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J q)

theorem complexCircleVector_eq_matrix (J : Mat4) (q : FourSpace) (t : ℝ) :
    complexCircleVector J q t =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (complexCircleMatrix J t) q := by
  rw [complexCircleMatrix, map_add, map_smul, map_smul, map_one]
  rfl

theorem complexCircleVector_norm (J : Mat4) (hsk : Jᵀ = -J)
    (hsq : J * J = -(1 : Mat4)) (q : FourSpace) (t : ℝ) :
    ‖complexCircleVector J q t‖ = ‖q‖ := by
  rw [complexCircleVector_eq_matrix]
  exact (orthogonalEuclideanIsometry (complexCircleMatrix J t)
    (complexCircleMatrix_orthogonal J hsk hsq t)).norm_map q

theorem complexCircleVector_hasDerivAt (J : Mat4) (hsq : J * J = -(1 : Mat4))
    (q : FourSpace) (t : ℝ) :
    HasDerivAt (complexCircleVector J q)
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J (complexCircleVector J q t)) t := by
  have hJJ : Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J q) = -q := by
    change ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J) *
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J)) q = -q
    rw [← map_mul, hsq, map_neg, map_one]
    rfl
  refine (((Real.hasDerivAt_cos t).smul_const q).add
    ((Real.hasDerivAt_sin t).smul_const
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J q))).congr_deriv ?_
  · rw [complexCircleVector, map_add, map_smul, map_smul, hJJ]
    module

theorem complexCircleVector_zero (J : Mat4) (q : FourSpace) : complexCircleVector J q 0 = q := by
  simp [complexCircleVector]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A symmetric projection of trace one is determined by a unit vector
in its image. This will identify the actual parallel Weyl block. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian Matrix
open scoped BigOperators
noncomputable section

theorem unitWeylProjection_eq_vector (A : Mat) (hs : symmetric A)
    (ht : traceFree A) (hp : A * A = A + (2 : ℝ) • (1 : Mat))
    (v : Fin 3 → ℝ) (hv : dotProduct v v = 1) (hAv : A *ᵥ v = (2 : ℝ) • v) :
    A = (3 : ℝ) • Matrix.vecMulVec v v - 1 := by
  have hPv : unitWeylProjection A *ᵥ v = v := by
    rw [unitWeylProjection, Matrix.smul_mulVec, Matrix.add_mulVec, hAv, Matrix.one_mulVec]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hP := symmetric_projection_trace_one (unitWeylProjection A)
    (fun i j => by
      have h := Matrix.isHermitian_iff_isSymm.mp (unitWeylProjection_symmetric A hs)
      exact congrFun (congrFun h j) i)
    (unitWeylProjection_idempotent A hp).eq (unitWeylProjection_trace A ht) v hv hPv
  ext i j
  have h := congrFun (congrFun hP i) j
  change (1 / 3 : ℝ) * (A i j + (1 : Mat) i j) = v i * v j at h
  change A i j = 3 * (v i * v j) - (1 : Mat) i j
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The pointwise speed identity in the actual round exponential chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem metric_curve_speed_congr {γ η : ℝ → M} {t : ℝ}
    (h : γ =ᶠ[𝓝 t] η) :
    metricTangentNorm g (γ t) (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) =
      metricTangentNorm g (η t) (mfderiv 𝓘(ℝ, ℝ) I4 η t 1) := by
  have hD : (show ℝ →L[ℝ] FourSpace from mfderiv 𝓘(ℝ, ℝ) I4 γ t) =
      (show ℝ →L[ℝ] FourSpace from mfderiv 𝓘(ℝ, ℝ) I4 η t) := by
    simpa only [ContinuousLinearMap.id_comp] using! h.mfderiv_eq
  let v : FourSpace := mfderiv 𝓘(ℝ, ℝ) I4 γ t 1
  let w : FourSpace := mfderiv 𝓘(ℝ, ℝ) I4 η t 1
  have hv : v = w := congrArg (fun D : ℝ →L[ℝ] FourSpace => D 1) hD
  change metricTangentNorm g (γ t) v = metricTangentNorm g (η t) w
  rw [hv, h.self_of_nhds]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal Jacobi curvature is constant along each geodesic
in the unit parallel-form branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix Jacobi
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem parallel_twoForm_frameValue_along_flow (w : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (i : Fin 4) (t : ℝ) :
    twoFormFrameValue o w.val (parallelFrameFlowMap g i t e) =
      twoFormFrameValue o w.val e := by
  apply twoFormTensor_injective
  simpa only [twoFormFramedValue_eq] using parallel_twoForm_along_flow w hz e i t

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two scalar Jacobi factors for Ricci-normalized complex curvature. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour
noncomputable section

theorem sqrt_two_inverse : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
  apply (div_eq_div_iff (by positivity : Real.sqrt 2 ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)).mpr
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem complexJacobiSlow_hasDerivAt (t : ℝ) :
    HasDerivAt complexJacobiSlow (Real.cos (t / Real.sqrt 2)) t := by
  refine (((hasDerivAt_id t).div_const (Real.sqrt 2)).sin.const_mul (Real.sqrt 2)).congr_deriv ?_
  · dsimp only [id_eq]
    field_simp

theorem complexJacobiFast_hasDerivAt (t : ℝ) :
    HasDerivAt complexJacobiFast (Real.cos (Real.sqrt 2 * t)) t := by
  refine (((hasDerivAt_id t).const_mul (Real.sqrt 2)).sin.div_const (Real.sqrt 2)).congr_deriv ?_
  · dsimp only [id_eq]
    field_simp

theorem complexJacobiSlow_velocity_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => Real.cos (s / Real.sqrt 2))
      (-(1 / 2 : ℝ) * complexJacobiSlow t) t := by
  convert ((hasDerivAt_id t).div_const (Real.sqrt 2)).cos using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp only [id_eq])
  rw [sqrt_two_inverse]
  unfold complexJacobiSlow
  ring

theorem complexJacobiFast_velocity_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => Real.cos (Real.sqrt 2 * s))
      (-2 * complexJacobiFast t) t := by
  convert ((hasDerivAt_id t).const_mul (Real.sqrt 2)).cos using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp only [id_eq])
  unfold complexJacobiFast
  rw [div_eq_mul_one_div, sqrt_two_inverse]
  ring

end
end PositiveEinsteinFour.Jacobi
end


section

/-! The exact matrix Jacobi solution for the two eigenspaces of the
Ricci-normalized complex-space-form curvature. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section

def complexModelJacobi (P : NormalMatrix) (hP : P * P = P) :
    MatrixJacobiSolution (fun _ => complexJacobiCurvature P) where
  J := complexJacobiPosition P
  V := complexJacobiVelocity P
  initial_position := by
    simp [complexJacobiPosition, complexJacobiSlow, complexJacobiFast]
  initial_velocity := by
    simp [complexJacobiVelocity]
  position_derivative t :=
    ((complexJacobiSlow_hasDerivAt t).smul_const (1 - P)).add
      ((complexJacobiFast_hasDerivAt t).smul_const P)
  velocity_derivative t := by
    have h := ((complexJacobiSlow_velocity_hasDerivAt t).smul_const (1 - P)).add
      ((complexJacobiFast_velocity_hasDerivAt t).smul_const P)
    have h' : HasDerivAt (complexJacobiVelocity P) _ t := h
    refine h'.congr_deriv ?_
    · symm
      rw [complexJacobiPosition, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
        complexJacobiCurvature_mul_complement P hP, complexJacobiCurvature_mul_projection P hP]
      ext i j
      simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
        smul_eq_mul]
      ring

theorem MatrixJacobiSolution.eq_complex_projection {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (P : NormalMatrix) (hP : P * P = P)
    (hR : ∀ s, R s = complexJacobiCurvature P) :
    d.J = complexJacobiPosition P ∧ d.V = complexJacobiVelocity P := by
  let m := complexModelJacobi P hP
  let e : MatrixJacobiSolution R :=
    { J := m.J
      V := m.V
      initial_position := m.initial_position
      initial_velocity := m.initial_velocity
      position_derivative := m.position_derivative
      velocity_derivative := fun t => by
        simpa only [hR t] using m.velocity_derivative t }
  exact d.unique e ‖complexJacobiCurvature P‖₊ (fun s => by rw [hR]; rfl)

end
end PositiveEinsteinFour.Jacobi
end


section

/-! The exact trigonometric coefficients in the Fubini--Study polar metric. -/
namespace PositiveEinsteinFour.Jacobi
noncomputable section

theorem complexJacobiSlow_sq (t : ℝ) :
    complexJacobiSlow t ^ 2 = 2 * Real.sin (t / Real.sqrt 2) ^ 2 := by
  rw [complexJacobiSlow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem complexJacobiFast_sq (t : ℝ) :
    complexJacobiFast t ^ 2 =
      2 * Real.sin (t / Real.sqrt 2) ^ 2 * Real.cos (t / Real.sqrt 2) ^ 2 := by
  have htime : Real.sqrt 2 * t = 2 * (t / Real.sqrt 2) := by
    calc
      _ = (Real.sqrt 2 * Real.sqrt 2) * (t / Real.sqrt 2) := by
        field_simp
      _ = _ := by rw [← pow_two,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [complexJacobiFast,htime,Real.sin_two_mul,div_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem complexJacobiFast_sq_sub_slow_sq (t : ℝ) :
    complexJacobiFast t ^ 2 - complexJacobiSlow t ^ 2 =
      -2 * Real.sin (t / Real.sqrt 2) ^ 4 := by
  rw [complexJacobiFast_sq,complexJacobiSlow_sq]
  have h := Real.sin_sq_add_cos_sq (t / Real.sqrt 2)
  nlinarith [sq_nonneg (Real.sin (t / Real.sqrt 2)),
    congrArg (fun x : ℝ => Real.sin (t / Real.sqrt 2) ^ 2 * x) h]

end
end PositiveEinsteinFour.Jacobi
end


section

/-! The determinant and first zero of the complex-space-form Jacobi matrix. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section

theorem rankOne_two_eigenvalue_determinant (v : Fin 3 → ℝ)
    (hv : dotProduct v v = 1) (a b : ℝ) :
    Matrix.det (a • ((1 : NormalMatrix) - Matrix.vecMulVec v v) +
      b • Matrix.vecMulVec v v) = a ^ 2 * b := by
  have hn : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_succ, pow_two, add_assoc] using hv
  have he : Matrix.det (a • ((1 : NormalMatrix) - Matrix.vecMulVec v v) +
      b • Matrix.vecMulVec v v) =
      a ^ 3 + a ^ 2 * (b - a) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
    simp [Matrix.det_fin_three, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply]
    ring
  rw [he, hn]
  ring

theorem complexJacobiPosition_det (v : Fin 3 → ℝ) (hv : dotProduct v v = 1) (t : ℝ) :
    Matrix.det (complexJacobiPosition (Matrix.vecMulVec v v) t) =
      complexJacobiSlow t ^ 2 * complexJacobiFast t :=
  rankOne_two_eigenvalue_determinant v hv _ _

theorem complexJacobiFast_radius : complexJacobiFast complexJacobiRadius = 0 := by
  unfold complexJacobiFast complexJacobiRadius
  have h : Real.sqrt 2 * (Real.pi / Real.sqrt 2) = Real.pi := by field_simp
  rw [h, Real.sin_pi, zero_div]

theorem complexJacobiFast_pos {t : ℝ} (ht : 0 < t) (hr : t < complexJacobiRadius) :
    0 < complexJacobiFast t := by
  have hs : 0 < Real.sqrt 2 := by positivity
  apply div_pos _ hs
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hs ht)
  have h := mul_lt_mul_of_pos_left hr hs
  dsimp only [complexJacobiRadius] at h
  have he : Real.sqrt 2 * (Real.pi / Real.sqrt 2) = Real.pi := by field_simp
  rwa [he] at h

theorem complexJacobiSlow_pos {t : ℝ} (ht : 0 < t) (hr : t < complexJacobiRadius) :
    0 < complexJacobiSlow t := by
  have hs : 0 < Real.sqrt 2 := by positivity
  apply mul_pos hs
  apply Real.sin_pos_of_pos_of_lt_pi (div_pos ht hs)
  have h := div_lt_div_of_pos_right hr hs
  dsimp only [complexJacobiRadius] at h
  rw [div_div, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  linarith [Real.pi_pos]

theorem complexJacobiPosition_det_pos (v : Fin 3 → ℝ) (hv : dotProduct v v = 1)
    {t : ℝ} (ht : 0 < t) (hr : t < complexJacobiRadius) :
    0 < Matrix.det (complexJacobiPosition (Matrix.vecMulVec v v) t) := by
  rw [complexJacobiPosition_det v hv]
  exact mul_pos (sq_pos_of_pos (complexJacobiSlow_pos ht hr)) (complexJacobiFast_pos ht hr)

theorem complexJacobiPosition_det_radius (v : Fin 3 → ℝ) (hv : dotProduct v v = 1) :
    Matrix.det (complexJacobiPosition (Matrix.vecMulVec v v) complexJacobiRadius) = 0 := by
  rw [complexJacobiPosition_det v hv, complexJacobiFast_radius, mul_zero]

end
end PositiveEinsteinFour.Jacobi
end


section

/-! The actual Jacobi fields and first conjugate radius in the parallel
complex-curvature branch. No model identification is used. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix Jacobi
open scoped BigOperators Manifold ContDiff Matrix.Norms.L2Operator
noncomputable section

theorem selfDual_firstThree_unit (a : TwoFormFour)
    (ha : twoFormHodge a = a) (hn : ‖a‖ ^ 2 = 2) :
    dotProduct ![a 0,a 1,a 2] ![a 0,a 1,a 2] = 1 := by
  have h3 : a 3 = a 2 := congrArg (fun b : TwoFormFour => b 2) ha
  have h4 : a 4 = -a 1 := by
    have h := congrArg (fun b : TwoFormFour => b 1) ha
    change -a 4 = a 1 at h
    linarith
  have h5 : a 5 = a 0 := congrArg (fun b : TwoFormFour => b 0) ha
  have h := EuclideanSpace.real_norm_sq_eq a
  simp [Fin.sum_univ_succ, h3, h4, h5] at h
  simp [dotProduct, Fin.sum_univ_succ]
  nlinarith only [h,hn]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem unitSelfDual_frame_firstThree (w : smoothTwoForms o)
    (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    let a := twoFormFrameValue o w.val e
    dotProduct ![a 0,a 1,a 2] ![a 0,a 1,a 2] = 1 := by
  apply selfDual_firstThree_unit
  · rw [← twoFormFrameValue_hodge o w.val e he]
    congr 1
    exact funext hstar
  · rw [twoFormFrameValue_norm, hw]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The complex line tangent is in the actual exponential kernel at the
first conjugate radius. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour Matrix
noncomputable section

theorem complexJacobiPosition_radius_mulVec (v : Fin 3 → ℝ)
    (hv : dotProduct v v = 1) :
    complexJacobiPosition (Matrix.vecMulVec v v) complexJacobiRadius *ᵥ v = 0 := by
  have hp : Matrix.vecMulVec v v *ᵥ v = v := by
    rw [Matrix.vecMulVec_mulVec, hv]
    simp
  rw [complexJacobiPosition, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.sub_mulVec, Matrix.one_mulVec, hp, sub_self, smul_zero,
    complexJacobiFast_radius, zero_smul, add_zero]

end
end PositiveEinsteinFour.Jacobi

end


section

/-! Squaring the actual complex Jacobi solution retains its two orthogonal
eigenspaces. This is the pullback metric, rather than merely its determinant. -/
namespace PositiveEinsteinFour.Jacobi
open EinsteinFour Matrix PositiveEinsteinFour.Geometry
noncomputable section

theorem jacobiBlockMatrix_transpose_mul (a : ℝ) (A : NormalMatrix) :
    (jacobiBlockMatrix a A)ᵀ * jacobiBlockMatrix a A =
      jacobiBlockMatrix (a ^ 2) (Aᵀ * A) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [jacobiBlockMatrix, Fin.sum_univ_succ, pow_two]
    · simp [jacobiBlockMatrix, Fin.sum_univ_succ]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [jacobiBlockMatrix, Fin.sum_univ_succ]
    · simp [jacobiBlockMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

end
end PositiveEinsteinFour.Jacobi
end


section

/-! Exact radial volume of the Ricci-normalized complex Jacobi solution. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Jacobi MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem complexRadialDensity_eq (t : ℝ) :
    complexRadialDensity t =
      2 * Real.sqrt 2 * Real.sin (t / Real.sqrt 2) ^ 3 * Real.cos (t / Real.sqrt 2) := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have harg : Real.sqrt 2 * t = 2 * (t / Real.sqrt 2) := by
    calc
      _ = (Real.sqrt 2 * Real.sqrt 2) * (t / Real.sqrt 2) := by field_simp
      _ = _ := by rw [hs]
  unfold complexRadialDensity complexJacobiSlow complexJacobiFast
  rw [harg, Real.sin_two_mul]
  field_simp

theorem complexRadialPrimitive_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => Real.sin (s / Real.sqrt 2) ^ 4) (complexRadialDensity t) t := by
  refine (((hasDerivAt_id t).div_const (Real.sqrt 2)).sin.pow 4).congr_deriv ?_
  · rw [complexRadialDensity_eq]
    simp only [id_eq, Nat.reduceSub, Nat.cast_ofNat]
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring

theorem complexRadial_integral (c : ℝ) :
    (∫ r in (0 : ℝ)..c, complexRadialDensity r) = Real.sin (c / Real.sqrt 2) ^ 4 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => complexRadialPrimitive_hasDerivAt r)
    (complexRadialDensity_continuous.intervalIntegrable 0 c)]
  simp

theorem complexRadialDensity_nonneg {r : ℝ} (hr : r ∈ Icc (0 : ℝ) complexJacobiRadius) :
    0 ≤ complexRadialDensity r := by
  rcases eq_or_lt_of_le hr.1 with h0 | h0
  · rw [← h0]
    simp [complexRadialDensity, complexJacobiSlow]
  rcases eq_or_lt_of_le hr.2 with hc | hc
  · rw [hc, complexRadialDensity, complexJacobiFast_radius, mul_zero]
  exact mul_nonneg (sq_nonneg _) (complexJacobiFast_pos h0 hc).le

theorem complexRadialMass_formula (c : ℝ) (hc : c ∈ Icc (0 : ℝ) complexJacobiRadius) :
    complexRadialMass c = ENNReal.ofReal (Real.sin (c / Real.sqrt 2) ^ 4) := by
  have hi : IntegrableOn complexRadialDensity (Ioc (0 : ℝ) c) :=
    complexRadialDensity_continuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hn : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) c)), 0 ≤ complexRadialDensity r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact complexRadialDensity_nonneg ⟨hr.1.le, hr.2.trans hc.2⟩
  rw [complexRadialMass, ← ofReal_integral_eq_lintegral_ofReal hi hn,
    ← intervalIntegral.integral_of_le hc.1, complexRadial_integral]

theorem complexRadialMass_radius : complexRadialMass complexJacobiRadius = 1 := by
  rw [complexRadialMass_formula _ ⟨complexJacobiRadius_pos.le, le_rfl⟩]
  have h : complexJacobiRadius / Real.sqrt 2 = Real.pi / 2 := by
    rw [complexJacobiRadius, div_div, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp [h, Real.sin_pi_div_two]

theorem complexRadialMass_le_one (c : ℝ) (hc : c ≤ complexJacobiRadius) :
    complexRadialMass c ≤ 1 := by
  rw [← complexRadialMass_radius]
  exact lintegral_mono_set (Ioc_subset_Ioc_right hc)

theorem complexRadialMass_lt_one (c : ℝ) (hc : c ∈ Ico (0 : ℝ) complexJacobiRadius) :
    complexRadialMass c < 1 := by
  rw [complexRadialMass_formula c ⟨hc.1,hc.2.le⟩]
  have hs : 0 < Real.sqrt 2 := by positivity
  have h0 : 0 ≤ c / Real.sqrt 2 := div_nonneg hc.1 hs.le
  have hlt : c / Real.sqrt 2 < Real.pi / 2 := by
    have h := div_lt_div_of_pos_right hc.2 hs
    dsimp only [complexJacobiRadius] at h
    rwa [div_div, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hn := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hp : Real.sin (c / Real.sqrt 2) < 1 := by
    have h := Real.strictMonoOn_sin (show c / Real.sqrt 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)
      from ⟨by linarith [Real.pi_pos], hlt.le⟩)
      (show Real.pi / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) from ⟨by linarith [Real.pi_pos], le_rfl⟩) hlt
    simpa only [Real.sin_pi_div_two] using h
  exact (ENNReal.ofReal_lt_one).mpr (pow_lt_one₀ hn hp (by decide : 4 ≠ 0))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The inverse sphere homeomorphism does not increase the distance
between the endpoints of an actual unit geodesic of length at most pi. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] [PreconnectedSpace M] in
theorem round_frameGeodesic_real_speed (f : FrameBundle g) (t : ℝ) :
    metricTangentNorm g (frameGeodesic g 0 f t)
      (mfderiv 𝓘(ℝ, ℝ) I4 (frameGeodesic g 0 f) t 1) = 1 := by
  have h := frameGeodesic_metric_speed g 0 f t
  rw [metricTangentENorm_eq_ofReal] at h
  have hn : 0 ≤ metricTangentNorm g (frameGeodesic g 0 f t)
      (mfderiv 𝓘(ℝ, ℝ) I4 (frameGeodesic g 0 f) t 1) := by
    rw [metricTangentNorm_eq_sqrt]
    exact Real.sqrt_nonneg _
  have hh := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal hn, ENNReal.toReal_one] using hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! The complex operator reconstructed from a two-form is equivariant
under genuine orthonormal frame changes. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormFrameValue_rotate (u : M → TwoFormFour) (e : FrameBundle g)
    (Q : OrthogonalFour) :
    twoFormFrameValue o u (e.rotate Q) = twoFormFrameAction Q.val (twoFormFrameValue o u e) := by
  have hQ : e.frame.changeMatrix (e.frame.rotate Q) = Q.val := by
    change e.frame.matrix⁻¹ * (e.frame.matrix * Q.val) = Q.val
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr e.frame.det_ne_zero), Matrix.one_mul]
  exact (twoFormFrameValue_change o u e.frame (e.frame.rotate Q)).trans (by rw [hQ])

theorem twoForm_operator_rotate (u : M → TwoFormFour) (e : FrameBundle g)
    (Q : OrthogonalFour) (v : FourSpace) :
    Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) Q.val
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (twoFormMatrix (twoFormFrameValue o u (e.rotate Q))) v) =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (twoFormMatrix (twoFormFrameValue o u e))
          (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) Q.val v) := by
  have hmat : Q.val * twoFormMatrix (twoFormFrameValue o u (e.rotate Q)) =
      twoFormMatrix (twoFormFrameValue o u e) * Q.val := by
    rw [twoFormFrameValue_rotate, twoFormMatrix_frameAction]
    calc
      _ = (Q.val * Q.valᵀ) * twoFormMatrix (twoFormFrameValue o u e) * Q.val := by
        noncomm_ring
      _ = _ := by rw [mul_eq_one_comm.mp Q.property, Matrix.one_mul]
  change ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) Q.val) *
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (twoFormMatrix (twoFormFrameValue o u (e.rotate Q))))) v =
    ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      (twoFormMatrix (twoFormFrameValue o u e))) *
        (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) Q.val)) v
  rw [← map_mul, ← map_mul, hmat]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A unit self-dual form admits a positively oriented standard frame,
constructed with the existing quaternion lifts. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix TraceHessian QuaternionFrame
open scoped BigOperators
noncomputable section

def standardSelfDualForm : TwoFormFour := WithLp.toLp 2 ![1,0,0,0,0,1]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The real orthonormal coordinates adapted to a parallel self-dual form
are the usual two complex coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators
noncomputable section

theorem complexCoordinates_standard_complex (x : FourSpace) :
    complexCoordinates (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      (twoFormMatrix standardSelfDualForm) x) = (-Complex.I) • complexCoordinates x := by
  change complexCoordinatesLinear (WithLp.toLp 2
    ((twoFormMatrix standardSelfDualForm) *ᵥ (x : Fin 4 → ℝ))) = _
  ext i
  fin_cases i <;> apply Complex.ext <;>
    simp [complexCoordinates, complexCoordinatesLinear,
      dotProduct, standardSelfDualForm, twoFormMatrix, Fin.sum_univ_succ]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Real complex circles are exactly multiplication by unit complex scalars. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
noncomputable section

theorem complexCoordinates_circle_standard (q : FourSpace) (t : ℝ) :
    complexCoordinates (complexCircleVector (twoFormMatrix standardSelfDualForm) q t) =
      complexPhase (-t) • complexCoordinates q := by
  rw [complexCircleVector, map_add, map_smul, map_smul, complexCoordinates_standard_complex]
  ext i
  apply Complex.ext <;> simp [complexPhase, Complex.mul_re, Complex.mul_im] <;>
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re]

theorem complexCircle_standard_of_phase (p q : FourSpace) (a : ℂ) (ha : ‖a‖ = 1)
    (hpq : complexCoordinates p = a • complexCoordinates q) :
    p = complexCircleVector (twoFormMatrix standardSelfDualForm) q (-a.arg) := by
  apply complexCoordinates.injective
  rw [complexCoordinates_circle_standard, neg_neg, complexPhase_arg a ha]
  exact hpq

end
end PositiveEinsteinFour.Geometry
end


section

/-! The quaternionic direction frame preserves the standard
complex structure, so it can be used without changing the parallel form. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Angular
open scoped Manifold ContDiff
noncomputable section

theorem directionFrameMatrix_standard_complex (q : Directions) :
    directionFrameMatrix q * twoFormMatrix standardSelfDualForm =
      twoFormMatrix standardSelfDualForm * directionFrameMatrix q := by
  ext i j
  simp only [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [directionFrameMatrix,standardSelfDualForm,twoFormMatrix,Fin.sum_univ_succ]

theorem twoFormFrameAction_direction_standard (q : Directions) :
    twoFormFrameAction (directionFrameMatrix q) standardSelfDualForm = standardSelfDualForm := by
  apply twoFormMatrix_injective
  rw [twoFormMatrix_frameAction,Matrix.mul_assoc,← directionFrameMatrix_standard_complex,
    ← Matrix.mul_assoc,directionFrameMatrix_orthogonal,Matrix.one_mul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormFrameValue_direction_standard (w : M → TwoFormFour) (e : FrameBundle g)
    (hstd : twoFormFrameValue o w e = standardSelfDualForm) (q : Directions) :
    twoFormFrameValue o w (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) =
      standardSelfDualForm := by
  rw [twoFormFrameValue_rotate,hstd]
  exact twoFormFrameAction_direction_standard q

end
end PositiveEinsteinFour.Geometry
end


section

/-! The explicit projective polar points at the Ricci-three scale. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
open scoped BigOperators
noncomputable section

theorem complexPolarLift_inner (t s : ℝ) (q p : Directions) :
    inner ℂ (complexPolarLift t q) (complexPolarLift s p) =
      ((Real.cos (t / Real.sqrt 2) * Real.cos (s / Real.sqrt 2) : ℝ) : ℂ) +
        ((Real.sin (t / Real.sqrt 2) * Real.sin (s / Real.sqrt 2) : ℝ) : ℂ) *
          inner ℂ (complexCoordinates q.val) (complexCoordinates p.val) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]
  change (Real.cos (s / Real.sqrt 2) : ℂ) * star (Real.cos (t / Real.sqrt 2) : ℂ) +
    ((Real.sin (s / Real.sqrt 2) : ℂ) * complexCoordinates p.val 0) *
      star ((Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 0) +
    ((Real.sin (s / Real.sqrt 2) : ℂ) * complexCoordinates p.val 1) *
      star ((Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 1) = _
  simp only [Pi.star_apply]
  simp only [map_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

theorem fubiniStudyDistance_complexPolar (t s : ℝ) (q p : Directions) :
    fubiniStudyDistance (complexProjectivePolar t q) (complexProjectivePolar s p) =
      Real.arccos ‖((Real.cos (t / Real.sqrt 2) * Real.cos (s / Real.sqrt 2) : ℝ) : ℂ) +
        ((Real.sin (t / Real.sqrt 2) * Real.sin (s / Real.sqrt 2) : ℝ) : ℂ) *
          inner ℂ (complexCoordinates q.val) (complexCoordinates p.val)‖ := by
  rw [complexProjectivePolar, complexProjectivePolar, fubiniStudyDistance_mk,
    complexPolarLift_norm, complexPolarLift_norm, one_mul, div_one, complexPolarLift_inner]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The projective quotient preserves the polar radius and is injective
at every strictly positive radius before the boundary. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section

theorem complexProjectivePolar_radius_eq {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) complexJacobiRadius)
    (hs : s ∈ Icc (0 : ℝ) complexJacobiRadius) (q p : Directions)
    (heq : complexProjectivePolar t q = complexProjectivePolar s p) : t = s := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp heq
  have hn : ‖a‖ = 1 := by
    have h := congrArg norm ha
    simpa only [norm_smul, complexPolarLift_norm, mul_one] using h
  have h0 := congrArg (fun z : CP2Vector => z 0) ha
  have hc : Real.cos (s / Real.sqrt 2) = Real.cos (t / Real.sqrt 2) := by
    have h := congrArg norm h0
    change ‖a * (Real.cos (s / Real.sqrt 2) : ℂ)‖ =
      ‖(Real.cos (t / Real.sqrt 2) : ℂ)‖ at h
    rw [norm_mul, hn, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [(complexPolar_angle_mem hs).1, Real.pi_pos], (complexPolar_angle_mem hs).2⟩),
      abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [(complexPolar_angle_mem ht).1, Real.pi_pos], (complexPolar_angle_mem ht).2⟩)] at h
    exact h
  have ht' := complexPolar_angle_mem ht
  have hs' := complexPolar_angle_mem hs
  have h := congrArg Real.arccos hc
  rw [Real.arccos_cos hs'.1 (by linarith [hs'.2,Real.pi_pos]),
    Real.arccos_cos ht'.1 (by linarith [ht'.2,Real.pi_pos])] at h
  exact (div_left_inj' (by positivity : Real.sqrt 2 ≠ 0)).mp h.symm

theorem complexProjectivePolar_interior_injective {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) complexJacobiRadius) (q p : Directions)
    (heq : complexProjectivePolar t q = complexProjectivePolar t p) : q = p := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp heq
  have hangle := complexPolar_angle_mem ⟨ht.1.le,ht.2.le⟩
  have hlt : t / Real.sqrt 2 < Real.pi / 2 := by
    have h := div_lt_div_of_pos_right ht.2 (by positivity : 0 < Real.sqrt 2)
    unfold complexJacobiRadius at h
    rwa [div_div, ← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hc : (Real.cos (t / Real.sqrt 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hangle.1,Real.pi_pos], hlt⟩).ne'
  have h0 := congrArg (fun z : CP2Vector => z 0) ha
  change a * (Real.cos (t / Real.sqrt 2) : ℂ) =
    (Real.cos (t / Real.sqrt 2) : ℂ) at h0
  have ha1 : a = 1 := (mul_eq_right₀ hc).mp h0
  have hs : (Real.sin (t / Real.sqrt 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi
      (div_pos ht.1 (by positivity)) (by linarith [hlt,Real.pi_pos])).ne'
  rw [ha1,one_smul] at ha
  apply Subtype.ext
  apply complexCoordinates.injective
  ext i
  fin_cases i
  · have h := congrArg (fun z : CP2Vector => z 1) ha
    exact (mul_left_cancel₀ hs h).symm
  · have h := congrArg (fun z : CP2Vector => z 2) ha
    exact (mul_left_cancel₀ hs h).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The ordinary affine chart of CP2 and its exact polar coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section

theorem complexProjectivePolar_affine (t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) complexJacobiRadius) (q : Directions) :
    complexProjectivePolar t q =
      complexAffinePoint ((Real.tan (t / Real.sqrt 2)) • complexCoordinates q.val) := by
  have hangle := complexPolar_angle_mem ⟨ht.1,ht.2.le⟩
  have hlt : t / Real.sqrt 2 < Real.pi / 2 := by
    have h := div_lt_div_of_pos_right ht.2 (by positivity : 0 < Real.sqrt 2)
    unfold complexJacobiRadius at h
    rwa [div_div,← pow_two,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hc : Real.cos (t / Real.sqrt 2) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hangle.1,Real.pi_pos],hlt⟩).ne'
  have hcs : (Real.cos (t / Real.sqrt 2) : ℂ) * (Real.tan (t / Real.sqrt 2) : ℂ) =
      (Real.sin (t / Real.sqrt 2) : ℂ) := by
    rw [← Complex.ofReal_mul,Real.tan_eq_sin_div_cos]
    congr 1
    field_simp
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(Real.cos (t / Real.sqrt 2) : ℂ),?_⟩
  ext i
  fin_cases i
  · change (Real.cos (t / Real.sqrt 2) : ℂ) * 1 = _
    exact mul_one _
  · change (Real.cos (t / Real.sqrt 2) : ℂ) *
      ((Real.tan (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 0) = _
    rw [← mul_assoc,hcs]
    rfl
  · change (Real.cos (t / Real.sqrt 2) : ℂ) *
      ((Real.tan (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 1) = _
    rw [← mul_assoc,hcs]
    rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full bilinear exponential metric in standard complex coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped BigOperators Manifold ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem complex_diagonal_pairing (a b : ℝ) (u v : FourSpace) :
    WithLp.ofLp u ⬝ᵥ (Matrix.diagonal ![1,b^2,a^2,a^2] *ᵥ WithLp.ofLp v) =
      a^2 * inner ℝ u v + (1-a^2)*u 0*v 0 + (b^2-a^2)*u 1*v 1 := by
  simp [dotProduct,Matrix.mulVec_diagonal,Fin.sum_univ_four,PiLp.inner_apply,RCLike.inner_apply]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact boundary equivalence relation of the projective polar ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
noncomputable section

theorem complexPolarLift_radius (q : Directions) :
    complexPolarLift complexJacobiRadius q =
      WithLp.toLp 2 ![0,complexCoordinates q.val 0,complexCoordinates q.val 1] := by
  simp [complexPolarLift,complexPolar_radius_angle]

theorem complexProjectivePolar_boundary_phase (q p : Directions)
    (heq : complexProjectivePolar complexJacobiRadius q =
      complexProjectivePolar complexJacobiRadius p) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ complexCoordinates p.val = a • complexCoordinates q.val := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp heq.symm
  refine ⟨a,?_,?_⟩
  · have h := congrArg norm ha
    simpa only [norm_smul,complexPolarLift_norm,mul_one] using h
  · apply Eq.symm
    ext i
    fin_cases i
    · have h := congrArg (fun z : CP2Vector => z 1) ha
      simp only [complexPolarLift_radius] at h
      exact h
    · have h := congrArg (fun z : CP2Vector => z 2) ha
      simp only [complexPolarLift_radius] at h
      exact h

theorem complexProjectivePolar_boundary_circle (q p : Directions)
    (heq : complexProjectivePolar complexJacobiRadius q =
      complexProjectivePolar complexJacobiRadius p) :
    ∃ t : ℝ, p.val = complexCircleVector (twoFormMatrix standardSelfDualForm) q.val t := by
  obtain ⟨a,ha,hpq⟩ := complexProjectivePolar_boundary_phase q p heq
  exact ⟨-a.arg,complexCircle_standard_of_phase p.val q.val a ha hpq⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every point of CP2 occurs in the explicit closed polar ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped BigOperators
noncomputable section

theorem exists_radial_direction (v : FourSpace) :
    ∃ q : Directions, ‖v‖ • q.val = v := by
  by_cases hv : v = 0
  · exact ⟨firstDirection, by simp [hv]⟩
  refine ⟨⟨‖v‖⁻¹ • v, ?_⟩, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  · exact (smul_smul _ _ _).trans (by
      rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul])

theorem complexProjectivePolar_surjective (p : ComplexProjective2) :
    ∃ t ∈ Icc (0 : ℝ) complexJacobiRadius, ∃ q : Directions,
      complexProjectivePolar t q = p := by
  obtain ⟨z,hz,hn,hp,him,hre⟩ := cp2_exists_first_aligned p
  let a := (z 0).re
  let u : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![z 1,z 2]
  let v := complexCoordinates.symm u
  have hhead : z 0 = (a : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him
  have hvn : ‖v‖ = ‖u‖ := complexCoordinates.symm.norm_map u
  have hsquare : a ^ 2 + ‖v‖ ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) hn
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, hhead] at h
    rw [hvn, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simpa only [u, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, one_pow, add_assoc] using h
  have ha0 : 0 ≤ a := hre
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg ‖v‖]
  let θ := Real.arccos a
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg a
  have hθ1 : θ ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr ha0
  have hcos : Real.cos θ = a := Real.cos_arccos (by linarith) ha1
  have hsin : Real.sin θ = ‖v‖ := by
    rw [Real.sin_arccos]
    rw [show 1 - a ^ 2 = ‖v‖ ^ 2 by linarith]
    exact Real.sqrt_sq (norm_nonneg _)
  obtain ⟨q,hq⟩ := exists_radial_direction v
  have hu : ‖v‖ • complexCoordinates q.val = u := by
    have h := congrArg complexCoordinates hq
    simpa only [map_smul, v, LinearIsometryEquiv.apply_symm_apply] using h
  let t := Real.sqrt 2 * θ
  have hdivide : t / Real.sqrt 2 = θ := by
    dsimp only [t]
    exact mul_div_cancel_left₀ θ (by positivity)
  have hscale : Real.sqrt 2 * (Real.pi / 2) = complexJacobiRadius := by
    unfold complexJacobiRadius
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have ht : t ∈ Icc (0 : ℝ) complexJacobiRadius :=
    ⟨mul_nonneg (Real.sqrt_nonneg _) hθ0,
      (mul_le_mul_of_nonneg_left hθ1 (Real.sqrt_nonneg _)).trans_eq hscale⟩
  have hlift : complexPolarLift t q = z := by
    ext i
    fin_cases i
    · change (Real.cos (t / Real.sqrt 2) : ℂ) = z 0
      rw [hdivide,hcos,hhead]
    · have h := congrArg (fun x : EuclideanSpace ℂ (Fin 2) => x 0) hu
      change (Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 0 = z 1
      rw [hdivide,hsin]
      exact h
    · have h := congrArg (fun x : EuclideanSpace ℂ (Fin 2) => x 1) hu
      change (Real.sin (t / Real.sqrt 2) : ℂ) * complexCoordinates q.val 1 = z 2
      rw [hdivide,hsin]
      exact h
  refine ⟨t,ht,q,?_⟩
  simpa only [complexProjectivePolar, hlift] using hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact logarithm of the standard projective affine chart, in the
Ricci-three normal coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section

def complexAffineLog (z : EuclideanSpace ℂ (Fin 2)) : FourSpace :=
  (complexAffineRadius z / ‖z‖) • complexCoordinates.symm z

theorem complexAffineLog_norm (z : EuclideanSpace ℂ (Fin 2)) :
    ‖complexAffineLog z‖ = complexAffineRadius z := by
  by_cases hz : z = 0
  · simp [hz,complexAffineLog,complexAffineRadius]
  rw [complexAffineLog,norm_smul,complexCoordinates.symm.norm_map,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (complexAffineRadius_mem z).1 (norm_nonneg _)),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]

theorem complexAffinePoint_polar_log (z : EuclideanSpace ℂ (Fin 2)) :
    ∃ q : Directions,
      complexProjectivePolar (complexAffineRadius z) q = complexAffinePoint z ∧
      complexAffineRadius z • q.val = complexAffineLog z := by
  have ht := complexAffineRadius_mem z
  by_cases hz : z = 0
  · refine ⟨firstDirection,?_,?_⟩
    · simpa [hz,complexAffineRadius] using complexProjectivePolar_affine 0
        ⟨le_rfl,complexJacobiRadius_pos⟩ firstDirection
    · simp [hz,complexAffineRadius,complexAffineLog]
  let q : Directions := ⟨‖z‖⁻¹ • complexCoordinates.symm z,by
    rw [norm_smul,complexCoordinates.symm.norm_map,Real.norm_eq_abs,abs_inv,
      abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  have hq : complexCoordinates q.val = ‖z‖⁻¹ • z := by
    change complexCoordinates (‖z‖⁻¹ • complexCoordinates.symm z) = _
    rw [map_smul,LinearIsometryEquiv.apply_symm_apply]
  have hd : complexAffineRadius z / Real.sqrt 2 = Real.arctan ‖z‖ := by
    exact mul_div_cancel_left₀ _ (by positivity)
  refine ⟨q,?_,?_⟩
  · rw [complexProjectivePolar_affine _ ht,hq,hd,Real.tan_arctan,smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),one_smul]
  · change complexAffineRadius z • (‖z‖⁻¹ • complexCoordinates.symm z) = _
    rw [smul_smul,complexAffineLog,div_eq_mul_inv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Arbitrary-direction form of the actual complex radial metric. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped BigOperators Manifold ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

def complexCompanion (q : Directions) : FourSpace :=
  WithLp.toLp 2 ![-q.val 1,q.val 0,-q.val 3,q.val 2]

theorem complexCoordinates_companion (q : Directions) :
    complexCoordinates (complexCompanion q) = Complex.I • complexCoordinates q.val := by
  ext i
  fin_cases i <;> apply Complex.ext <;>
    simp [complexCompanion,complexCoordinates,complexCoordinatesLinear]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact distance to the north pole in the projective polar coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section

def complexProjectiveNorth : ComplexProjective2 := complexProjectivePolar 0 firstDirection

theorem complexProjectivePolar_zero (q : Directions) :
    complexProjectivePolar 0 q = complexProjectiveNorth := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨1,by simp [complexPolarLift]⟩

theorem fubiniStudyDistance_north_polar (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) complexJacobiRadius) (q : Directions) :
    fubiniStudyDistance complexProjectiveNorth (complexProjectivePolar t q) = t / Real.sqrt 2 := by
  rw [complexProjectiveNorth,fubiniStudyDistance_complexPolar]
  simp only [zero_div,Real.cos_zero,Real.sin_zero,one_mul,zero_mul,Complex.ofReal_zero,
    add_zero,Complex.norm_real,Real.norm_eq_abs]
  have ha := complexPolar_angle_mem ht
  rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [ha.1,Real.pi_pos],ha.2⟩),
    Real.arccos_cos ha.1 (by linarith [ha.2,Real.pi_pos])]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Hausdorff topology determined by the actual projective overlaps. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section

attribute [local instance] complexProjectiveTopology

theorem complexPolarLift_continuous :
    Continuous (fun x : ℝ × Directions => complexPolarLift x.1 x.2) := by
  have hC : Continuous (fun x : ℝ × Directions => complexCoordinates x.2.val) :=
    complexCoordinates.continuous.comp (continuous_subtype_val.comp continuous_snd)
  have hf : Continuous (fun x : ℝ × Directions =>
      (![(Real.cos (x.1 / Real.sqrt 2) : ℂ),
        (Real.sin (x.1 / Real.sqrt 2) : ℂ) * complexCoordinates x.2.val 0,
        (Real.sin (x.1 / Real.sqrt 2) : ℂ) * complexCoordinates x.2.val 1] : Fin 3 → ℂ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm.continuous.comp hf

theorem complexProjectivePolar_continuous :
    Continuous (fun x : ℝ × Directions => complexProjectivePolar x.1 x.2) := by
  apply complexProjectiveEvaluation_isEmbedding.continuous_iff.mpr
  apply continuous_pi
  intro p
  change Continuous (fun x : ℝ × Directions => cp2Overlap p (complexProjectivePolar x.1 x.2))
  have heq (x : ℝ × Directions) : cp2Overlap p (complexProjectivePolar x.1 x.2) =
      ‖inner ℂ (cp2UnitRep p) (complexPolarLift x.1 x.2)‖ :=
    cp2Overlap_of_unit_representatives _ _ _ _ (cp2UnitRep_ne_zero p)
      (complexPolarLift_ne_zero x.1 x.2) (cp2UnitRep_norm p)
      (complexPolarLift_norm x.1 x.2) (cp2UnitRep_mk p) rfl
  simp_rw [heq]
  exact (continuous_const.inner complexPolarLift_continuous).norm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential factors through the projective polar quotient.
The resulting map is surjective. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section

def complexProjectivePolarData (p : ComplexProjective2) : ComplexProjectivePolarData p := by
  exact Classical.choice (by
    obtain ⟨t,ht,q,hq⟩ := complexProjectivePolar_surjective p
    exact ⟨⟨t,ht,q,hq⟩⟩)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def actualComplexProjectiveMap (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (p : ComplexProjective2) : M :=
  let D := complexProjectivePolarData p
  frameExponential g o e (D.time • D.direction.val)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial and complex-radial real components are the real and
imaginary parts of the Hermitian inner product. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem complexCoordinates_inner_re (u v : FourSpace) :
    (inner ℂ (complexCoordinates u) (complexCoordinates v)).re = inner ℝ u v := by
  change RCLike.re (inner ℂ (complexCoordinates u) (complexCoordinates v)) = inner ℝ u v
  rw [← real_inner_eq_re_inner ℂ]
  exact complexCoordinates.inner_map_map u v

theorem complexCoordinates_inner_im (q : Angular.Directions) (v : FourSpace) :
    (inner ℂ (complexCoordinates q.val) (complexCoordinates v)).im =
      inner ℝ (complexCompanion q) v := by
  have h := complexCoordinates_inner_re (complexCompanion q) v
  rw [complexCoordinates_companion,inner_smul_left] at h
  simpa using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact polar parametrization is a genuine quotient onto CP2. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space

def complexPolarProjection (p : ComplexPolarDomain) : ComplexProjective2 :=
  complexProjectivePolar p.1.val p.2

theorem complexPolarProjection_surjective : Function.Surjective complexPolarProjection := by
  intro p
  obtain ⟨t,ht,q,hq⟩ := complexProjectivePolar_surjective p
  exact ⟨(⟨t,ht⟩,q),hq⟩

theorem complexPolarProjection_continuous : Continuous complexPolarProjection := by
  have ht : Continuous (fun p : ComplexPolarDomain => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hq : Continuous (fun p : ComplexPolarDomain => p.2) := continuous_snd
  have hpair : Continuous (fun p : ComplexPolarDomain => (p.1.val,p.2)) := ht.prodMk hq
  change Continuous ((fun x : ℝ × Directions => complexProjectivePolar x.1 x.2) ∘
    (fun p : ComplexPolarDomain => (p.1.val,p.2)))
  exact Continuous.comp complexProjectivePolar_continuous hpair

theorem complexPolarProjection_isQuotientMap : Topology.IsQuotientMap complexPolarProjection := by
  exact Topology.IsQuotientMap.of_surjective_continuous
    complexPolarProjection_surjective complexPolarProjection_continuous

end
end PositiveEinsteinFour.Geometry
end


section

/-! The explicit homogeneous differential of the projective polar map. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular
noncomputable section

theorem complexCoordinates_linear_norm_sq (q : Directions) (v : FourSpace) (a b : ℝ) :
    ‖a • complexCoordinates q.val + b • complexCoordinates v‖ ^ 2 =
      a^2 + 2*a*b*inner ℝ q.val v + b^2*‖v‖^2 := by
  rw [norm_add_sq_real,norm_smul,norm_smul,real_inner_smul_left,real_inner_smul_right,
    complexCoordinates.inner_map_map,complexCoordinates.norm_map,complexCoordinates.norm_map,q.property]
  simp only [Real.norm_eq_abs,mul_pow,sq_abs,mul_one]
  ring

def complexPolarLiftDifferential (t : ℝ) (q : Directions) (v : FourSpace) : CP2Vector :=
  let x := inner ℝ q.val v
  let a := (Real.cos (t / Real.sqrt 2) / Real.sqrt 2 - Real.sin (t / Real.sqrt 2) / t) * x
  let b := Real.sin (t / Real.sqrt 2) / t
  complexHeadTail ((-Real.sin (t / Real.sqrt 2) / Real.sqrt 2 * x : ℝ) : ℂ)
    (a • complexCoordinates q.val + b • complexCoordinates v)

theorem complexPolarLiftDifferential_norm_sq (t : ℝ) (q : Directions) (v : FourSpace) :
    ‖complexPolarLiftDifferential t q v‖ ^ 2 =
      (-Real.sin (t / Real.sqrt 2) / Real.sqrt 2 * inner ℝ q.val v)^2 +
      ((Real.cos (t / Real.sqrt 2) / Real.sqrt 2 - Real.sin (t / Real.sqrt 2) / t) * inner ℝ q.val v)^2 +
      2*((Real.cos (t / Real.sqrt 2) / Real.sqrt 2 - Real.sin (t / Real.sqrt 2) / t) * inner ℝ q.val v)*
        (Real.sin (t / Real.sqrt 2) / t)*inner ℝ q.val v +
      (Real.sin (t / Real.sqrt 2) / t)^2*‖v‖^2 := by
  rw [complexPolarLiftDifferential,complexHeadTail_norm_sq,complexCoordinates_linear_norm_sq,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The phase component of the homogeneous polar differential. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular
noncomputable section

theorem complexPolarLift_headTail (t : ℝ) (q : Directions) :
    complexPolarLift t q = complexHeadTail (Real.cos (t / Real.sqrt 2))
      (Real.sin (t / Real.sqrt 2) • complexCoordinates q.val) := by
  ext i
  fin_cases i <;> rfl

theorem complexPolarLiftDifferential_inner (t : ℝ) (q : Directions) (v : FourSpace) :
    inner ℂ (complexPolarLift t q) (complexPolarLiftDifferential t q v) =
      ((Real.sin (t / Real.sqrt 2)^2 / t * inner ℝ (complexCompanion q) v : ℝ) : ℂ) * Complex.I := by
  rw [complexPolarLift_headTail,complexPolarLiftDifferential,complexHeadTail_inner,
    inner_smul_left_eq_smul,inner_add_right,inner_smul_right_eq_smul,inner_smul_right_eq_smul,
    inner_self_eq_norm_sq_to_K,complexCoordinates.norm_map,q.property]
  apply Complex.ext <;>
    simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.smul_re,Complex.smul_im,smul_eq_mul,Complex.ofReal_re,Complex.ofReal_im,
      Complex.star_def,Complex.conj_ofReal,Complex.I_re,Complex.I_im,
      complexCoordinates_inner_re,complexCoordinates_inner_im] <;> norm_num <;> ring

theorem complexPolarLiftDifferential_inner_norm_sq (t : ℝ) (q : Directions) (v : FourSpace) :
    ‖inner ℂ (complexPolarLift t q) (complexPolarLiftDifferential t q v)‖^2 =
      (Real.sin (t / Real.sqrt 2)^2 / t)^2 * (inner ℝ (complexCompanion q) v)^2 := by
  rw [complexPolarLiftDifferential_inner,norm_mul,Complex.norm_I,mul_one,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The homogeneous lift of the actual normal-coordinate projective map. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular
noncomputable section

def complexNormalLift (v : FourSpace) : CP2Vector :=
  complexHeadTail (Real.cos (‖v‖ / Real.sqrt 2))
    ((Real.sin (‖v‖ / Real.sqrt 2) / ‖v‖) • complexCoordinates v)

theorem complexNormalLift_radial (t : ℝ) (ht : 0 < t) (q : Directions) :
    complexNormalLift (t • q.val) = complexPolarLift t q := by
  have hn : ‖t • q.val‖ = t := by rw [norm_smul,q.property,Real.norm_of_nonneg ht.le,mul_one]
  rw [complexNormalLift,hn,complexPolarLift_headTail,map_smul,smul_smul,
    div_mul_cancel₀ _ ht.ne']

theorem hasDerivAt_norm_radial {c : ℝ → FourSpace} {v : FourSpace} {s t : ℝ}
    (hc : HasDerivAt c v s) (ht : 0 < t) (q : Directions) (hcs : c s = t • q.val) :
    HasDerivAt (fun r => ‖c r‖) (inner ℝ q.val v) s := by
  have hn : ‖c s‖ = t := by rw [hcs,norm_smul,q.property,Real.norm_of_nonneg ht.le,mul_one]
  have hd := hc.norm_sq.sqrt (by rw [hn]; positivity)
  have hfun : (fun r => Real.sqrt (‖c r‖ ^ 2)) = fun r => ‖c r‖ := by
    funext r
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun,Real.sqrt_sq (norm_nonneg _),hn,hcs,real_inner_smul_left] at hd
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The horizontal homogeneous metric agrees with the actual two-frequency
normal metric. The normalization is Ricci equal to three times the metric. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
noncomputable section

theorem complex_projective_differential_gram (t : ℝ) (q : Directions) (v : FourSpace) :
    2 * (‖complexPolarLiftDifferential t q v‖^2 -
      ‖inner ℂ (complexPolarLift t q) (complexPolarLiftDifferential t q v)‖^2) =
        (complexJacobiSlow t / t)^2 * ‖v‖^2 +
          (1-(complexJacobiSlow t / t)^2)*(inner ℝ q.val v)^2 +
          ((complexJacobiFast t / t)^2-(complexJacobiSlow t / t)^2)*
            (inner ℝ (complexCompanion q) v)^2 := by
  have hA : (complexJacobiSlow t / t)^2 = 2*(Real.sin (t / Real.sqrt 2)/t)^2 := by
    rw [div_pow,complexJacobiSlow_sq]
    ring
  have hB : (complexJacobiFast t / t)^2-(complexJacobiSlow t / t)^2 =
      -2*(Real.sin (t / Real.sqrt 2)^2/t)^2 := by
    rw [div_pow,div_pow,← sub_div,complexJacobiFast_sq_sub_slow_sq]
    ring
  rw [complexPolarLiftDifferential_norm_sq,complexPolarLiftDifferential_inner_norm_sq,hB,hA]
  have hroot : (Real.sqrt 2)⁻¹^2 = (1/2 : ℝ) := by
    rw [inv_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  calc
    _ = 2 * ((Real.sqrt 2)⁻¹^2 *
        (Real.sin (t / Real.sqrt 2)^2 + Real.cos (t / Real.sqrt 2)^2) * (inner ℝ q.val v)^2 -
        (Real.sin (t / Real.sqrt 2)/t)^2 * (inner ℝ q.val v)^2 +
        (Real.sin (t / Real.sqrt 2)/t)^2 * ‖v‖^2 -
        (Real.sin (t / Real.sqrt 2)^2/t)^2 * (inner ℝ (complexCompanion q) v)^2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq,hroot]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiation of the homogeneous normal lift along actual curves. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular
noncomputable section

theorem complexNormalLift_hasDerivAt {c : ℝ → FourSpace} {v : FourSpace} {s t : ℝ}
    (hc : HasDerivAt c v s) (ht : 0 < t) (q : Directions) (hcs : c s = t • q.val) :
    HasDerivAt (fun r => complexNormalLift (c r)) (complexPolarLiftDifferential t q v) s := by
  have hn := hasDerivAt_norm_radial hc ht q hcs
  have hnval : ‖c s‖ = t := by
    rw [hcs,norm_smul,q.property,Real.norm_of_nonneg ht.le,mul_one]
  have hroot : Real.sqrt 2 ≠ 0 := by positivity
  have htheta := hn.div_const (Real.sqrt 2)
  have hcoef : HasDerivAt (fun r => Real.sin (‖c r‖ / Real.sqrt 2) / ‖c r‖)
      (((Real.cos (t / Real.sqrt 2) / Real.sqrt 2 - Real.sin (t / Real.sqrt 2) / t) / t) *
        inner ℝ q.val v) s := by
    have hd := htheta.sin.div hn (by rw [hnval]; exact ht.ne')
    rw [hnval] at hd
    convert hd using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  have hcoordinates : HasDerivAt (fun r => complexCoordinates (c r)) (complexCoordinates v) s :=
    complexCoordinates.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s hc
  have htail := hcoef.smul hcoordinates
  have htail' : HasDerivAt
      (fun r => (Real.sin (‖c r‖ / Real.sqrt 2) / ‖c r‖) • complexCoordinates (c r))
      (((Real.cos (t / Real.sqrt 2) / Real.sqrt 2 - Real.sin (t / Real.sqrt 2) / t) *
          inner ℝ q.val v) • complexCoordinates q.val +
        (Real.sin (t / Real.sqrt 2) / t) • complexCoordinates v) s := by
    convert htail using 1
    all_goals try with_reducible_and_instances rfl
    rw [hnval,hcs,map_smul,smul_smul,add_comm]
    congr 1
    field_simp
  have hhead := htheta.cos.ofReal_comp
  have hhead' : HasDerivAt (fun r => (Real.cos (‖c r‖ / Real.sqrt 2) : ℂ))
      ((-Real.sin (t / Real.sqrt 2) / Real.sqrt 2 * inner ℝ q.val v : ℝ) : ℂ) s := by
    convert hhead using 1
    all_goals try with_reducible_and_instances rfl
    rw [hnval]
    congr 1
    ring
  exact complexHeadTail_hasDerivAt hhead' htail'

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal homogeneous lift represents the actual projective quotient map. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
open scoped Manifold ContDiff
noncomputable section

theorem complexNormalLift_norm (v : FourSpace) : ‖complexNormalLift v‖ = 1 := by
  by_cases hv : v = 0
  · subst v
    simp [complexNormalLift,complexHeadTail,EuclideanSpace.norm_eq,Fin.sum_univ_three]
  · let q : Directions := ⟨‖v‖⁻¹ • v, by
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
    have hrad : ‖v‖ • q.val = v := by
      change ‖v‖ • (‖v‖⁻¹ • v) = v
      rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul]
    rw [← hrad,complexNormalLift_radial ‖v‖ (norm_pos_iff.mpr hv),complexPolarLift_norm]

theorem complexNormalLift_ne_zero (v : FourSpace) : complexNormalLift v ≠ 0 := by
  intro h
  have hn := complexNormalLift_norm v
  rw [h,norm_zero] at hn
  exact zero_ne_one hn

def complexNormalPoint (v : FourSpace) : ComplexProjective2 :=
  Projectivization.mk ℂ (complexNormalLift v) (complexNormalLift_ne_zero v)

theorem complexNormalPoint_radial (t : ℝ) (ht : 0 < t) (q : Directions) :
    complexNormalPoint (t • q.val) = complexProjectivePolar t q := by
  simp only [complexNormalPoint,complexProjectivePolar,complexNormalLift_radial t ht q]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The ordinary affine logarithm is differentiable away from its center. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
noncomputable section

theorem complexAffineLog_ne_zero {z : EuclideanSpace ℂ (Fin 2)} (hz : z ≠ 0) :
    complexAffineLog z ≠ 0 := by
  apply norm_pos_iff.mp
  rw [complexAffineLog_norm]
  exact complexAffineRadius_pos hz

theorem complexAffineLog_differentiableAt {z : EuclideanSpace ℂ (Fin 2)} (hz : z ≠ 0) :
    DifferentiableAt ℝ complexAffineLog z := by
  have hn : DifferentiableAt ℝ (fun z : EuclideanSpace ℂ (Fin 2) => ‖z‖) z :=
    (differentiableAt_id : DifferentiableAt ℝ (fun w : EuclideanSpace ℂ (Fin 2) => w) z).norm ℝ hz
  have hr : DifferentiableAt ℝ complexAffineRadius z := hn.arctan.const_mul (Real.sqrt 2)
  have hq : DifferentiableAt ℝ (fun w => complexAffineRadius w / ‖w‖) z :=
    by simpa only [Pi.mul_apply,Pi.inv_apply,div_eq_mul_inv] using!
      hr.mul (hn.inv (norm_ne_zero_iff.mpr hz))
  have hlin : DifferentiableAt ℝ (fun w => complexCoordinates.symm w) z :=
    complexCoordinates.symm.toContinuousLinearEquiv.differentiableAt
  exact hq.smul hlin

theorem complexNormalPoint_affineLog {z : EuclideanSpace ℂ (Fin 2)} (hz : z ≠ 0) :
    complexNormalPoint (complexAffineLog z) = complexAffinePoint z := by
  obtain ⟨q,hq,hlog⟩ := complexAffinePoint_polar_log z
  rw [← hlog,complexNormalPoint_radial _ (complexAffineRadius_pos hz),hq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! C1 regularity of the affine logarithm used for projective paths. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
noncomputable section

theorem complexAffineLog_contDiffAt {z : EuclideanSpace ℂ (Fin 2)} (hz : z ≠ 0) :
    ContDiffAt ℝ 1 complexAffineLog z := by
  have hn : ContDiffAt ℝ 1 (fun w : EuclideanSpace ℂ (Fin 2) => ‖w‖) z :=
    contDiffAt_norm ℝ hz
  have hr : ContDiffAt ℝ 1 complexAffineRadius z := contDiffAt_const.mul hn.arctan
  have hq : ContDiffAt ℝ 1 (fun w => complexAffineRadius w / ‖w‖) z := by
    simpa only [Pi.mul_apply,Pi.inv_apply,div_eq_mul_inv] using!
      hr.mul (hn.inv (norm_ne_zero_iff.mpr hz))
  have hl : ContDiffAt ℝ 1 (fun w => complexCoordinates.symm w) z :=
    complexCoordinates.symm.toContinuousLinearEquiv.contDiff.contDiffAt
  exact hq.smul hl

end
end PositiveEinsteinFour.Geometry
end


section

/-! A section of the actual projective map and its unique local values before the cut radius. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def actualComplexProjectiveSection (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (h : Function.Surjective (actualComplexProjectiveMap g o e)) :
    M → ComplexProjective2 := Function.surjInv h

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M] in
theorem actualComplexProjectiveSection_rightInverse
    (e : FrameBundle g) (h : Function.Surjective (actualComplexProjectiveMap g o e)) :
    Function.RightInverse (actualComplexProjectiveSection g o e h)
      (actualComplexProjectiveMap g o e) := Function.rightInverse_surjInv h

end
end PositiveEinsteinFour.Geometry
end


section

/-! A projective section is continuous wherever the actual fiber is a singleton. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space

theorem complexProjective_compactSpace : CompactSpace ComplexProjective2 := by
  apply isCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr complexPolarProjection_surjective]
  exact isCompact_range complexPolarProjection_continuous

end
end PositiveEinsteinFour.Geometry
end


section

/-! The explicit Fubini--Study distance induces the existing compact projective topology. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space

theorem complexProjective_open_iff (V : Set ComplexProjective2) :
    IsOpen V ↔ ∀ x ∈ V, ∃ ε > 0, ∀ y, fubiniStudyDistance x y < ε → y ∈ V := by
  let : CompactSpace ComplexProjective2 := complexProjective_compactSpace
  constructor
  · intro hV x hx
    by_cases hempty : Vᶜ = ∅
    · refine ⟨1,zero_lt_one,fun y _ => ?_⟩
      by_contra hy
      have hh : y ∈ (∅ : Set ComplexProjective2) := hempty ▸ hy
      exact hh
    obtain ⟨y,hy,hmin⟩ := hV.isClosed_compl.isCompact.exists_isMinOn
      (Set.nonempty_iff_ne_empty.mpr hempty) (fubiniStudyDistance_left_continuous x).continuousOn
    have hpos : 0 < fubiniStudyDistance x y := by
      apply lt_of_le_of_ne
      · rw [fubiniStudyDistance_eq_arccos]; exact Real.arccos_nonneg _
      · intro h
        exact hy ((fubiniStudyDistance_eq_zero_iff x y).mp h.symm ▸ hx)
    refine ⟨fubiniStudyDistance x y,hpos,fun z hz => ?_⟩
    by_contra hzV
    exact (not_lt_of_ge (hmin hzV)) hz
  · intro h
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨ε,hε,hsub⟩ := h x hx
    have hn : {y | fubiniStudyDistance x y < ε} ∈ 𝓝 x :=
      (isOpen_lt (fubiniStudyDistance_left_continuous x) continuous_const).mem_nhds
        (by simpa only [mem_ofPred_eq,fubiniStudyDistance_self] using hε)
    exact mem_of_superset hn hsub

@[instance_reducible] def complexProjectiveMetric : MetricSpace ComplexProjective2 :=
  MetricSpace.ofDistTopology fubiniStudyDistance fubiniStudyDistance_self
    fubiniStudyDistance_comm fubiniStudyDistance_triangle complexProjective_open_iff
    (fun P Q h => (fubiniStudyDistance_eq_zero_iff P Q).mp h)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The open polar ball is dense in the actual projective metric space. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped _root_.Topology
noncomputable section
attribute [local instance] complexProjectiveMetric

def complexProjectiveInterior : Set ComplexProjective2 :=
  {P | ∃ t ∈ Ico (0 : ℝ) complexJacobiRadius, ∃ q : Directions, complexProjectivePolar t q = P}

theorem complexProjectiveInterior_dense : Dense complexProjectiveInterior := by
  intro P
  obtain ⟨t,ht,q,rfl⟩ := complexProjectivePolar_surjective P
  by_cases ht0 : t = 0
  · subst t
    exact subset_closure ⟨0,⟨le_rfl,complexJacobiRadius_pos⟩,q,rfl⟩
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hlim : Tendsto (fun s : ℝ => complexProjectivePolar s q)
      (𝓝[<] t) (𝓝 (complexProjectivePolar t q)) :=
    (complexProjectivePolar_continuous.comp (continuous_id.prodMk continuous_const)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (eventually_gt_nhds htpos)] with s hst hs0
  exact ⟨s,⟨hs0.le,hst.trans_le ht.2⟩,q,rfl⟩

theorem exists_complexInterior_sequence (P : ComplexProjective2) :
    ∃ u : ℕ → ComplexProjective2, (∀ n, u n ∈ complexProjectiveInterior) ∧
      Tendsto u atTop (𝓝 P) :=
  mem_closure_iff_seq_limit.mp (complexProjectiveInterior_dense P)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual cut locus is covered by two Lipschitz images of closed complex disks. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section

theorem cp2Overlap_north (P : ComplexProjective2) :
    cp2Overlap complexProjectiveNorth P = ‖cp2UnitRep P 0‖ := by
  have h := cp2Overlap_of_unit_representatives complexProjectiveNorth P
    (complexPolarLift 0 firstDirection) (cp2UnitRep P)
    (complexPolarLift_ne_zero 0 firstDirection) (cp2UnitRep_ne_zero P)
    (complexPolarLift_norm 0 firstDirection) (cp2UnitRep_norm P) rfl (cp2UnitRep_mk P)
  rw [h]
  simp [complexPolarLift,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_three]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Cones over locally Lipschitz complex parametrizations have dimension at most three. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology NNReal ENNReal
noncomputable section

def complexParametrizedCone (a : FourSpace) (f : ℂ → FourSpace) (U : Set ℂ) : Set FourSpace :=
  (fun p : ℂ × ℝ => a + p.2 • (f p.1 - a)) '' (U ×ˢ univ)

theorem complexParametrizedCone_dimH_le (a : FourSpace) (f : ℂ → FourSpace) (U : Set ℂ)
    (hf : ∀ z ∈ U, ∃ K : ℝ≥0, ∃ V ∈ 𝓝 z, LipschitzOnWith K f V) :
    dimH (complexParametrizedCone a f U) ≤ 3 := by
  have houter : LocallyLipschitz (fun p : FourSpace × ℝ => a + p.2 • (p.1 - a)) :=
    (contDiff_const.add (contDiff_snd.smul (contDiff_fst.sub contDiff_const)) :
      ContDiff ℝ 1 (fun p : FourSpace × ℝ => a + p.2 • (p.1 - a))).locallyLipschitz
  have hlocal : ∀ p ∈ U ×ˢ (univ : Set ℝ), ∃ K : ℝ≥0, ∃ V ∈ 𝓝[U ×ˢ univ] p,
      LipschitzOnWith K (fun p : ℂ × ℝ => a + p.2 • (f p.1 - a)) V := by
    intro p hp
    obtain ⟨K,V,hV,hfV⟩ := hf p.1 hp.1
    let T : Set (ℂ × ℝ) := Prod.fst ⁻¹' V
    have hT : T ∈ 𝓝 p := continuous_fst.continuousAt hV
    have hpair : LipschitzOnWith (max K 1) (fun q : ℂ × ℝ => (f q.1,q.2)) T := by
      have hh : LipschitzOnWith K (fun q : ℂ × ℝ => f q.1) T := by
        simpa only [mul_one,Function.comp_def] using hfV.comp
          (LipschitzWith.prod_fst.lipschitzOnWith : LipschitzOnWith 1 Prod.fst T)
          (fun _ hq => hq)
      exact hh.prodMk LipschitzWith.prod_snd.lipschitzOnWith
    obtain ⟨L,W,hW,houterW⟩ := houter (f p.1,p.2)
    have hpre : (fun q : ℂ × ℝ => (f q.1,q.2)) ⁻¹' W ∈ 𝓝 p :=
      (hpair.continuousOn.continuousAt hT) hW
    refine ⟨L * max K 1,T ∩ (fun q : ℂ × ℝ => (f q.1,q.2)) ⁻¹' W,
      mem_nhdsWithin_of_mem_nhds (inter_mem hT hpre), ?_⟩
    intro u hu v hv
    have hd := (houterW hu.2 hv.2).trans (mul_le_mul_right (hpair hu.1 hv.1) (L : ℝ≥0∞))
    simpa only [ENNReal.coe_mul,mul_assoc] using hd
  calc
    _ ≤ dimH (U ×ˢ (univ : Set ℝ)) := dimH_image_le_of_locally_lipschitzOn hlocal
    _ ≤ dimH (univ : Set (ℂ × ℝ)) := dimH_mono (subset_univ _)
    _ = 3 := by rw [Real.dimH_univ_eq_finrank]; norm_num [Module.finrank_prod]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Arbitrarily short polygonal detours around two complex-parametrized sets. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology NNReal ENNReal
noncomputable section

theorem exists_not_mem_of_dimH_le_three (s : Set FourSpace) (hs : dimH s ≤ 3)
    (x : FourSpace) (V : Set FourSpace) (hV : V ∈ 𝓝 x) : ∃ y ∈ V, y ∉ s := by
  by_contra! h
  have hdim : (4 : ℝ≥0∞) ≤ 3 := by
    calc
      _ = dimH V := by rw [Real.dimH_of_mem_nhds hV]; norm_num [FourSpace]
      _ ≤ dimH s := dimH_mono h
      _ ≤ 3 := hs
  norm_num at hdim

theorem segment_avoids_of_not_mem_complexCone (a b : FourSpace)
    (f : ℂ → FourSpace) (U : Set ℂ) (ha : a ∉ f '' U)
    (hb : b ∉ complexParametrizedCone a f U) :
    Disjoint (segment ℝ a b) (f '' U) := by
  rw [Set.disjoint_left]
  intro p hp hpf
  obtain ⟨z,hz,rfl⟩ := hpf
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨t,ht,heq⟩ := hp
  by_cases ht0 : t = 0
  · have hfa : f z = a := by simpa only [ht0,AffineMap.lineMap_apply_zero] using heq.symm
    exact ha ⟨z,hz,hfa⟩
  · apply hb
    refine ⟨(z,t⁻¹),⟨hz,mem_univ _⟩,?_⟩
    have hsub : f z - a = t • (b-a) := by
      rw [← heq,AffineMap.lineMap_apply]
      simp only [vsub_eq_sub,vadd_eq_add]
      abel
    change a + t⁻¹ • (f z-a) = b
    rw [hsub,smul_smul,inv_mul_cancel₀ ht0,one_smul]
    abel

theorem exists_complexParametrized_detour (f : Fin 2 → ℂ → FourSpace) (U : Fin 2 → Set ℂ)
    (hf : ∀ i z, z ∈ U i → ∃ K : ℝ≥0, ∃ V ∈ 𝓝 z, LipschitzOnWith K (f i) V)
    (a b : FourSpace) (ha : ∀ i, a ∉ f i '' U i) (hb : ∀ i, b ∉ f i '' U i)
    (V : Set FourSpace) (hV : V ∈ 𝓝 b) :
    ∃ z ∈ V, ∀ i, Disjoint (segment ℝ a z) (f i '' U i) ∧
      Disjoint (segment ℝ z b) (f i '' U i) := by
  let B := (⋃ i, complexParametrizedCone a (f i) (U i)) ∪
    (⋃ i, complexParametrizedCone b (f i) (U i))
  have hB : dimH B ≤ 3 := by
    rw [dimH_union]
    apply max_le
    · rw [dimH_iUnion]
      exact iSup_le (fun i => complexParametrizedCone_dimH_le a (f i) (U i) (hf i))
    · rw [dimH_iUnion]
      exact iSup_le (fun i => complexParametrizedCone_dimH_le b (f i) (U i) (hf i))
  obtain ⟨z,hz,hzB⟩ := exists_not_mem_of_dimH_le_three B hB b V hV
  refine ⟨z,hz,fun i => ⟨?_,?_⟩⟩
  · apply segment_avoids_of_not_mem_complexCone a z (f i) (U i) (ha i)
    exact fun h => hzB (Or.inl (mem_iUnion.mpr ⟨i,h⟩))
  · rw [segment_symm]
    apply segment_avoids_of_not_mem_complexCone b z (f i) (U i) (hb i)
    exact fun h => hzB (Or.inr (mem_iUnion.mpr ⟨i,h⟩))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual cut-locus parametrizations and their cones in any fixed linear chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

def complexCutChartMap (g : SmoothMetric M) (o : FrameOrientation g) (e : FrameBundle g)
    (c : M) (A : FourSpace →L[ℝ] FourSpace) (i : Fin 2) (z : ℂ) : FourSpace :=
  A (chartAt FourSpace c (actualComplexProjectiveMap g o e (complexCutPoint i z)))

def complexCutChartDomain (g : SmoothMetric M) (o : FrameOrientation g) (e : FrameBundle g)
    (c : M) (i : Fin 2) : Set ℂ :=
  (fun z => actualComplexProjectiveMap g o e (complexCutPoint i z)) ⁻¹'
    (chartAt FourSpace c).source

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local metric increment bounds control the length of a straight segment. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology
noncomputable section

theorem dist_le_of_segment_local_bound {Y : Type*} [PseudoMetricSpace Y]
    (f : FourSpace → Y) (a b : FourSpace) (K : ℝ)
    (hf : ContinuousOn f (segment ℝ a b))
    (hlocal : ∀ x ∈ segment ℝ a b, ∀ᶠ y in 𝓝[segment ℝ a b] x,
      dist (f x) (f y) ≤ K * dist x y) :
    dist (f a) (f b) ≤ K * dist a b := by
  let η : ℝ → FourSpace := AffineMap.lineMap a b
  have hη : Continuous η := (ContinuousAffineMap.lineMap a b).continuous
  have hmaps : MapsTo η (Icc 0 1) (segment ℝ a b) := fun t ht => lineMap_mem_segment ℝ a b ht
  have hcomp : ContinuousOn (f ∘ η) (Icc 0 1) := hf.comp hη.continuousOn hmaps
  let q : ℝ → ℝ := fun t => dist (f a) (f (η t))
  have hq : ContinuousOn q (Icc 0 1) := continuous_dist.comp_continuousOn (continuousOn_const.prodMk hcomp)
  have hinc (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ∀ᶠ s in 𝓝[>] t, q s-q t ≤ (K*dist a b)*(s-t) := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1,ht.2.le⟩
    have hηlim : Tendsto η (𝓝[>] t) (𝓝[segment ℝ a b] (η t)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hη.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_lt_nhds ht.2)] with s hs hsb
      exact hmaps ⟨ht.1.trans hs.le,hsb.le⟩
    filter_upwards [hηlim (hlocal (η t) (hmaps ht')),self_mem_nhdsWithin] with s hs hts
    have htri : q s-q t ≤ dist (f (η t)) (f (η s)) := by
      dsimp [q]
      linarith [dist_triangle (f a) (f (η t)) (f (η s))]
    calc
      _ ≤ K * dist (η t) (η s) := htri.trans hs
      _ = (K*dist a b)*(s-t) := by
        change K * dist (AffineMap.lineMap a b t) (AffineMap.lineMap a b s) = _
        rw [dist_lineMap_lineMap,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hts.le)]
        ring
  have h := sub_le_of_local_increment q 0 1 (K*dist a b) (by norm_num) hq hinc
  simpa only [q,η,AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one,dist_self,
    sub_zero,mul_one] using h

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! A local length bound extends across a finite union of complex-parametrized thin sets. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter
open scoped _root_.Topology NNReal
noncomputable section

theorem dist_le_of_complexThinSet {Y : Type*} [PseudoMetricSpace Y]
    (f : FourSpace → Y) (p : Fin 2 → ℂ → FourSpace) (U : Fin 2 → Set ℂ)
    (hp : ∀ i z, z ∈ U i → ∃ K : ℝ≥0, ∃ V ∈ 𝓝 z, LipschitzOnWith K (p i) V)
    (V : Set FourSpace) (hV : IsOpen V) (hconv : Convex ℝ V) (K : ℝ) (hK : 0 ≤ K)
    (hf : ContinuousOn f (V \ ⋃ i, p i '' U i))
    (hlocal : ∀ x ∈ V \ ⋃ i, p i '' U i,
      ∀ᶠ y in 𝓝[V \ ⋃ i, p i '' U i] x, dist (f x) (f y) ≤ K * dist x y)
    (a b : FourSpace) (ha : a ∈ V \ ⋃ i, p i '' U i) (hb : b ∈ V \ ⋃ i, p i '' U i) :
    dist (f a) (f b) ≤ K * dist a b := by
  have hseg (x y : FourSpace) (hxy : segment ℝ x y ⊆ V \ ⋃ i, p i '' U i) :
      dist (f x) (f y) ≤ K * dist x y := by
    apply dist_le_of_segment_local_bound f x y K (hf.mono hxy)
    intro z hz
    exact nhdsWithin_mono z hxy (hlocal z (hxy hz))
  have hε (ε : ℝ) (hε : 0 < ε) : dist (f a) (f b) ≤ K*(dist a b+2*ε) := by
    obtain ⟨z,hz,havoid⟩ := exists_complexParametrized_detour p U hp a b
      (fun i hi => ha.2 (mem_iUnion.mpr ⟨i,hi⟩))
      (fun i hi => hb.2 (mem_iUnion.mpr ⟨i,hi⟩))
      (V ∩ Metric.ball b ε) (inter_mem (hV.mem_nhds hb.1) (Metric.ball_mem_nhds b hε))
    have hleft : segment ℝ a z ⊆ V \ ⋃ i, p i '' U i := by
      intro w hw
      refine ⟨hconv.segment_subset ha.1 hz.1 hw,?_⟩
      intro hwB
      obtain ⟨i,hi⟩ := mem_iUnion.mp hwB
      exact Set.disjoint_left.mp (havoid i).1 hw hi
    have hright : segment ℝ z b ⊆ V \ ⋃ i, p i '' U i := by
      intro w hw
      refine ⟨hconv.segment_subset hz.1 hb.1 hw,?_⟩
      intro hwB
      obtain ⟨i,hi⟩ := mem_iUnion.mp hwB
      exact Set.disjoint_left.mp (havoid i).2 hw hi
    calc
      _ ≤ dist (f a) (f z)+dist (f z) (f b) := dist_triangle _ _ _
      _ ≤ K*dist a z+K*dist z b := add_le_add (hseg a z hleft) (hseg z b hright)
      _ = K*(dist a z+dist z b) := by ring
      _ ≤ K*(dist a b+2*ε) := by
        apply mul_le_mul_of_nonneg_left _ hK
        have hzb : dist z b < ε := hz.2
        linarith [dist_triangle a b z,dist_comm b z]
  have ht : Tendsto (fun ε : ℝ => K*(dist a b+2*ε)) (𝓝[>] 0) (𝓝 (K*dist a b)) := by
    have h : Continuous (fun ε : ℝ => K*(dist a b+2*ε)) := by fun_prop
    simpa only [mul_zero,add_zero] using h.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  exact ge_of_tendsto ht (Filter.Eventually.mono self_mem_nhdsWithin (fun ε hpos => hε ε hpos))

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


