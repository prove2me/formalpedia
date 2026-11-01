-- Prove2me | Definitions.Def_OAIQ091C021
-- name    : OAIQ091C021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:05:42.498947+00:00
-- url     : https://prove2.me/theorems/add8ec0a-f705-4b6c-b001-52b33c13db73
-- title:
--   Definitions bundle OAIQ091C021 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 329 declarations of OpenAI's Lean: 66 definitions, 6 inductive types or structures and 257 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.HeatRadialFrameFlow`, `OAI.PositiveEinsteinFour.Geometry.HeatRadialFrameFlow.recenter`, `OAI.PositiveEinsteinFour.Geometry.HeatRadialFrameFlow.restrictTime`, `OAI.PositiveEinsteinFour.Geometry.HodgeDualOneCohomology`, `OAI.PositiveEinsteinFour.Geometry.JacobiRealizationData`, `OAI.PositiveEinsteinFour.Geometry.JacobiRealizationData.toParallelJacobiData`, `OAI.PositiveEinsteinFour.Geometry.NormalEndpointJetData`, `OAI.PositiveEinsteinFour.Geometry.NormalQuadraticJetData`, `OAI.PositiveEinsteinFour.Geometry.OneFormDeRhamCohomology`, `OAI.PositiveEinsteinFour.Geometry.ParallelJacobiData`, `OAI.PositiveEinsteinFour.Geometry.PetersenPositiveRicciInput`, `OAI.PositiveEinsteinFour.Geometry.PetersenScalingInput`, `OAI.PositiveEinsteinFour.Geometry.ScalarEuclideanSobolev.toL4`, `OAI.PositiveEinsteinFour.Geometry.SmoothScalarPoincare`, `OAI.PositiveEinsteinFour.Geometry.WeylEnergyIdentities`, `OAI.PositiveEinsteinFour.Geometry.actualCutTime`, `OAI.PositiveEinsteinFour.Geometry.actualFirstConjugateTime`, `OAI.PositiveEinsteinFour.Geometry.actualMinimizingTangentDomain`, `OAI.PositiveEinsteinFour.Geometry.chartCoordinateExtension`, `OAI.PositiveEinsteinFour.Geometry.chartEnergyBoundary`, `OAI.PositiveEinsteinFour.Geometry.chartEnergyDensity`, `OAI.PositiveEinsteinFour.Geometry.chartEnergyFirstDensity`, `OAI.PositiveEinsteinFour.Geometry.chartEnergyIndexDensity`, `OAI.PositiveEinsteinFour.Geometry.chartEnergySecondDensity`, `OAI.PositiveEinsteinFour.Geometry.chartScalarLaplacian`, `OAI.PositiveEinsteinFour.Geometry.chartTransitionSecondJet`, `OAI.PositiveEinsteinFour.Geometry.chartWeight`, `OAI.PositiveEinsteinFour.Geometry.exponentialAreaMeasure`, `OAI.PositiveEinsteinFour.Geometry.fourHeatScaledCommutator`, `OAI.PositiveEinsteinFour.Geometry.frameAntipode`, `OAI.PositiveEinsteinFour.Geometry.frameDistanceSplitTimes`, `OAI.PositiveEinsteinFour.Geometry.frameMinimizingTimes`, `OAI.PositiveEinsteinFour.Geometry.geodesicChartVelocity`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyConnection`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyCurvature`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyDensity`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyFirst`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyLeading`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyMetric`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyOneFirst` and 32 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_AngularTrace`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/AngularTrace.lean), [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_GeodesicGeometry06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry06.lean), [`EinsteinFour_GeodesicGeometry12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry12.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory09.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean), [`EinsteinFour_WeylEstimates07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates07.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C038` and `OAIQ091C018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C026`, `OAIQ091C041`, `OAIQ091C045`, `OAIQ091C046`, `OAIQ091C047`, `OAIQ091C049`, `OAIQ091C050`, `OAIQ091C051`, `OAIQ091C052` and `OAIQ091C053`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C038
import Definitions.Def_OAIQ091C018

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularTrace
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.canonicalFrameMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.canonicalUnitTangentMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.chartCoordinateMeasure_sigmaFinite _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_pseudoMetrizable _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothH1TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothL2TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarAngularProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarDirectionProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite _root_.OAI.PositiveEinsteinFour.Geometry.tangentBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.unitTangentBundle_secondCountable
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.scaleBetween_vector _root_.OAI.PositiveEinsteinFour.Geometry.actualFrameFlow_apply _root_.OAI.PositiveEinsteinFour.Geometry.endpointChartFirst_zero _root_.OAI.PositiveEinsteinFour.Geometry.endpointChartPosition_zero _root_.OAI.PositiveEinsteinFour.Geometry.endpointChartSecond_zero _root_.OAI.PositiveEinsteinFour.Geometry.mem_scalarH1MeanZero _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationFrameClass_proj _root_.OAI.PositiveEinsteinFour.Geometry.rescaleMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_first _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1SubtractMean_idempotent _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_equiv _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_none _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_some _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradientL2_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradient_subtractMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal Jacobi trace follows from the classical Einstein curvature
decomposition and the two trace-free Weyl blocks. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular
open scoped Manifold ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem normalCurvature_trace (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (q : Directions)
    (hdec : frameCurvature g c e = einsteinCurvatureTensor (plusWeyl g c e)
      (minusWeyl g c e))
    (hT : (plusWeyl g c e).trace = 0) (hU : (minusWeyl g c e).trace = 0) :
    (normalCurvature g c e q).trace = 3 := by
  rw [normalCurvature_eq_of_decomposition g c e hdec q, Matrix.trace_add,
    normalDeviation_trace _ _ _ hT hU]
  norm_num [Matrix.trace_one]

theorem frameCurvatureField_add_one_trace (g : SmoothMetric M) (e : FrameBundle g)
    (hdec : frameCurvature g e.base e.frame =
      einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame))
    (hT : (plusWeyl g e.base e.frame).trace = 0)
    (hU : (minusWeyl g e.base e.frame).trace = 0) :
    ((1 : Mat3) + frameCurvatureField g e).trace = 3 := by
  have he : (1 : Mat3) + (normalCurvature g e.base e.frame firstDirection - 1) =
      normalCurvature g e.base e.frame firstDirection := by abel
  change ((1 : Mat3) + (normalCurvature g e.base e.frame firstDirection - 1)).trace = 3
  rw [he]
  exact normalCurvature_trace g e.base e.frame firstDirection hdec hT hU

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.mem_scalarH1MeanZero _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1SubtractMean_idempotent _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_equiv _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_none _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_some _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradientL2_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradient_subtractMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Smooth two-form fields are defined by their actual coefficients in
local positively oriented orthonormal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem TwoFormSmooth.hodge {o : FrameOrientation g} {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) : TwoFormSmooth o (fun c => twoFormHodge (u c)) := by
  intro c S hS U hU hUt hp
  have hs := twoFormHodge.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hu c S hS U hU hUt hp)
  apply hs.congr
  intro z hz
  change twoFormChartValue o (fun x => twoFormHodge (u x)) c S hS z =
    twoFormHodge (twoFormChartValue o u c S hS z)
  simp only [twoFormChartValue, dite_eq_left (hUt hz)]
  exact twoFormFrameValue_hodge o u _ (hp z hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual frame Laplacian descends to a smooth scalar on the base.
This supplies smooth test functions for the distributional Poisson equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartScalarLaplacian (g : SmoothMetric M) (a : M → ℝ) (c : M) (z : FourSpace) : ℝ :=
  ∑ i, frameTensor (chartGramMatrix g c 1 z) (iteratedScalarDerivative g a c 2 z) ![i, i]

theorem chartScalarLaplacian_contDiffAt (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (chartScalarLaplacian g a c) z := by
  unfold chartScalarLaplacian
  simp_rw [frameTensor_two]
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.sum
  intro k _
  exact ((chartGramMatrix_contDiffAt g c 1 z hz j i).mul
    (chartGramMatrix_contDiffAt g c 1 z hz k i)).mul
      (iteratedScalarDerivative_contDiffAt g ha c 2 z hz ![j, k])

theorem chartScalarLaplacian_eq_base (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (c : M) (z : ChartTarget c) :
    chartScalarLaplacian g a c z = scalarLaplacianBase g a ((chartAt FourSpace c).symm z) := by
  have hc := iteratedScalarDerivative_transition g ha c ((chartAt FourSpace c).symm z)
    2 z z.property (mem_chart_source FourSpace ((chartAt FourSpace c).symm z))
  rw [chartTransitionMatrix_to_center c z z.property] at hc
  rw [chartScalarLaplacian, hc]
  simp_rw [← frameTensor_mul]
  have hz : chartTransition c ((chartAt FourSpace c).symm z) z =
      chartAt FourSpace ((chartAt FourSpace c).symm z) ((chartAt FourSpace c).symm z) := rfl
  rw [hz]
  change scalarLaplacian g a (chartGramSection g c 1 (by simp) z) = _
  exact scalarLaplacian_eq_base g a _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The horizontal frame equation with a fixed, arbitrary initial direction.
Unlike choosing a unit direction, this equation is smooth at zero velocity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatRadialFrameVelocity (q : HeatRadialFrameSpace) : Fin 4 → ℝ :=
  q.2.2 *ᵥ WithLp.ofLp q.1

def heatRadialFrameConnection (g : SmoothMetric M) (c : M)
    (q : HeatRadialFrameSpace) : Mat4 :=
  ∑ r : Fin 4, heatRadialFrameVelocity q r • connectionMatrix g c r q.2.1

def heatRadialFrameField (g : SmoothMetric M) (c : M)
    (q : HeatRadialFrameSpace) : HeatRadialFrameSpace :=
  (0, (WithLp.toLp 2 (heatRadialFrameVelocity q),
    -(heatRadialFrameConnection g c q * q.2.2)))

theorem heatRadialFrameField_contDiffAt (g : SmoothMetric M) (c : M)
    (q : HeatRadialFrameSpace) (hq : q.2.1 ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (heatRadialFrameField g c) q := by
  have hv (r : Fin 4) : ContDiffAt ℝ ∞ (fun p : HeatRadialFrameSpace =>
      heatRadialFrameVelocity p r) q := by
    change ContDiffAt ℝ ∞ (fun p : HeatRadialFrameSpace => ∑ k : Fin 4,
      p.2.2 r k * p.1 k) q
    apply ContDiffAt.sum
    intro k _
    fun_prop
  have hz : ContDiffAt ℝ ∞ (fun p : HeatRadialFrameSpace => p.2.1) q :=
    contDiffAt_fst.comp q contDiffAt_snd
  have hΓ (r i j : Fin 4) : ContDiffAt ℝ ∞ (fun p : HeatRadialFrameSpace =>
      christoffel g c p.2.1 i r j) q := by
    exact ContDiffAt.comp (f := fun p : HeatRadialFrameSpace => p.2.1)
      (g := fun w => christoffel g c w i r j) q
      (christoffel_contDiffAt g c q.2.1 hq
        (metricInChart_posDef g c q.2.1 hq).det_pos.ne' i r j) hz
  have hbase : ContDiffAt ℝ ∞ (fun p : HeatRadialFrameSpace =>
      WithLp.toLp 2 (heatRadialFrameVelocity p)) q :=
    (contDiffAt_piLp 2).mpr hv
  have hmatrix : ContDiffAt ℝ ∞ (fun p : HeatRadialFrameSpace =>
      -(heatRadialFrameConnection g c p * p.2.2)) q := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    change ContDiffAt ℝ ∞ (fun p : HeatRadialFrameSpace =>
      -(∑ k : Fin 4, (∑ r : Fin 4, heatRadialFrameVelocity p r *
        christoffel g c p.2.1 i r k) * p.2.2 k j)) q
    apply ContDiffAt.neg
    apply ContDiffAt.sum
    intro k _
    exact (ContDiffAt.sum (fun r _ => (hv r).mul (hΓ r i k))).mul (by fun_prop)
  exact contDiffAt_const.prodMk (hbase.prodMk hmatrix)

theorem heatRadialFrameField_zero_direction (g : SmoothMetric M) (c : M)
    (p : CoordinateFrameSpace) : heatRadialFrameField g c (0, p) = 0 := by
  simp [heatRadialFrameField, heatRadialFrameVelocity, heatRadialFrameConnection]

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

theorem chartScalarLaplacian_coefficients (g : SmoothMetric M) (a : M → ℝ)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    chartScalarLaplacian g a c z = ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
      (partialDeriv (fun w => partialDeriv
        (fun v => a ((chartAt FourSpace c).symm v)) j w) i z -
        ∑ k, christoffel g c z k i j *
          partialDeriv (fun w => a ((chartAt FourSpace c).symm w)) k z) := by
  rw [chartScalarLaplacian, frameTensor_trace_two, chartGramMatrix_mul_transpose g c z hz]
  simp_rw [scalarCoordinate_hessian]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual local radial-frame trajectories with finite smooth dependence
at zero velocity, constructed by the Picard flow. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

structure HeatRadialFrameFlow (g : SmoothMetric M) (c : M) (p : CoordinateFrameSpace) where
  radius : ℝ
  radius_pos : 0 < radius
  time : ℝ
  time_pos : 0 < time
  map : HeatRadialFrameSpace × ℝ → HeatRadialFrameSpace
  continuous : ContinuousOn map (closedBall (0, p) radius ×ˢ Ioo (-time) time)
  initial : ∀ q ∈ closedBall (0, p) radius, map (q, 0) = q
  in_chart : ∀ q ∈ closedBall (0, p) radius, ∀ t ∈ Ioo (-time) time,
    (map (q, t)).2.1 ∈ (chartAt FourSpace c).target
  derivative : ∀ q ∈ closedBall (0, p) radius, ∀ t ∈ Ioo (-time) time,
    HasDerivAt (fun s => map (q, s)) (heatRadialFrameField g c (map (q, t))) t
  regular : ∀ n : ℕ, ContDiffAt ℝ n map ((0, p), 0)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial-frame flow keeps its direction and preserves the actual
metric Gram matrix of the transported frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem HeatRadialFrameFlow.direction {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    (q : HeatRadialFrameSpace) (hq : q ∈ Metric.closedBall (0, p) F.radius)
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) : (F.map (q, t)).1 = q.1 := by
  have hd (s : ℝ) (hs : s ∈ Ioo (-F.time) F.time) :
      HasDerivAt (fun r => (F.map (q, r)).1) 0 s := (F.derivative q hq s hs).fst
  have hz : (0 : ℝ) ∈ Ioo (-F.time) F.time := ⟨by linarith [F.time_pos], F.time_pos⟩
  have h := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo _ _).isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) ht hz
  simpa only [F.initial q hq] using h

theorem HeatRadialFrameFlow.stationary {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) : F.map ((0, p), t) = (0, p) := by
  have hq : ((0 : FourSpace), p) ∈ Metric.closedBall (0, p) F.radius :=
    Metric.mem_closedBall_self F.radius_pos.le
  have hd (s : ℝ) (hs : s ∈ Ioo (-F.time) F.time) :
      HasDerivAt (fun r => F.map ((0, p), r)) 0 s := by
    have h := F.derivative (0, p) hq s hs
    have he : F.map ((0, p), s) = (0, (F.map ((0, p), s)).2) :=
      Prod.ext (F.direction (0, p) hq s hs) rfl
    rw [he, heatRadialFrameField_zero_direction] at h
    exact h
  have hz : (0 : ℝ) ∈ Ioo (-F.time) F.time := ⟨by linarith [F.time_pos], F.time_pos⟩
  have h := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo _ _).isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) ht hz
  simpa only [F.initial (0, p) hq] using h

theorem heatRadialFrameGram_hasDerivAt_zero (g : SmoothMetric M) (c : M)
    (α : ℝ → HeatRadialFrameSpace) (t : ℝ)
    (ht : (α t).2.1 ∈ (chartAt FourSpace c).target)
    (hd : HasDerivAt α (heatRadialFrameField g c (α t)) t) :
    HasDerivAt (fun s => (α s).2.2ᵀ * metricInChart g c (α s).2.1 * (α s).2.2) 0 t := by
  let G : ℝ → Mat4 := fun s => metricInChart g c (α s).2.1
  let E : ℝ → Mat4 := fun s => (α s).2.2
  let U := heatRadialFrameConnection g c (α t)
  let P : Mat4 := -(U * E t)
  let D : Mat4 := Uᵀ * G t + G t * U
  have hx : HasDerivAt (fun s => (α s).2.1)
      (WithLp.toLp 2 (heatRadialFrameVelocity (α t))) t := hd.snd.fst
  have hG (i j : Fin 4) : HasDerivAt (fun s => G s i j) (D i j) t := by
    have hg := hasDerivAt_coordinate_comp hx
      ((metricInChart_contDiffAt g c (α t).2.1 ht i j).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    have hr := congrFun (congrFun (parallelFrame_metric_rate g c (α t).2.1 ht
      (heatRadialFrameVelocity (α t))) i) j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, matrixPartial] at hr
    change (∑ r, heatRadialFrameVelocity (α t) r *
      partialDeriv (fun z => metricInChart g c z i j) r (α t).2.1) = D i j at hr
    rwa [hr] at hg
  have hP (i j : Fin 4) : HasDerivAt (fun s => E s i j) (P i j) t :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp hd.snd.snd i) j
  have hTG := heatMatrixProduct_hasDerivAt (fun s => (E s)ᵀ) G Pᵀ D t
    (fun i j => hP j i) hG
  have hprod := heatMatrixProduct_hasDerivAt (fun s => (E s)ᵀ * G s) E
    (Pᵀ * G t + (E t)ᵀ * D) P t hTG hP
  have he : (Pᵀ * G t + (E t)ᵀ * D) * E t + (E t)ᵀ * G t * P = 0 := by
    dsimp only [P, D]
    simp only [Matrix.transpose_neg, Matrix.transpose_mul]
    noncomm_ring
  rw [he] at hprod
  exact hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (hprod i))

theorem HeatRadialFrameFlow.gram {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    (q : HeatRadialFrameSpace) (hq : q ∈ Metric.closedBall (0, p) F.radius)
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) :
    (F.map (q, t)).2.2ᵀ * metricInChart g c (F.map (q, t)).2.1 * (F.map (q, t)).2.2 =
      q.2.2ᵀ * metricInChart g c q.2.1 * q.2.2 := by
  have hd (s : ℝ) (hs : s ∈ Ioo (-F.time) F.time) :=
    heatRadialFrameGram_hasDerivAt_zero g c (fun r => F.map (q, r)) s
      (F.in_chart q hq s hs) (F.derivative q hq s hs)
  have hz : (0 : ℝ) ∈ Ioo (-F.time) F.time := ⟨by linarith [F.time_pos], F.time_pos⟩
  have h := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo _ _).isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) ht hz
  simpa only [F.initial q hq] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Frame-independent energies descend continuously through the compact
frame bundle. Their integrability follows from finite Riemannian volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem actual_baseCurvature (o : FrameOrientation g) (hRic : RicciThree g)
    (c : M) (e : OrthonormalFrame g c) :
    normalizedBlockNorm (plusWeyl g c e) ^ 2 + normalizedBlockNorm (minusWeyl g c e) ^ 2 =
      plusNorm o c ^ 2 + minusNorm o c ^ 2 :=
  frame_weyl_norm_sum_same_base e (o.frame c) hRic

theorem actual_baseDerivative (o : FrameOrientation g) (hRic : RicciThree g)
    (c : M) (e : OrthonormalFrame g c) :
    gradientSquareNorm (plusWeylGradient g c e) + gradientSquareNorm (minusWeylGradient g c e) =
      plusGradientEnergy o c + minusGradientEnergy o c :=
  frame_weyl_gradient_sum_same_base e (o.frame c) hRic

variable [CompactSpace (FrameBundle g)]

theorem compactSpace_of_compact_frames (g : SmoothMetric M)
    [CompactSpace (FrameBundle g)] : CompactSpace M := by
  apply isCompact_univ_iff.mp
  simpa only [Set.image_univ, Set.range_eq_univ.mpr (frameBase_surjective g)] using
    (isCompact_univ : IsCompact (Set.univ : Set (FrameBundle g))).image (continuous_frameBase g)

variable [T3Space M]

theorem continuous_totalGradientEnergy (d : MetricGreenData g μ) (opposite : OppositeWeylData d)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    Continuous (fun c => plusGradientEnergy o c + minusGradientEnergy o c) := by
  have hq := Topology.IsQuotientMap.of_surjective_continuous
    (frameBase_surjective g) (continuous_frameBase g)
  apply hq.continuous_iff.mpr
  have hc := (continuous_gradientSquareNorm _ d.continuousGradient).add
    (continuous_gradientSquareNorm _ opposite.continuousGradient)
  change Continuous (fun e : FrameBundle g =>
    plusGradientEnergy o e.base + minusGradientEnergy o e.base)
  have heq : (fun e : FrameBundle g =>
      plusGradientEnergy o e.base + minusGradientEnergy o e.base) =
      (fun e : FrameBundle g => gradientSquareNorm (plusWeylGradient g e.base e.frame) +
        gradientSquareNorm (minusWeylGradient g e.base e.frame)) := by
    funext e
    exact (actual_baseDerivative o hRic e.base e.frame).symm
  rw [heq]
  exact hc

end
end PositiveEinsteinFour.Geometry
end


section

/-! The total second-variation boundary term is independent of the chart.
The second coordinate jet includes the Hessian of the actual chart change;
the Christoffel transformation cancels exactly that extra term. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartTransitionSecondJet (c d : M) (z : FourSpace)
    (y u : JacobiCoordinateVector) : JacobiCoordinateVector :=
  chartTransitionMatrix c d z *ᵥ u + chartTransitionSecondVector c d z y

theorem chartTransition_connection_equation (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i : Fin 4) :
    chartTransitionMatrix c d z * connectionMatrix g c i z =
      matrixPartial (chartTransitionMatrix c d) i z +
        weightedConnection (chartTransitionMatrix c d z)
          (fun a => connectionMatrix g d a (chartTransition c d z)) i *
            chartTransitionMatrix c d z := by
  have he : connectionMatrix g c i z = pulledChartConnection g c d z i := by
    ext a b
    exact christoffel_transition g c d z hz hx a i b
  rw [he]
  exact pulledConnection_equation _ _ _
    (isUnit_iff_ne_zero.mpr (chartTransitionMatrix_det_ne_zero g c d z hz hx))

/-- The corrected second coordinate jet transforms as a tangent vector. -/
theorem actual_covariantSecondJet_transition (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source)
    (y u : JacobiCoordinateVector) :
    chartTransitionMatrix c d z *ᵥ
        jacobiCovariantSecondJet (fun i => connectionMatrix g c i z) y u =
      jacobiCovariantSecondJet
        (fun i => connectionMatrix g d i (chartTransition c d z))
        (chartTransitionMatrix c d z *ᵥ y) (chartTransitionSecondJet c d z y u) :=
  jacobiCovariantSecondJet_pullback _ _ _ _
    (chartTransition_connection_equation g c d z hz hx) y u

/-- The full second-variation boundary scalar agrees on overlapping charts. -/
theorem actual_secondVariationBoundary_transition (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source)
    (v y u : JacobiCoordinateVector) :
    jacobiMetricPair (metricInChart g c z) v
        (jacobiCovariantSecondJet (fun i => connectionMatrix g c i z) y u) =
      jacobiMetricPair (metricInChart g d (chartTransition c d z))
        (chartTransitionMatrix c d z *ᵥ v)
        (jacobiCovariantSecondJet
          (fun i => connectionMatrix g d i (chartTransition c d z))
          (chartTransitionMatrix c d z *ᵥ y) (chartTransitionSecondJet c d z y u)) := by
  rw [jacobiMetricPair_pullback _ _ _ (metricInChart_transition g c d z hz hx),
    actual_covariantSecondJet_transition g c d z hz hx]

theorem chartTransition_hasDerivAt (c d : M) (x : ℝ → FourSpace)
    (y : JacobiCoordinateVector) (t : ℝ)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm (x t) ∈ (chartAt FourSpace d).source)
    (hx : HasDerivAt x (WithLp.toLp 2 y) t) :
    HasDerivAt (fun s => chartTransition c d (x s))
      (WithLp.toLp 2 (chartTransitionMatrix c d (x t) *ᵥ y)) t := by
  rw [chartTransitionMatrix_mulVec]
  exact ((chartTransition_contDiffAt c d (x t) hz hd).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp_hasDerivAt t hx

/-- A genuine raw second jet has the Hessian-corrected transformation used above. -/
theorem chartTransition_secondJet_hasDerivAt (c d : M)
    (x : ℝ → FourSpace) (y : ℝ → JacobiCoordinateVector)
    (u : JacobiCoordinateVector) (t : ℝ)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm (x t) ∈ (chartAt FourSpace d).source)
    (hx : HasDerivAt x (WithLp.toLp 2 (y t)) t) (hy : HasDerivAt y u t) :
    HasDerivAt (fun s => chartTransitionMatrix c d (x s) *ᵥ y s)
      (chartTransitionSecondJet c d (x t) (y t) u) t := by
  let P : Mat4 := jacobiConnection
    (fun i => matrixPartial (chartTransitionMatrix c d) i (x t)) (y t)
  have hJ (a b : Fin 4) : HasDerivAt
      (fun s => chartTransitionMatrix c d (x s) a b) (P a b) t := by
    have h := hasDerivAt_coordinate_comp hx
      ((chartTransitionMatrix_contDiffAt c d (x t) hz hd a b).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    simpa only [P, jacobiConnection, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, matrixPartial] using h
  have hprod : HasDerivAt (fun s => chartTransitionMatrix c d (x s) *ᵥ y s)
      (P *ᵥ y t + chartTransitionMatrix c d (x t) *ᵥ u) t := by
    apply hasDerivAt_pi.mpr
    intro i
    have h := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
      (hJ i j).mul (hasDerivAt_pi.mp hy j))
    simpa only [Matrix.mulVec, dotProduct, Pi.mul_apply, Pi.add_apply,
      Finset.sum_add_distrib] using h
  simpa only [chartTransitionSecondJet, chartTransitionSecondVector, P, add_comm] using hprod

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth finite-order endpoint frames for arbitrary small velocities,
including zero. The frame equations and orthonormality come from the
constructed horizontal ODE, not from a choice of unit directions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem HeatRadialFrameFlow.exists_pos_slice {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p) (n : ℕ) :
    ∃ t > (0 : ℝ), t ∈ Ioo (-F.time) F.time ∧
      ContDiffAt ℝ n (fun q => F.map (q, t)) (0, p) := by
  have hn := (F.regular n).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have htend : Tendsto (fun t : ℝ => (((0 : FourSpace), p), t))
      (𝓝 0) (𝓝 (((0 : FourSpace), p), 0)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp (htend.eventually hn)
  let t := min F.time δ / 2
  have ht0 : 0 < t := half_pos (lt_min F.time_pos hδ)
  have htT : t < F.time := (half_lt_self (lt_min F.time_pos hδ)).trans_le (min_le_left _ _)
  have htδ : t < δ := (half_lt_self (lt_min F.time_pos hδ)).trans_le (min_le_right _ _)
  refine ⟨t, ht0, ⟨by linarith [F.time_pos], htT⟩, ?_⟩
  have hFt : ContDiffAt ℝ n F.map ((0, p), t) :=
    hnear (by simpa only [Real.dist_eq, sub_zero, abs_of_pos ht0] using htδ)
  exact hFt.comp (0, p) (contDiffAt_id.prodMk contDiffAt_const)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial-frame trajectories project to the actual metric Hamiltonian
trajectories. A constant matrix packages the arbitrary direction as a
column, so the cotangent-lift identity applies. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatRadialCotangentState (g : SmoothMetric M) (c : M) (v : FourSpace)
    (p : CoordinateFrameSpace) : CotangentCoordinates :=
  (p.1, WithLp.toLp 2 (metricInChart g c p.1 *ᵥ (p.2 *ᵥ WithLp.ofLp v)))

theorem hasDerivAt_heatRadialCotangentState (g : SmoothMetric M) (c : M)
    (v : FourSpace) (x : ℝ → FourSpace) (E : ℝ → Mat4) (t : ℝ)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x (WithLp.toLp 2 (E t *ᵥ WithLp.ofLp v)) t)
    (hE : ∀ i j, HasDerivAt (fun s => E s i j)
      (-((∑ r : Fin 4, (E t *ᵥ WithLp.ofLp v) r • connectionMatrix g c r (x t)) * E t) i j) t) :
    HasDerivAt (fun s => heatRadialCotangentState g c v (x s, E s))
      (cotangentHamiltonianField (kineticHamiltonian g c)
        (heatRadialCotangentState g c v (x t, E t))) t := by
  let V : Mat4 := fun i _ => v i
  let B : ℝ → Mat4 := fun s => E s * V
  let C : Mat4 := ∑ r : Fin 4, (E t *ᵥ WithLp.ofLp v) r • connectionMatrix g c r (x t)
  have hBcol (s : ℝ) (i j : Fin 4) : B s i j = (E s *ᵥ WithLp.ofLp v) i := rfl
  have hC : parallelFrameConnection g c 0 (x t, B t) = C := rfl
  have hB (i j : Fin 4) : HasDerivAt (fun s => B s i j)
      (-(C * B t) i j) t := by
    have h := HasDerivAt.fun_sum (fun k (_ : k ∈ Finset.univ) =>
      (hE i k).mul_const (V k j))
    have he : (-(C * E t)) * V = -(C * B t) := by
      simp only [B, Matrix.neg_mul, Matrix.mul_assoc]
    change HasDerivAt (fun s => B s i j) (((-(C * E t)) * V) i j) t at h
    rwa [he] at h
  have hxB : HasDerivAt x (WithLp.toLp 2 (fun r => B t r 0)) t := hx
  have h := hasDerivAt_parallelFrame_cotangentLift g c x B t 0 hz hxB
    (fun i j => by simpa only [hC] using hB i j)
  exact h

theorem HeatRadialFrameFlow.cotangent_derivative {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    (q : HeatRadialFrameSpace) (hq : q ∈ Metric.closedBall (0, p) F.radius)
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) :
    HasDerivAt (fun s => heatRadialCotangentState g c q.1 (F.map (q, s)).2)
      (cotangentHamiltonianField (kineticHamiltonian g c)
        (heatRadialCotangentState g c q.1 (F.map (q, t)).2)) t := by
  have hdir := F.direction q hq t ht
  have hd := F.derivative q hq t ht
  have hx : HasDerivAt (fun s => (F.map (q, s)).2.1)
      (WithLp.toLp 2 ((F.map (q, t)).2.2 *ᵥ WithLp.ofLp q.1)) t := by
    have h : HasDerivAt (fun s => (F.map (q, s)).2.1)
        (WithLp.toLp 2 (heatRadialFrameVelocity (F.map (q, t)))) t := hd.snd.fst
    simpa only [heatRadialFrameVelocity, hdir] using! h
  have hE (i j : Fin 4) : HasDerivAt (fun s => (F.map (q, s)).2.2 i j)
      (-((∑ r : Fin 4, ((F.map (q, t)).2.2 *ᵥ WithLp.ofLp q.1) r •
        connectionMatrix g c r (F.map (q, t)).2.1) * (F.map (q, t)).2.2) i j) t := by
    have h := hasDerivAt_pi.mp (hasDerivAt_pi.mp hd.snd.snd i) j
    simpa only [heatRadialFrameField, heatRadialFrameConnection, heatRadialFrameVelocity,
      hdir] using! h
  exact hasDerivAt_heatRadialCotangentState g c q.1 (fun s => (F.map (q, s)).2.1)
    (fun s => (F.map (q, s)).2.2) t (F.in_chart q hq t ht) hx hE

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniqueness on the common interval for the actual radial frame ODE. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem HeatRadialFrameFlow.eq_on {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    (q : HeatRadialFrameSpace) (hq : q ∈ closedBall (0, p) F.radius)
    (γ : ℝ → HeatRadialFrameSpace) (hγ0 : γ 0 = q)
    (hγ : ∀ t ∈ Ioo (-F.time) F.time,
      HasDerivAt γ (heatRadialFrameField g c (γ t)) t) :
    EqOn (fun t => F.map (q, t)) γ (Ioo (-F.time) F.time) := by
  let f := heatRadialFrameField g c
  let I := Ioo (-F.time) F.time
  let : PreconnectedSpace I :=
    isPreconnected_iff_preconnectedSpace.mp (convex_Ioo _ _).isPreconnected
  let S : Set I := {t | F.map (q, t.val) = γ t.val}
  have hcF : Continuous (fun t : I => F.map (q, t.val)) :=
    (HasDerivAt.continuousOn (fun t ht => F.derivative q hq t ht)).domRestrict
  have hcγ : Continuous (fun t : I => γ t.val) := (HasDerivAt.continuousOn hγ).domRestrict
  have hclosed : IsClosed S := isClosed_eq hcF hcγ
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    change F.map (q, s.val) = γ s.val at hs
    have hf : ContDiffAt ℝ 1 f (F.map (q, s.val)) :=
      (heatRadialFrameField_contDiffAt g c _ (F.in_chart q hq s.val s.property)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    obtain ⟨K, U, hU, hLip⟩ := hf.exists_lipschitzOnWith
    have hn : ∀ᶠ t in 𝓝 s.val, t ∈ I := isOpen_Ioo.mem_nhds s.property
    have hdF := hn.mono fun t ht => F.derivative q hq t ht
    have hdγ := hn.mono fun t ht => hγ t ht
    have hFU := hdF.self_of_nhds.continuousAt.preimage_mem_nhds hU
    have hγU := hdγ.self_of_nhds.continuousAt.preimage_mem_nhds
      (by simpa only [← hs] using hU)
    have heq := ODE_solution_unique_of_eventually
      (Filter.Eventually.of_forall fun _ => hLip) (hdF.and hFU) (hdγ.and hγU) hs
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds heq
  have hz : (0 : ℝ) ∈ I := ⟨by linarith [F.time_pos], F.time_pos⟩
  have hfull : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ
    ⟨⟨0, hz⟩, (F.initial q hq).trans hγ0.symm⟩
  intro t ht
  have h : (⟨t, ht⟩ : I) ∈ S := by rw [hfull]; trivial
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrating the actual coordinate second variation.  Parameter derivatives
are raw derivatives of the position and velocity; time derivatives are the
geodesic equation and the two mixed derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartEnergyDensity (g : SmoothMetric M) (c : M)
    (z : FourSpace) (v : JacobiCoordinateVector) : ℝ :=
  (1 / 2 : ℝ) * jacobiMetricPair (metricInChart g c z) v v

def chartEnergyFirstDensity (g : SmoothMetric M) (c : M)
    (z : FourSpace) (y v w : JacobiCoordinateVector) : ℝ :=
  (1 / 2 : ℝ) * jacobiMetricPair (jacobiMetricFirstDirectional g c z y) v v +
    jacobiMetricPair (metricInChart g c z) v w

def chartEnergySecondDensity (g : SmoothMetric M) (c : M)
    (z : FourSpace) (y v w u q : JacobiCoordinateVector) : ℝ :=
  coordinateEnergySecondDensity (metricInChart g c z)
      (jacobiMetricFirstDirectional g c z y) (jacobiMetricSecondDirectional g c z y) v w +
    (1 / 2 : ℝ) * jacobiMetricPair (jacobiMetricFirstDirectional g c z u) v v +
      jacobiMetricPair (metricInChart g c z) v q

def chartEnergyIndexDensity (g : SmoothMetric M) (c : M)
    (z : FourSpace) (v y w : JacobiCoordinateVector) : ℝ :=
  coordinateIndexDensity (metricInChart g c z) (fun i => connectionMatrix g c i z)
    (fun i j => matrixPartial (connectionMatrix g c j) i z) v y w

def chartEnergyBoundary (g : SmoothMetric M) (c : M)
    (z : FourSpace) (v y u : JacobiCoordinateVector) : ℝ :=
  jacobiMetricPair (metricInChart g c z) v
    (jacobiCovariantSecondJet (fun i => connectionMatrix g c i z) y u)

theorem chartEnergy_firstJet_hasDerivAt (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (v : ℝ → JacobiCoordinateVector)
    (y w : JacobiCoordinateVector) (s : ℝ)
    (hz : x s ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x (WithLp.toLp 2 y) s) (hv : HasDerivAt v w s) :
    HasDerivAt (fun r => chartEnergyDensity g c (x r) (v r))
      (chartEnergyFirstDensity g c (x s) y (v s) w) s := by
  let G := metricInChart g c (x s)
  let H := jacobiMetricFirstDirectional g c (x s) y
  have hG (i j : Fin 4) : HasDerivAt (fun r => metricInChart g c (x r) i j) (H i j) s := by
    have hd := hasDerivAt_coordinate_comp hx
      ((metricInChart_contDiffAt g c (x s) hz i j).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    simpa only [H, jacobiMetricFirstDirectional, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, matrixPartial] using hd
  have hp (i : Fin 4) : HasDerivAt (fun r => (metricInChart g c (x r) *ᵥ v r) i)
      ((H *ᵥ v s + G *ᵥ w) i) s := by
    have hd := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
      (hG i j).mul (hasDerivAt_pi.mp hv j))
    simpa only [G, Matrix.mulVec, dotProduct, Pi.mul_apply, Pi.add_apply,
      Finset.sum_add_distrib] using hd
  have hd := (HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
    (hasDerivAt_pi.mp hv i).mul (hp i))).const_mul (1 / 2 : ℝ)
  have hs : G.IsSymm := by
    ext i j
    exact metricInChart_comm g c (x s) j i
  have heq : (1 / 2 : ℝ) * (∑ i,
      (w i * (G *ᵥ v s) i + v s i * (H *ᵥ v s + G *ᵥ w) i)) =
      chartEnergyFirstDensity g c (x s) y (v s) w := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    change (1 / 2 : ℝ) * jacobiMetricPair G w (v s) +
      ((1 / 2 : ℝ) * jacobiMetricPair H (v s) (v s) +
        (1 / 2 : ℝ) * jacobiMetricPair G (v s) w) = _
    rw [jacobiMetricPair_symm hs w (v s)]
    unfold chartEnergyFirstDensity
    change _ = (1 / 2 : ℝ) * jacobiMetricPair H (v s) (v s) + jacobiMetricPair G (v s) w
    ring
  rw [heq] at hd
  simpa only [chartEnergyDensity, jacobiMetricPair, dotProduct, Pi.mul_apply, G] using hd

theorem chartEnergy_secondJet_hasDerivAt (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (y v w : ℝ → JacobiCoordinateVector)
    (u q : JacobiCoordinateVector) (s : ℝ)
    (hz : x s ∈ (chartAt FourSpace c).target)
    (hx : ∀ᶠ r in 𝓝 s, HasDerivAt x (WithLp.toLp 2 (y r)) r)
    (hy : HasDerivAt y u s)
    (hv : ∀ᶠ r in 𝓝 s, HasDerivAt v (w r) r) (hw : HasDerivAt w q s) :
    HasDerivAt (deriv (fun r => chartEnergyDensity g c (x r) (v r)))
      (chartEnergySecondDensity g c (x s) (y s) (v s) (w s) u q) s := by
  have ht : Tendsto (fun r : ℝ => s + r) (𝓝 0) (𝓝 s) := by
    have hcont : Continuous (fun r : ℝ => s + r) := continuous_const.add continuous_id
    simpa only [add_zero] using hcont.tendsto 0
  have hx' : ∀ᶠ r in 𝓝 (0 : ℝ),
      HasDerivAt (fun r => x (s + r)) (WithLp.toLp 2 (y (s + r))) r := by
    filter_upwards [ht.eventually hx] with r hr
    exact hr.comp_const_add s r
  have hv' : ∀ᶠ r in 𝓝 (0 : ℝ),
      HasDerivAt (fun r => v (s + r)) (w (s + r)) r := by
    filter_upwards [ht.eventually hv] with r hr
    exact hr.comp_const_add s r
  have hy' : HasDerivAt (fun r => y (s + r)) u 0 := by
    apply HasDerivAt.comp_const_add s 0
    simpa only [add_zero] using hy
  have hw' : HasDerivAt (fun r => w (s + r)) q 0 := by
    apply HasDerivAt.comp_const_add s 0
    simpa only [add_zero] using hw
  have h := actual_metricEnergy_secondJet g c (fun r => x (s + r))
    (fun r => y (s + r)) (fun r => v (s + r)) (fun r => w (s + r)) u q
    (by simpa only [add_zero] using hz) hx' hy' hv' hw'
  apply secondDeriv_at_of_shift
  simpa only [chartEnergyDensity, chartEnergySecondDensity, add_zero] using h

theorem chartEnergyFirst_hasDerivAt (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (y v w : ℝ → JacobiCoordinateVector)
    (u q : JacobiCoordinateVector) (s : ℝ)
    (hz : x s ∈ (chartAt FourSpace c).target)
    (hx : ∀ᶠ r in 𝓝 s, HasDerivAt x (WithLp.toLp 2 (y r)) r)
    (hy : HasDerivAt y u s)
    (hv : ∀ᶠ r in 𝓝 s, HasDerivAt v (w r) r) (hw : HasDerivAt w q s) :
    HasDerivAt (fun r => chartEnergyFirstDensity g c (x r) (y r) (v r) (w r))
      (chartEnergySecondDensity g c (x s) (y s) (v s) (w s) u q) s := by
  have hsecond := chartEnergy_secondJet_hasDerivAt g c x y v w u q s hz hx hy hv hw
  have hnear : ∀ᶠ r in 𝓝 s, x r ∈ (chartAt FourSpace c).target :=
    hx.self_of_nhds.continuousAt.eventually ((chartAt FourSpace c).open_target.mem_nhds hz)
  apply hsecond.congr_of_eventuallyEq
  filter_upwards [hnear, hx, hv] with r hr hxr hvr
  exact (chartEnergy_firstJet_hasDerivAt g c x v (y r) (w r) r hr hxr hvr).deriv.symm

/-- Differentiation under the energy integral uses only the ordinary raw
parameter jets and joint continuity of the three explicit scalar densities. -/
theorem chartEnergyIntegral_secondDeriv (g : SmoothMetric M) (c : M)
    (x : ℝ → ℝ → FourSpace) (y v w u q : ℝ → ℝ → JacobiCoordinateVector)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    (hz : ∀ s ∈ Icc (-δ) δ, ∀ t ∈ Icc a b, x s t ∈ (chartAt FourSpace c).target)
    (hx : ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => x r t) (WithLp.toLp 2 (y s t)) s)
    (hy : ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => y r t) (u s t) s)
    (hv : ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => v r t) (w s t) s)
    (hw : ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => w r t) (q s t) s)
    (hF : ContinuousOn (fun p : ℝ × ℝ => chartEnergyDensity g c (x p.1 p.2) (v p.1 p.2))
      (Icc (-δ) δ ×ˢ Icc a b))
    (hG : ContinuousOn (fun p : ℝ × ℝ =>
      chartEnergyFirstDensity g c (x p.1 p.2) (y p.1 p.2) (v p.1 p.2) (w p.1 p.2))
      (Icc (-δ) δ ×ˢ Icc a b))
    (hH : ContinuousOn (fun p : ℝ × ℝ => chartEnergySecondDensity g c (x p.1 p.2)
      (y p.1 p.2) (v p.1 p.2) (w p.1 p.2) (u p.1 p.2) (q p.1 p.2))
      (Icc (-δ) δ ×ˢ Icc a b)) :
    HasDerivAt (deriv (fun s => ∫ t in a..b, chartEnergyDensity g c (x s t) (v s t)))
      (∫ t in a..b, chartEnergySecondDensity g c (x 0 t)
        (y 0 t) (v 0 t) (w 0 t) (u 0 t) (q 0 t)) 0 := by
  apply intervalIntegral_secondDeriv_rectangle
    (fun s t => chartEnergyDensity g c (x s t) (v s t))
    (fun s t => chartEnergyFirstDensity g c (x s t) (y s t) (v s t) (w s t))
    (fun s t => chartEnergySecondDensity g c (x s t) (y s t) (v s t)
      (w s t) (u s t) (q s t)) hδ hab hF hG hH
  · intro s hs t ht
    exact chartEnergy_firstJet_hasDerivAt g c (fun r => x r t) (fun r => v r t)
      (y s t) (w s t) s (hz s ⟨hs.1.le, hs.2.le⟩ t ht) (hx s hs t ht) (hv s hs t ht)
  · intro s hs t ht
    have hxnear : ∀ᶠ r in 𝓝 s,
        HasDerivAt (fun r => x r t) (WithLp.toLp 2 (y r t)) r := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      exact hx r hr t ht
    have hvnear : ∀ᶠ r in 𝓝 s, HasDerivAt (fun r => v r t) (w r t) r := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
      exact hv r hr t ht
    exact chartEnergyFirst_hasDerivAt g c (fun r => x r t) (fun r => y r t)
      (fun r => v r t) (fun r => w r t) (u s t) (q s t) s
      (hz s ⟨hs.1.le, hs.2.le⟩ t ht) hxnear (hy s hs t ht) hvnear (hw s hs t ht)

/-- The derivative of the total boundary, with no omitted second-jet term. -/
theorem chartEnergyBoundary_hasDerivAt (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (v y u : ℝ → JacobiCoordinateVector)
    (w q : JacobiCoordinateVector) (t : ℝ)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x (WithLp.toLp 2 (v t)) t)
    (hv : HasDerivAt v
      (-(jacobiConnection (fun i => connectionMatrix g c i (x t)) (v t) *ᵥ v t)) t)
    (hy : HasDerivAt y w t) (hu : HasDerivAt u q t) :
    HasDerivAt (fun s => chartEnergyBoundary g c (x s) (v s) (y s) (u s))
      (chartEnergySecondDensity g c (x t) (y t) (v t) w (u t) q -
        chartEnergyIndexDensity g c (x t) (v t) (y t) w) t := by
  have h₁ := actual_coordinateEnergyBoundary_hasDerivAt g c x v y _ w t hz hx hv hy rfl
  have h₂ := actual_metricEnergy_jetBoundary_hasDerivAt g c x v u _ q t hz hx hv hu rfl
  have h := h₂.add h₁
  have heq : (fun s => chartEnergyBoundary g c (x s) (v s) (y s) (u s)) =
      (fun s => jacobiMetricPair (metricInChart g c (x s)) (v s) (u s) +
        jacobiMetricPair (metricInChart g c (x s)) (v s)
          (jacobiConnection (fun i => connectionMatrix g c i (x s)) (y s) *ᵥ y s)) := by
    funext s
    exact jacobiMetricPair_add_right _ _ _ _
  change HasDerivAt (fun s =>
    jacobiMetricPair (metricInChart g c (x s)) (v s) (u s) +
      jacobiMetricPair (metricInChart g c (x s)) (v s)
        (jacobiConnection (fun i => connectionMatrix g c i (x s)) (y s) *ᵥ y s)) _ t at h
  rw [← heq] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [chartEnergySecondDensity, chartEnergyIndexDensity,
    actual_coordinateEnergySecondDensity g c (x t) hz]
  ring

theorem chartEnergySecond_integral (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (v y w u q : ℝ → JacobiCoordinateVector) (a b : ℝ)
    (hz : ∀ t ∈ uIcc a b, x t ∈ (chartAt FourSpace c).target)
    (hx : ∀ t ∈ uIcc a b, HasDerivAt x (WithLp.toLp 2 (v t)) t)
    (hv : ∀ t ∈ uIcc a b, HasDerivAt v
      (-(jacobiConnection (fun i => connectionMatrix g c i (x t)) (v t) *ᵥ v t)) t)
    (hy : ∀ t ∈ uIcc a b, HasDerivAt y (w t) t)
    (hu : ∀ t ∈ uIcc a b, HasDerivAt u (q t) t)
    (hS : IntervalIntegrable
      (fun t => chartEnergySecondDensity g c (x t) (y t) (v t) (w t) (u t) (q t)) volume a b)
    (hI : IntervalIntegrable
      (fun t => chartEnergyIndexDensity g c (x t) (v t) (y t) (w t)) volume a b) :
    (∫ t in a..b, chartEnergySecondDensity g c (x t) (y t) (v t) (w t) (u t) (q t)) =
      (∫ t in a..b, chartEnergyIndexDensity g c (x t) (v t) (y t) (w t)) +
        chartEnergyBoundary g c (x b) (v b) (y b) (u b) -
          chartEnergyBoundary g c (x a) (v a) (y a) (u a) := by
  have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => chartEnergyBoundary_hasDerivAt g c x v y u (w t) (q t) t
      (hz t ht) (hx t ht) (hv t ht) (hy t ht) (hu t ht)) (hS.sub hI)
  rw [intervalIntegral.integral_sub hS hI] at hd
  linarith

theorem chartEnergyBoundary_zero (g : SmoothMetric M) (c : M) (z : FourSpace)
    (v : JacobiCoordinateVector) : chartEnergyBoundary g c z v 0 0 = 0 := by
  simp [chartEnergyBoundary, jacobiCovariantSecondJet, jacobiConnection, jacobiMetricPair]

theorem chartEnergyBoundary_transition (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source)
    (v y u : JacobiCoordinateVector) :
    chartEnergyBoundary g c z v y u =
      chartEnergyBoundary g d (chartTransition c d z)
        (chartTransitionMatrix c d z *ᵥ v) (chartTransitionMatrix c d z *ᵥ y)
        (chartTransitionSecondJet c d z y u) :=
  actual_secondVariationBoundary_transition g c d z hz hd v y u

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial volume bound for the metric fields. The Weyl identities
are Gursky--LeBrun (1999), equations (3), (12) and Lemma 1; spherical
disintegration and parallel flow are Brin--Karcher (1984), Section 1.
The Jacobi/polar construction retains the ordinary ODE and polar density
formula (Sakai, Chapter II, Section 5), together with the diameter truncation.
No curvature-energy bound or radial-volume deficit is an input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

/-- Disintegration of the normalized frame measure for the metric energy calculation. -/
structure WeylEnergyIdentities (g : SmoothMetric M) (_o : FrameOrientation g)
    (μ : Measure (FrameBundle g)) where
  averaging : BrinKarcherAveraging g μ

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.geometricVolumeNormedAddCommGroup
local instance geometricVolumeNormedSpace_r45cbc0_1 : NormedSpace ℝ Mat3 := Matrix.frobeniusNormedSpace
/-- Ordinary parallel-frame Jacobi data and the polar formula. The matrix
curve is the actual curvature along this same flow, and `RegularJacobi`
contains its ordinary Jacobi equation and initial conditions. -/
structure ParallelJacobiData (g : SmoothMetric M) (μ : Measure (FrameBundle g)) where
  compact : CompactSpace (FrameBundle g)
  flow : FrameFlow g μ
  curvatureContinuous : Continuous (frameCurvatureField g)
  derivativeContinuous : Continuous (frameCurvatureDerivative g)
  derivative : ∀ t e, HasDerivAt (fun r => frameCurvatureField g (flow.map r e))
    (frameCurvatureDerivative g (flow.map t e)) t
  jacobi : (u : ℝ) → FrameBundle g → Jacobi.RegularJacobi (Real.pi * u)
  curvature : ∀ u e r, (jacobi u e).R r = 1 + frameCurvatureField g (flow.map r e)
  densityIntegrable : ∀ u, 0 < u → u < 1 →
    Integrable (fun e => (jacobi u e).truncatedDensity) μ
  firstIntegral : IntervalIntegrable (fun u => ∫ e, (jacobi u e).truncatedDensity ∂μ)
    volume 0 (5 / 8)
  secondIntegral : IntervalIntegrable (fun u => ∫ e, (jacobi u e).truncatedDensity ∂μ)
    volume (5 / 8) 1
  polar : volumeRatio g ≤ (3 * Real.pi / 4) *
    ((∫ u in (0 : ℝ)..(5 / 8), ∫ e, (jacobi u e).truncatedDensity ∂μ) +
      ∫ u in (5 / 8 : ℝ)..1, ∫ e, (jacobi u e).truncatedDensity ∂μ)

end

end PositiveEinsteinFour.Geometry
end


section

/-! A common initial cotangent domain for small velocities and nearby
coordinate frames, including the zero velocity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatRadialCotangentState_continuousAt (g : SmoothMetric M) (c : M)
    (z : HeatRadialFrameSpace) (hz : z.2.1 ∈ (chartAt FourSpace c).target) :
    ContinuousAt (fun w : HeatRadialFrameSpace => heatRadialCotangentState g c w.1 w.2) z := by
  have hG (i j : Fin 4) : ContinuousAt
      (fun w : HeatRadialFrameSpace => metricInChart g c w.2.1 i j) z :=
    ContinuousAt.comp (f := fun w : HeatRadialFrameSpace => w.2.1)
      (g := fun x => metricInChart g c x i j)
      (metricInChart_contDiffAt g c z.2.1 hz i j).continuousAt continuousAt_snd.fst
  apply continuousAt_snd.fst.prodMk
  apply (PiLp.continuous_toLp 2 _).continuousAt.comp
  apply continuousAt_pi.mpr
  intro i
  change ContinuousAt (fun w : HeatRadialFrameSpace => ∑ j : Fin 4,
    metricInChart g c w.2.1 i j * ∑ k : Fin 4, w.2.2 j k * w.1 k) z
  apply tendsto_finsetSum
  intro j _
  apply (hG i j).mul
  apply tendsto_finsetSum
  intro k _
  have hE : Continuous (fun w : HeatRadialFrameSpace => w.2.2 j k) := by fun_prop
  let π : FourSpace →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) k
  have hV : ContinuousAt (fun w : HeatRadialFrameSpace => w.1 k) z :=
    π.continuous.continuousAt.comp
      (f := fun w : HeatRadialFrameSpace => w.1) continuousAt_fst
  exact hE.continuousAt.mul hV

theorem continuous_family_ball (f : HeatRadialFrameSpace → CotangentCoordinates)
    (p : CoordinateFrameSpace) (hf : ContinuousAt f (0, p))
    (R : ℝ) (hR : 0 < R) :
    ∃ r > (0 : ℝ), ∀ v : FourSpace, ‖v‖ < r → ∀ q : CoordinateFrameSpace,
      q ∈ ball p r → f (v, q) ∈ ball (f (0, p)) R := by
  have hn := hf.preimage_mem_nhds (ball_mem_nhds (f (0, p)) hR)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, ?_⟩
  intro v hv q hq
  have hmem : (v, q) ∈ ball ((0 : FourSpace), p) r := by
    change max (dist v 0) (dist q p) < r
    exact max_lt (by simpa only [dist_zero_right] using hv) hq
  exact hball hmem

theorem heatRadialCotangentState_common_domain (g : SmoothMetric M) (c : M)
    (p : CoordinateFrameSpace) (hp : p.1 ∈ (chartAt FourSpace c).target)
    (R : ℝ) (hR : 0 < R) :
    ∃ r > (0 : ℝ), ∀ v : FourSpace, ‖v‖ < r → ∀ q : CoordinateFrameSpace,
      q ∈ ball p r → heatRadialCotangentState g c v q ∈ ball (p.1, (0 : FourSpace)) R := by
  have h0 : heatRadialCotangentState g c (0 : FourSpace) p = (p.1, 0) := by
    simp only [heatRadialCotangentState, WithLp.ofLp_zero, Matrix.mulVec_zero, WithLp.toLp_zero]
  obtain ⟨r, hr, hball⟩ := continuous_family_ball
    (fun z => heatRadialCotangentState g c z.1 z.2) p
    (heatRadialCotangentState_continuousAt g c (0, p) hp) R hR
  refine ⟨r, hr, ?_⟩
  intro v hv q hq
  have h := hball v hv q hq
  simpa only [h0] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common radial-frame flow for nearby centers and nearby initial frames.
This retains joint finite regularity instead of choosing a new flow at each center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M} {p : CoordinateFrameSpace}

def heatRadialFrameFamily (F : HeatRadialFrameFlow g c p) (t : ℝ)
    (q : HeatRadialFrameSpace) : CoordinateFrameSpace :=
  (F.map ((t⁻¹ • q.1, q.2), t)).2

theorem HeatRadialFrameFlow.stationary_at (F : HeatRadialFrameFlow g c p)
    (q : CoordinateFrameSpace) (hq : ((0 : FourSpace), q) ∈ closedBall (0, p) F.radius)
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) : F.map ((0, q), t) = (0, q) := by
  have hd (s : ℝ) (hs : s ∈ Ioo (-F.time) F.time) :
      HasDerivAt (fun r => F.map ((0, q), r)) 0 s := by
    have h := F.derivative (0, q) hq s hs
    have he : F.map ((0, q), s) = (0, (F.map ((0, q), s)).2) :=
      Prod.ext (F.direction (0, q) hq s hs) rfl
    rw [he, heatRadialFrameField_zero_direction] at h
    exact h
  have hz : (0 : ℝ) ∈ Ioo (-F.time) F.time := ⟨by linarith [F.time_pos], F.time_pos⟩
  have h := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo _ _).isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) ht hz
  simpa only [F.initial (0, q) hq] using h

theorem HeatRadialFrameFlow.exists_joint_frame_family (F : HeatRadialFrameFlow g c p) :
    ∃ t > (0 : ℝ), t ∈ Ioo (-F.time) F.time ∧ ∃ r > (0 : ℝ),
      ∀ q ∈ ball (0, p) r,
        ContDiffAt ℝ 12 (heatRadialFrameFamily F t) q ∧
        (t⁻¹ • q.1, q.2) ∈ closedBall (0, p) F.radius ∧
        (heatRadialFrameFamily F t q).1 ∈ (chartAt FourSpace c).target ∧
        (heatRadialFrameFamily F t q).2ᵀ *
            metricInChart g c (heatRadialFrameFamily F t q).1 * (heatRadialFrameFamily F t q).2 =
          q.2.2ᵀ * metricInChart g c q.2.1 * q.2.2 := by
  obtain ⟨t, ht, htI, hFt⟩ := F.exists_pos_slice 12
  norm_num at hFt
  let A : HeatRadialFrameSpace → HeatRadialFrameSpace := fun q => (t⁻¹ • q.1, q.2)
  have hA : ContDiff ℝ 12 A := ((contDiff_const (c := t⁻¹)).smul contDiff_fst).prodMk contDiff_snd
  have hA0 : A (0, p) = (0, p) := by simp [A]
  have hreg : ContDiffAt ℝ 12 (heatRadialFrameFamily F t) (0, p) := by
    have hh : ContDiffAt ℝ 12 (fun q => F.map (q, t)) (A (0, p)) := by simpa only [hA0] using hFt
    exact (hh.comp (0, p) hA.contDiffAt).snd
  have hn : ∀ᶠ q in 𝓝 ((0 : FourSpace), p),
      ContDiffAt ℝ 12 (heatRadialFrameFamily F t) q ∧ A q ∈ ball (0, p) F.radius := by
    apply (hreg.eventually (by norm_num)).and
    apply hA.continuous.continuousAt.preimage_mem_nhds
    rw [hA0]
    exact ball_mem_nhds (0, p) F.radius_pos
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨t, ht, htI, r, hr, fun q hq => ?_⟩
  obtain ⟨hqreg, hqa⟩ := hball (by simpa only [mem_ball] using hq)
  have hqa' : A q ∈ closedBall (0, p) F.radius := ball_subset_closedBall hqa
  exact ⟨hqreg, hqa', F.in_chart (A q) hqa' t htI, F.gram (A q) hqa' t htI⟩

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Multiplication by a genuine orthonormal frame cancels exactly the
coordinate metric density. -/
theorem jacobiBlockMatrix_metric_density (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (A : Mat4) :
    chartVolumeDensity g c (chartAt FourSpace c e.base) *
      |(frameChartMatrix g c e * A).det| = |A.det| := by
  rw [Matrix.det_mul, abs_mul, ← mul_assoc,
    chartVolumeDensity_mul_frame_det g c (chartAt FourSpace c e.base)
      ((chartAt FourSpace c).map_source he) (frameChartMatrix g c e)
      (frameChartMatrix_normalizes g c e he), one_mul]

theorem jacobiBlockMatrix_scaled_metric_density (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (t : ℝ) (J : Matrix (Fin 3) (Fin 3) ℝ) :
    chartVolumeDensity g c (chartAt FourSpace c e.base) *
      |(frameChartMatrix g c e * jacobiBlockMatrix 1 (t⁻¹ • J)).det| =
        |J.det / t ^ 3| := by
  rw [jacobiBlockMatrix_metric_density g c e he, jacobiBlockMatrix_scaled_det]

theorem jacobiBlockMatrix_scaled_linear_density (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (t : ℝ) (J : Matrix (Fin 3) (Fin 3) ℝ) :
    chartVolumeDensity g c (chartAt FourSpace c e.base) *
      |LinearMap.det (Matrix.toEuclideanLin
        (frameChartMatrix g c e * jacobiBlockMatrix 1 (t⁻¹ • J)))| =
        |J.det / t ^ 3| := by
  rw [LinearMap.det_toLpLin 2]
  exact jacobiBlockMatrix_scaled_metric_density g c e he t J

end
end PositiveEinsteinFour.Geometry
end


section

/-! The same local flow remains a smooth radial-frame flow when its
initial frame is moved inside the original neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M} {p : CoordinateFrameSpace}

theorem HeatRadialFrameFlow.regular_at (F : HeatRadialFrameFlow g c p)
    (n : ℕ) (q : HeatRadialFrameSpace) (hq : q ∈ ball (0, p) F.radius) :
    ContDiffAt ℝ n F.map (q, 0) := by
  have hqc : q ∈ closedBall (0, p) F.radius := ball_subset_closedBall hq
  have ht0 : (0 : ℝ) ∈ Ioo (-F.time) F.time := ⟨by linarith [F.time_pos], F.time_pos⟩
  have hp : q.2.1 ∈ (chartAt FourSpace c).target := by
    simpa only [F.initial q hqc] using F.in_chart q hqc 0 ht0
  have hf := heatRadialFrameField_contDiffAt g c q hp
  have hball : closedBall (0, p) F.radius ∈ 𝓝 q :=
    mem_of_superset (isOpen_ball.mem_nhds hq) ball_subset_closedBall
  have hdom : closedBall (0, p) F.radius ×ˢ Ioo (-F.time) F.time ∈ 𝓝 (q, (0 : ℝ)) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod hball (isOpen_Ioo.mem_nhds ht0)
  have hi : ∀ᶠ z in 𝓝 q, F.map (z, 0) = z := by
    filter_upwards [hball] with z hz
    exact F.initial z hz
  have hs : ∀ᶠ z in 𝓝 (q, (0 : ℝ)),
      HasDerivAt (fun s => F.map (z.1, s)) (heatRadialFrameField g c (F.map z)) z.2 := by
    filter_upwards [hdom] with z hz
    exact F.derivative z.1 hz.1 z.2 hz.2
  exact FlowCalculus.local_flow_contDiffAt_finite n HeatRadialFrameSpace
    (heatRadialFrameField g c) F.map q (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (contDiffAt_zero.mpr ⟨_, hdom, F.continuous⟩) hi hs

def HeatRadialFrameFlow.recenter (F : HeatRadialFrameFlow g c p)
    (q : CoordinateFrameSpace) (hq : ((0 : FourSpace), q) ∈ ball (0, p) F.radius) :
    HeatRadialFrameFlow g c q := by
  let r := (F.radius - dist ((0 : FourSpace), q) (0, p)) / 2
  have hr : 0 < r := by dsimp [r]; exact half_pos (sub_pos.mpr hq)
  have hsub : closedBall ((0 : FourSpace), q) r ⊆ closedBall (0, p) F.radius :=
    closedBall_subset_closedBall' (by dsimp [r]; linarith [show dist ((0 : FourSpace), q) (0, p) < F.radius from hq])
  exact {
    radius := r
    radius_pos := hr
    time := F.time
    time_pos := F.time_pos
    map := F.map
    continuous := F.continuous.mono (fun z hz => ⟨hsub hz.1, hz.2⟩)
    initial := fun z hz => F.initial z (hsub hz)
    in_chart := fun z hz t ht => F.in_chart z (hsub hz) t ht
    derivative := fun z hz t ht => F.derivative z (hsub hz) t ht
    regular := fun n => F.regular_at n (0, q) hq }

end
end PositiveEinsteinFour.Geometry
end


section

/-! Jacobi fields and polar integration for the parallel-frame flow. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

structure JacobiRealizationData (d : MetricGreenData g μ) where
  jacobi : (u : ℝ) → FrameBundle g → Jacobi.RegularJacobi (Real.pi * u)
  curvature : ∀ u e r, (jacobi u e).R r = 1 + frameCurvatureField g ((d.flow 0).map r e)
  densityIntegrable : ∀ u, 0 < u → u < 1 →
    Integrable (fun e => (jacobi u e).truncatedDensity) μ
  firstIntegral : IntervalIntegrable (fun u => ∫ e, (jacobi u e).truncatedDensity ∂μ)
    volume 0 (5 / 8)
  secondIntegral : IntervalIntegrable (fun u => ∫ e, (jacobi u e).truncatedDensity ∂μ)
    volume (5 / 8) 1
  polar : volumeRatio g ≤ (3 * Real.pi / 4) *
    ((∫ u in (0 : ℝ)..(5 / 8), ∫ e, (jacobi u e).truncatedDensity ∂μ) +
      ∫ u in (5 / 8 : ℝ)..1, ∫ e, (jacobi u e).truncatedDensity ∂μ)

def JacobiRealizationData.toParallelJacobiData [CompactSpace M] {d : MetricGreenData g μ}
    (j : JacobiRealizationData d) (o : OppositeWeylData d) (hRic : RicciThree g) :
    ParallelJacobiData g μ where
  compact := actual_compactFrameBundle g
  flow := d.flow 0
  curvatureContinuous := d.continuousCurvatureField o hRic
  derivativeContinuous := d.continuousCurvatureDerivative o
  derivative := d.derivativeCurvatureField o hRic
  jacobi := j.jacobi
  curvature := j.curvature
  densityIntegrable := j.densityIntegrable
  firstIntegral := j.firstIntegral
  secondIntegral := j.secondIntegral
  polar := j.polar

end
end PositiveEinsteinFour.Geometry
end


section

/-! The explicit energy densities inherit continuity from the raw coordinate
jets.  In particular the endpoint-corrected variation satisfies all three
continuity hypotheses of the interval differentiation theorem. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set
open scoped _root_.Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metricPartial_contDiffAt (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (i j k : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => matrixPartial (metricInChart g c) i w j k) z := by
  exact ((metricInChart_contDiffAt g c z hz j k).fderiv_right (m := ∞)
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffAt_const

theorem metricSecondPartial_contDiffAt (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (i j k l : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => matrixPartial (matrixPartial (metricInChart g c) j) i w k l) z := by
  exact ((metricPartial_contDiffAt g c z hz j k l).fderiv_right (m := ∞)
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffAt_const

variable {P : Type*} [TopologicalSpace P] {S : Set P}

theorem continuousOn_chartMatrix (A : FourSpace → Mat4)
    (x : P → FourSpace) (hx : ContinuousOn x S)
    (hA : ∀ p ∈ S, ∀ i j, ContinuousAt (fun z => A z i j) (x p)) :
    ContinuousOn (fun p => A (x p)) S := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j p hp
  exact (hA p hp i j).comp_continuousWithinAt (hx p hp)

theorem continuousOn_jacobiMetricFirstDirectional (g : SmoothMetric M) (c : M)
    (x : P → FourSpace) (y : P → JacobiCoordinateVector)
    (hx : ContinuousOn x S) (hy : ContinuousOn y S)
    (hz : ∀ p ∈ S, x p ∈ (chartAt FourSpace c).target) :
    ContinuousOn (fun p => jacobiMetricFirstDirectional g c (x p) (y p)) S := by
  unfold jacobiMetricFirstDirectional
  apply continuousOn_finsetSum
  intro i _
  apply (continuousOn_pi.mp hy i).smul
  exact continuousOn_chartMatrix (matrixPartial (metricInChart g c) i) x hx
    (fun p hp j k => (metricPartial_contDiffAt g c (x p) (hz p hp) i j k).continuousAt)

theorem continuousOn_jacobiMetricSecondDirectional (g : SmoothMetric M) (c : M)
    (x : P → FourSpace) (y : P → JacobiCoordinateVector)
    (hx : ContinuousOn x S) (hy : ContinuousOn y S)
    (hz : ∀ p ∈ S, x p ∈ (chartAt FourSpace c).target) :
    ContinuousOn (fun p => jacobiMetricSecondDirectional g c (x p) (y p)) S := by
  unfold jacobiMetricSecondDirectional
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  apply ((continuousOn_pi.mp hy i).mul (continuousOn_pi.mp hy j)).smul
  exact continuousOn_chartMatrix (matrixPartial (matrixPartial (metricInChart g c) j) i) x hx
    (fun p hp k l => (metricSecondPartial_contDiffAt g c (x p) (hz p hp) i j k l).continuousAt)

theorem continuousOn_actualMetric (g : SmoothMetric M) (c : M)
    (x : P → FourSpace) (hx : ContinuousOn x S)
    (hz : ∀ p ∈ S, x p ∈ (chartAt FourSpace c).target) :
    ContinuousOn (fun p => metricInChart g c (x p)) S :=
  continuousOn_chartMatrix (metricInChart g c) x hx
    (fun p hp i j => (metricInChart_contDiffAt g c (x p) (hz p hp) i j).continuousAt)

theorem continuousOn_chartEnergyDensity (g : SmoothMetric M) (c : M)
    (x : P → FourSpace) (v : P → JacobiCoordinateVector)
    (hx : ContinuousOn x S) (hv : ContinuousOn v S)
    (hz : ∀ p ∈ S, x p ∈ (chartAt FourSpace c).target) :
    ContinuousOn (fun p => chartEnergyDensity g c (x p) (v p)) S :=
  (continuousOn_metricPair (continuousOn_actualMetric g c x hx hz) hv hv).const_mul _

theorem continuousOn_chartEnergyFirstDensity (g : SmoothMetric M) (c : M)
    (x : P → FourSpace) (y v w : P → JacobiCoordinateVector)
    (hx : ContinuousOn x S) (hy : ContinuousOn y S) (hv : ContinuousOn v S)
    (hw : ContinuousOn w S) (hz : ∀ p ∈ S, x p ∈ (chartAt FourSpace c).target) :
    ContinuousOn (fun p => chartEnergyFirstDensity g c (x p) (y p) (v p) (w p)) S := by
  exact ((continuousOn_metricPair (continuousOn_jacobiMetricFirstDirectional g c x y hx hy hz)
    hv hv).const_mul _).add
      (continuousOn_metricPair (continuousOn_actualMetric g c x hx hz) hv hw)

theorem continuousOn_chartEnergySecondDensity (g : SmoothMetric M) (c : M)
    (x : P → FourSpace) (y v w u q : P → JacobiCoordinateVector)
    (hx : ContinuousOn x S) (hy : ContinuousOn y S) (hv : ContinuousOn v S)
    (hw : ContinuousOn w S) (hu : ContinuousOn u S) (hq : ContinuousOn q S)
    (hz : ∀ p ∈ S, x p ∈ (chartAt FourSpace c).target) :
    ContinuousOn (fun p => chartEnergySecondDensity g c (x p)
      (y p) (v p) (w p) (u p) (q p)) S := by
  have hG := continuousOn_actualMetric g c x hx hz
  have hH := continuousOn_jacobiMetricFirstDirectional g c x y hx hy hz
  have hK := continuousOn_jacobiMetricSecondDirectional g c x y hx hy hz
  have hU := continuousOn_jacobiMetricFirstDirectional g c x u hx hu hz
  exact ((((continuousOn_metricPair hG hw hw).add
    ((continuousOn_metricPair hH hw hv).const_mul _)).add
    ((continuousOn_metricPair hK hv hv).const_mul _)).add
    ((continuousOn_metricPair hU hv hv).const_mul _)).add
    (continuousOn_metricPair hG hv hq)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Endpoint curves are affine in a common chart.  In any overlapping chart,
their first and second jets are the actual derivatives of the chart change.
Restriction followed by constant extension gives globally continuous jet
functions without requiring a chart change to be regular outside its overlap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped _root_.Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem endpointChartPosition_symm (c d : M) (z : FourSpace)
    (y : JacobiCoordinateVector) (s : ℝ)
    (hd : (chartAt FourSpace c).symm (endpointChartLine z y s) ∈
      (chartAt FourSpace d).source) :
    (chartAt FourSpace d).symm (endpointChartPosition c d z y s) =
      (chartAt FourSpace c).symm (endpointChartLine z y s) :=
  (chartAt FourSpace d).left_inv hd

variable [IsManifold I4 ∞ M]

theorem endpointChartLine_hasDerivAt (z : FourSpace) (y : JacobiCoordinateVector) (s : ℝ) :
    HasDerivAt (endpointChartLine z y) (WithLp.toLp 2 y) s := by
  simpa only [endpointChartLine, one_smul, Pi.add_apply, Pi.smul_apply, id_eq] using!
    ((hasDerivAt_id s).smul_const (WithLp.toLp 2 y)).const_add z

theorem continuous_endpointChartLine (z : FourSpace) (y : JacobiCoordinateVector) :
    Continuous (endpointChartLine z y) := by
  unfold endpointChartLine
  fun_prop

theorem endpointChartPosition_hasDerivAt (c d : M) (z : FourSpace)
    (y : JacobiCoordinateVector) (s : ℝ)
    (hz : endpointChartLine z y s ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm (endpointChartLine z y s) ∈
      (chartAt FourSpace d).source) :
    HasDerivAt (endpointChartPosition c d z y) (endpointChartFirst c d z y s) s :=
  chartTransition_hasDerivAt c d (endpointChartLine z y) y s hz hd
    (endpointChartLine_hasDerivAt z y s)

theorem endpointChartFirst_hasDerivAt (c d : M) (z : FourSpace)
    (y : JacobiCoordinateVector) (s : ℝ)
    (hz : endpointChartLine z y s ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm (endpointChartLine z y s) ∈
      (chartAt FourSpace d).source) :
    HasDerivAt (endpointChartFirst c d z y) (endpointChartSecond c d z y s) s := by
  have h := chartTransition_secondJet_hasDerivAt c d (endpointChartLine z y)
    (fun _ => y) 0 s hz hd (endpointChartLine_hasDerivAt z y s) (hasDerivAt_const s y)
  have hmap := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap
    |>.hasFDerivAt.comp_hasDerivAt s h
  simpa only [endpointChartFirst, endpointChartSecond, chartTransitionSecondJet,
    Matrix.mulVec_zero, zero_add, Function.comp_def] using! hmap

theorem continuousAt_transitionFirst (c d : M) (z : FourSpace)
    (y : JacobiCoordinateVector) (hz : z ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    ContinuousAt (fun q => chartTransitionMatrix c d q *ᵥ y) z := by
  apply continuousAt_pi.mpr
  intro i
  unfold Matrix.mulVec dotProduct
  apply tendsto_finsetSum
  intro j _
  exact (chartTransitionMatrix_contDiffAt c d z hz hd i j).continuousAt.mul continuousAt_const

theorem continuousAt_transitionSecond (c d : M) (z : FourSpace)
    (y : JacobiCoordinateVector) (hz : z ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    ContinuousAt (fun q => chartTransitionSecondVector c d q y) z := by
  apply continuousAt_pi.mpr
  intro i
  simp only [chartTransitionSecondVector, jacobiConnection, Matrix.mulVec, dotProduct,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply tendsto_finsetSum
  intro j _
  apply ContinuousAt.mul _ continuousAt_const
  apply tendsto_finsetSum
  intro k _
  apply continuousAt_const.mul
  exact (((chartTransitionMatrix_contDiffAt c d z hz hd i j).fderiv_right
    (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (g := fun _ => coordinateVector k) contDiffAt_const).continuousAt

theorem endpointChartJets_continuousAt (c d : M) (z : FourSpace)
    (y : JacobiCoordinateVector) (s : ℝ)
    (hz : endpointChartLine z y s ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm (endpointChartLine z y s) ∈
      (chartAt FourSpace d).source) :
    ContinuousAt (endpointChartPosition c d z y) s ∧
      ContinuousAt (endpointChartFirst c d z y) s ∧
      ContinuousAt (endpointChartSecond c d z y) s := by
  have ht : Continuous (WithLp.toLp 2 : JacobiCoordinateVector → FourSpace) :=
    PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)
  have hline := (continuous_endpointChartLine z y).continuousAt (x := s)
  refine ⟨(endpointChartPosition_hasDerivAt c d z y s hz hd).continuousAt, ?_, ?_⟩
  · exact ht.continuousAt.comp ((continuousAt_transitionFirst c d _ y hz hd).comp hline)
  · exact ht.continuousAt.comp ((continuousAt_transitionSecond c d _ y hz hd).comp hline)

omit [IsManifold I4 ∞ M] in
theorem exists_endpointChartOverlap (c d : M) (z : FourSpace)
    (y : JacobiCoordinateVector) (hz : z ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    ∃ δ > 0, ∀ s ∈ Icc (-δ) δ,
      endpointChartLine z y s ∈ (chartAt FourSpace c).target ∧
      (chartAt FourSpace c).symm (endpointChartLine z y s) ∈ (chartAt FourSpace d).source := by
  have hline := (continuous_endpointChartLine z y).continuousAt (x := 0)
  have hz0 : endpointChartLine z y 0 ∈ (chartAt FourSpace c).target := by
    simpa only [endpointChartLine, zero_smul, add_zero] using hz
  have hs : ContinuousAt (chartAt FourSpace c).symm (endpointChartLine z y 0) :=
    (chartAt FourSpace c).continuousOn_symm.continuousAt
      ((chartAt FourSpace c).open_target.mem_nhds hz0)
  have hd0 : (chartAt FourSpace c).symm (endpointChartLine z y 0) ∈
      (chartAt FourSpace d).source := by
    simpa only [endpointChartLine, zero_smul, add_zero] using hd
  have hnear := (hline.eventually ((chartAt FourSpace c).open_target.mem_nhds hz0)).and
    ((hs.comp hline).eventually ((chartAt FourSpace d).open_source.mem_nhds hd0))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro s hs
  apply hball
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  rw [abs_lt]
  constructor <;> linarith [hs.1, hs.2]

/-- Three globally continuous endpoint-jet functions agree with the actual
chart transition on a common interval and have its genuine first and second
parameter derivatives in the interior. -/
theorem exists_endpointChartJets (c d : M) (z : FourSpace)
    (y : JacobiCoordinateVector) (hz : z ∈ (chartAt FourSpace c).target)
    (hd : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    ∃ δ > 0, ∃ A A' A'' : ℝ → FourSpace,
      Continuous A ∧ Continuous A' ∧ Continuous A'' ∧
      (∀ s ∈ Ioo (-δ) δ, HasDerivAt A (A' s) s ∧ HasDerivAt A' (A'' s) s) ∧
      (∀ s ∈ Icc (-δ) δ,
        A s = endpointChartPosition c d z y s ∧
        A' s = endpointChartFirst c d z y s ∧ A'' s = endpointChartSecond c d z y s) ∧
      (∀ s ∈ Icc (-δ) δ,
        endpointChartLine z y s ∈ (chartAt FourSpace c).target ∧
        (chartAt FourSpace c).symm (endpointChartLine z y s) ∈ (chartAt FourSpace d).source) := by
  obtain ⟨δ, hδ, hoverlap⟩ := exists_endpointChartOverlap c d z y hz hd
  have hab : -δ ≤ δ := by linarith
  let A := IccExtend hab (fun s : Icc (-δ) δ => endpointChartPosition c d z y s)
  let A' := IccExtend hab (fun s : Icc (-δ) δ => endpointChartFirst c d z y s)
  let A'' := IccExtend hab (fun s : Icc (-δ) δ => endpointChartSecond c d z y s)
  have hP : ContinuousOn (endpointChartPosition c d z y) (Icc (-δ) δ) := by
    intro s hs
    exact (endpointChartJets_continuousAt c d z y s
      (hoverlap s hs).1 (hoverlap s hs).2).1.continuousWithinAt
  have hF : ContinuousOn (endpointChartFirst c d z y) (Icc (-δ) δ) := by
    intro s hs
    exact (endpointChartJets_continuousAt c d z y s
      (hoverlap s hs).1 (hoverlap s hs).2).2.1.continuousWithinAt
  have hS : ContinuousOn (endpointChartSecond c d z y) (Icc (-δ) δ) := by
    intro s hs
    exact (endpointChartJets_continuousAt c d z y s
      (hoverlap s hs).1 (hoverlap s hs).2).2.2.continuousWithinAt
  have heq (s : ℝ) (hs : s ∈ Icc (-δ) δ) :
      A s = endpointChartPosition c d z y s ∧
      A' s = endpointChartFirst c d z y s ∧ A'' s = endpointChartSecond c d z y s :=
    ⟨IccExtend_of_mem hab _ hs, IccExtend_of_mem hab _ hs, IccExtend_of_mem hab _ hs⟩
  refine ⟨δ, hδ, A, A', A'', hP.domRestrict.Icc_extend',
    hF.domRestrict.Icc_extend', hS.domRestrict.Icc_extend', ?_, heq, hoverlap⟩
  intro s hs
  have hsc : s ∈ Icc (-δ) δ := ⟨hs.1.le, hs.2.le⟩
  rw [(heq s hsc).2.1, (heq s hsc).2.2]
  exact ⟨intervalExtension_hasDerivAt _ hab hs
      (endpointChartPosition_hasDerivAt c d z y s (hoverlap s hsc).1 (hoverlap s hsc).2),
    intervalExtension_hasDerivAt _ hab hs
      (endpointChartFirst_hasDerivAt c d z y s (hoverlap s hsc).1 (hoverlap s hsc).2)⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The chart fields need be continuous only on the compact time segment.
No extension of a coordinate field past its chart is needed to differentiate
the endpoint-corrected energy integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set
open scoped _root_.Topology Manifold ContDiff BigOperators

noncomputable section

theorem continuousOn_timeField (f : ℝ → FourSpace) {a b δ : ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    ContinuousOn (fun p : ℝ × ℝ => f p.2) (Icc (-δ) δ ×ˢ Icc a b) :=
  hf.comp continuous_snd.continuousOn (fun _ hp => hp.2)

theorem continuousOn_parameterField (f : ℝ → FourSpace) {a b δ : ℝ}
    (hf : ContinuousOn f (Icc (-δ) δ)) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1) (Icc (-δ) δ ×ˢ Icc a b) :=
  hf.comp continuous_fst.continuousOn (fun _ hp => hp.1)

theorem endpointCorrected_jets_continuousOn (x y v w A B A' B' A'' B'' : ℝ → FourSpace)
    {a b δ : ℝ}
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hA : ContinuousOn A (Icc (-δ) δ)) (hB : ContinuousOn B (Icc (-δ) δ))
    (hA' : ContinuousOn A' (Icc (-δ) δ)) (hB' : ContinuousOn B' (Icc (-δ) δ))
    (hA'' : ContinuousOn A'' (Icc (-δ) δ)) (hB'' : ContinuousOn B'' (Icc (-δ) δ)) :
    let S := Icc (-δ) δ ×ˢ Icc a b
    ContinuousOn (fun p => endpointCorrectedPosition x y A B a b p.1 p.2) S ∧
    ContinuousOn (fun p => endpointCorrectedParameter y A' B' a b p.1 p.2) S ∧
    ContinuousOn (fun p => endpointCorrectedVelocity x y v w A B a b p.1 p.2) S ∧
    ContinuousOn (fun p => endpointCorrectedMixed y w A' B' a b p.1 p.2) S ∧
    ContinuousOn (fun p => endpointCorrectedSecond A'' B'' a b p.1 p.2) S ∧
    ContinuousOn (fun p => endpointCorrectedMixedSecond A'' B'' a b p.1) S := by
  dsimp only
  have hxT := continuousOn_timeField (δ := δ) x hx
  have hyT := continuousOn_timeField (δ := δ) y hy
  have hvT := continuousOn_timeField (δ := δ) v hv
  have hwT := continuousOn_timeField (δ := δ) w hw
  have hAP := continuousOn_parameterField (a := a) (b := b) A hA
  have hBP := continuousOn_parameterField (a := a) (b := b) B hB
  have hA'P := continuousOn_parameterField (a := a) (b := b) A' hA'
  have hB'P := continuousOn_parameterField (a := a) (b := b) B' hB'
  have hA''P := continuousOn_parameterField (a := a) (b := b) A'' hA''
  have hB''P := continuousOn_parameterField (a := a) (b := b) B'' hB''
  have hε : ContinuousOn (fun p : ℝ × ℝ => p.1) (Icc (-δ) δ ×ˢ Icc a b) :=
    continuous_fst.continuousOn
  have hL : ContinuousOn (fun p : ℝ × ℝ => endpointWeightLeft a b p.2)
      (Icc (-δ) δ ×ˢ Icc a b) :=
    ((continuous_const.sub continuous_snd).div_const (b - a)).continuousOn
  have hR : ContinuousOn (fun p : ℝ × ℝ => endpointWeightRight a b p.2)
      (Icc (-δ) δ ×ˢ Icc a b) :=
    ((continuous_snd.sub continuous_const).div_const (b - a)).continuousOn
  have hRA : ContinuousOn (fun p : ℝ × ℝ => endpointResidual A (x a) (y a) p.1)
      (Icc (-δ) δ ×ˢ Icc a b) :=
    (hAP.sub continuousOn_const).sub (hε.smul continuousOn_const)
  have hRB : ContinuousOn (fun p : ℝ × ℝ => endpointResidual B (x b) (y b) p.1)
      (Icc (-δ) δ ×ˢ Icc a b) :=
    (hBP.sub continuousOn_const).sub (hε.smul continuousOn_const)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((hxT.add (hε.smul hyT)).add (hL.smul hRA)).add (hR.smul hRB)
  · exact (hyT.add (hL.smul (hA'P.sub continuousOn_const))).add
      (hR.smul (hB'P.sub continuousOn_const))
  · exact ((hvT.add (hε.smul hwT)).sub (hRA.const_smul (b - a)⁻¹)).add
      (hRB.const_smul (b - a)⁻¹)
  · exact (hwT.sub ((hA'P.sub continuousOn_const).const_smul (b - a)⁻¹)).add
      ((hB'P.sub continuousOn_const).const_smul (b - a)⁻¹)
  · exact (hL.smul hA''P).add (hR.smul hB''P)
  · exact (hA''P.const_smul (-(b - a)⁻¹)).add (hB''P.const_smul (b - a)⁻¹)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem endpointCorrected_energy_continuousOnSegment (g : SmoothMetric M) (c : M)
    (x y v w A B A' B' A'' B'' : ℝ → FourSpace) {a b δ : ℝ}
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hA : ContinuousOn A (Icc (-δ) δ)) (hB : ContinuousOn B (Icc (-δ) δ))
    (hA' : ContinuousOn A' (Icc (-δ) δ)) (hB' : ContinuousOn B' (Icc (-δ) δ))
    (hA'' : ContinuousOn A'' (Icc (-δ) δ)) (hB'' : ContinuousOn B'' (Icc (-δ) δ))
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      endpointCorrectedPosition x y A B a b ε t ∈ (chartAt FourSpace c).target) :
    let X := fun p : ℝ × ℝ => endpointCorrectedPosition x y A B a b p.1 p.2
    let Y := fun p : ℝ × ℝ => WithLp.ofLp (endpointCorrectedParameter y A' B' a b p.1 p.2)
    let V := fun p : ℝ × ℝ => WithLp.ofLp (endpointCorrectedVelocity x y v w A B a b p.1 p.2)
    let W := fun p : ℝ × ℝ => WithLp.ofLp (endpointCorrectedMixed y w A' B' a b p.1 p.2)
    let U := fun p : ℝ × ℝ => WithLp.ofLp (endpointCorrectedSecond A'' B'' a b p.1 p.2)
    let Q := fun p : ℝ × ℝ => WithLp.ofLp (endpointCorrectedMixedSecond A'' B'' a b p.1)
    ContinuousOn (fun p => chartEnergyDensity g c (X p) (V p)) (Icc (-δ) δ ×ˢ Icc a b) ∧
      ContinuousOn (fun p => chartEnergyFirstDensity g c (X p) (Y p) (V p) (W p))
        (Icc (-δ) δ ×ˢ Icc a b) ∧
      ContinuousOn (fun p => chartEnergySecondDensity g c (X p)
        (Y p) (V p) (W p) (U p) (Q p)) (Icc (-δ) δ ×ˢ Icc a b) := by
  dsimp only
  obtain ⟨hX, hY, hV, hW, hU, hQ⟩ := endpointCorrected_jets_continuousOn
    x y v w A B A' B' A'' B'' hx hy hv hw hA hB hA' hB' hA'' hB''
  have hof : Continuous (WithLp.ofLp : FourSpace → JacobiCoordinateVector) :=
    PiLp.continuous_ofLp 2 (fun _ : Fin 4 => ℝ)
  have hY' := hof.comp_continuousOn hY
  have hV' := hof.comp_continuousOn hV
  have hW' := hof.comp_continuousOn hW
  have hU' := hof.comp_continuousOn hU
  have hQ' := hof.comp_continuousOn hQ
  have htarget : ∀ p ∈ Icc (-δ) δ ×ˢ Icc a b,
      endpointCorrectedPosition x y A B a b p.1 p.2 ∈ (chartAt FourSpace c).target :=
    fun p hp => hz p.1 hp.1 p.2 hp.2
  exact ⟨continuousOn_chartEnergyDensity g c _ _ hX hV' htarget,
    continuousOn_chartEnergyFirstDensity g c _ _ _ _ hX hY' hV' hW' htarget,
    continuousOn_chartEnergySecondDensity g c _ _ _ _ _ _ hX hY' hV' hW' hU' hQ' htarget⟩

theorem hasDerivAt_coordinateVector {f : ℝ → FourSpace} {v : FourSpace} {t : ℝ}
    (h : HasDerivAt f v t) :
    HasDerivAt (fun s => WithLp.ofLp (f s)) (WithLp.ofLp v) t :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt t h

theorem endpointCorrected_energy_secondDerivOnSegment (g : SmoothMetric M) (c : M)
    (x y v w A B A' B' A'' B'' : ℝ → FourSpace) {a b δ : ℝ}
    (hδ : 0 < δ) (hab : a ≤ b)
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hA : ContinuousOn A (Icc (-δ) δ)) (hB : ContinuousOn B (Icc (-δ) δ))
    (hA' : ContinuousOn A' (Icc (-δ) δ)) (hB' : ContinuousOn B' (Icc (-δ) δ))
    (hA'' : ContinuousOn A'' (Icc (-δ) δ)) (hB'' : ContinuousOn B'' (Icc (-δ) δ))
    (hdA : ∀ ε ∈ Ioo (-δ) δ, HasDerivAt A (A' ε) ε)
    (hdB : ∀ ε ∈ Ioo (-δ) δ, HasDerivAt B (B' ε) ε)
    (hddA : ∀ ε ∈ Ioo (-δ) δ, HasDerivAt A' (A'' ε) ε)
    (hddB : ∀ ε ∈ Ioo (-δ) δ, HasDerivAt B' (B'' ε) ε)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      endpointCorrectedPosition x y A B a b ε t ∈ (chartAt FourSpace c).target) :
    let X := endpointCorrectedPosition x y A B a b
    let Y := fun ε t => WithLp.ofLp (endpointCorrectedParameter y A' B' a b ε t)
    let V := fun ε t => WithLp.ofLp (endpointCorrectedVelocity x y v w A B a b ε t)
    let W := fun ε t => WithLp.ofLp (endpointCorrectedMixed y w A' B' a b ε t)
    let U := fun ε t => WithLp.ofLp (endpointCorrectedSecond A'' B'' a b ε t)
    let Q := fun ε (_ : ℝ) => WithLp.ofLp (endpointCorrectedMixedSecond A'' B'' a b ε)
    HasDerivAt (deriv (fun ε => ∫ t in a..b, chartEnergyDensity g c (X ε t) (V ε t)))
      (∫ t in a..b, chartEnergySecondDensity g c (X 0 t)
        (Y 0 t) (V 0 t) (W 0 t) (U 0 t) (Q 0 t)) 0 := by
  dsimp only
  have hc := endpointCorrected_energy_continuousOnSegment g c x y v w A B A' B' A'' B''
    hx hy hv hw hA hB hA' hB' hA'' hB'' hz
  apply chartEnergyIntegral_secondDeriv g c
    (endpointCorrectedPosition x y A B a b)
    (fun ε t => WithLp.ofLp (endpointCorrectedParameter y A' B' a b ε t))
    (fun ε t => WithLp.ofLp (endpointCorrectedVelocity x y v w A B a b ε t))
    (fun ε t => WithLp.ofLp (endpointCorrectedMixed y w A' B' a b ε t))
    (fun ε t => WithLp.ofLp (endpointCorrectedSecond A'' B'' a b ε t))
    (fun ε (_ : ℝ) => WithLp.ofLp (endpointCorrectedMixedSecond A'' B'' a b ε))
    hδ hab hz
  · intro ε hε t _
    simpa only [WithLp.toLp_ofLp] using
      endpointCorrectedPosition_parameter x y A B A' B' a b ε t (hdA ε hε) (hdB ε hε)
  · intro ε hε t _
    exact hasDerivAt_coordinateVector
      (endpointCorrectedParameter_parameter y A' B' A'' B'' a b ε t
        (hddA ε hε) (hddB ε hε))
  · intro ε hε t _
    exact hasDerivAt_coordinateVector
      (endpointCorrectedVelocity_parameter x y v w A B A' B' a b ε t
        (hdA ε hε) (hdB ε hε))
  · intro ε hε t _
    exact hasDerivAt_coordinateVector
      (endpointCorrectedMixed_parameter y w A' B' A'' B'' a b ε t
        (hddA ε hε) (hddB ε hε))
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common intrinsic endpoint curve for adjacent chart variations.
Its affine definition in the endpoint's own chart fixes all compatibility
jets, including the second jet which cancels the boundary terms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def normalEndpointDirection (g : SmoothMetric M) (e : FrameBundle g)
    (a : Fin 3 → ℝ) : JacobiCoordinateVector :=
  frameChartMatrix g e.base e *ᵥ Fin.cons 0 a

def normalEndpointCurve (g : SmoothMetric M) (e : FrameBundle g)
    (a : Fin 3 → ℝ) (ε : ℝ) : M :=
  (chartAt FourSpace e.base).symm
    (endpointChartLine (chartAt FourSpace e.base e.base) (normalEndpointDirection g e a) ε)

theorem normalEndpoint_first_chart (g : SmoothMetric M) (e : FrameBundle g)
    (c : M) (hc : e.base ∈ (chartAt FourSpace c).source) (a : Fin 3 → ℝ) :
    chartTransitionMatrix e.base c (chartAt FourSpace e.base e.base) *ᵥ
      normalEndpointDirection g e a = frameChartMatrix g c e *ᵥ Fin.cons 0 a := by
  rw [normalEndpointDirection, Matrix.mulVec_mulVec,
    frameChartMatrix_change g e.base c e (mem_chart_source FourSpace e.base) hc]

theorem normalEndpoint_position_zero (g : SmoothMetric M) (e : FrameBundle g)
    (c : M) (a : Fin 3 → ℝ) :
    endpointChartPosition e.base c (chartAt FourSpace e.base e.base)
      (normalEndpointDirection g e a) 0 = chartAt FourSpace c e.base := by
  rw [endpointChartPosition_zero]
  simp only [chartTransition, (chartAt FourSpace e.base).left_inv
    (mem_chart_source FourSpace e.base)]

theorem normalEndpoint_first_zero (g : SmoothMetric M) (e : FrameBundle g)
    (c : M) (hc : e.base ∈ (chartAt FourSpace c).source) (a : Fin 3 → ℝ) :
    endpointChartFirst e.base c (chartAt FourSpace e.base e.base)
      (normalEndpointDirection g e a) 0 =
        WithLp.toLp 2 (frameChartMatrix g c e *ᵥ Fin.cons 0 a) := by
  rw [endpointChartFirst_zero, normalEndpoint_first_chart g e c hc a]

/-- The same endpoint curve can be represented in every adjacent chart,
with actual continuous first and second jets and the required initial field. -/
theorem exists_normalEndpointJets (g : SmoothMetric M) (e : FrameBundle g)
    (c : M) (hc : e.base ∈ (chartAt FourSpace c).source) (a : Fin 3 → ℝ) :
    ∃ δ > 0, ∃ A A' A'' : ℝ → FourSpace,
      Continuous A ∧ Continuous A' ∧ Continuous A'' ∧
      A 0 = chartAt FourSpace c e.base ∧
      A' 0 = WithLp.toLp 2 (frameChartMatrix g c e *ᵥ Fin.cons 0 a) ∧
      A'' 0 = endpointChartSecond e.base c (chartAt FourSpace e.base e.base)
        (normalEndpointDirection g e a) 0 ∧
      (∀ ε ∈ Ioo (-δ) δ, HasDerivAt A (A' ε) ε ∧ HasDerivAt A' (A'' ε) ε) ∧
      (∀ ε ∈ Icc (-δ) δ,
        A ε ∈ (chartAt FourSpace c).target ∧
        (chartAt FourSpace c).symm (A ε) = normalEndpointCurve g e a ε) := by
  have hz := (chartAt FourSpace e.base).map_source (mem_chart_source FourSpace e.base)
  have hd : (chartAt FourSpace e.base).symm (chartAt FourSpace e.base e.base) ∈
      (chartAt FourSpace c).source := by
    simpa only [(chartAt FourSpace e.base).left_inv (mem_chart_source FourSpace e.base)] using hc
  obtain ⟨δ, hδ, A, A', A'', hA, hA', hA'', hder, heq, hoverlap⟩ :=
    exists_endpointChartJets e.base c (chartAt FourSpace e.base e.base)
      (normalEndpointDirection g e a) hz hd
  have hzero : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  refine ⟨δ, hδ, A, A', A'', hA, hA', hA'', ?_, ?_, (heq 0 hzero).2.2, hder, ?_⟩
  · rw [(heq 0 hzero).1, normalEndpoint_position_zero]
  · rw [(heq 0 hzero).2.1, normalEndpoint_first_zero g e c hc a]
  · intro ε hε
    rw [(heq ε hε).1]
    have hcε := (hoverlap ε hε).2
    exact ⟨(chartAt FourSpace c).map_source hcε,
      endpointChartPosition_symm _ _ _ _ _ hcε⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constant rescaling step. The precise classical inputs are the Ricci
contraction of positive sectional curvature (Petersen §3.1.1), and Exercise
3.4.18, p.88, together with the length definition in §1.2. Only the actual
four-dimensional metric, one Ricci diagonal entry, and positive constant
rescalings are used here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The one positive Ricci entry needed to show the Einstein constant is
positive; it is the contraction of three strictly positive sectional terms. -/
def PetersenPositiveRicciInput (g : SmoothMetric M) : Prop :=
  HasPositiveSectionalCurvature g → ∀ x, 0 < chartRicci g x 0 0

/-- Constant metric rescaling, in actual chart tensors and actual distance.
No Einstein normalization or model conclusion is included. -/
def PetersenScalingInput (g : SmoothMetric M) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ h : SmoothMetric M,
    (∀ x, chartMetric h x = c • chartMetric g x) ∧
    (∀ x, chartRicci h x = chartRicci g x) ∧
    (∀ x u v, sectionalNumerator h x (chartAt FourSpace x x) u v =
      c * sectionalNumerator g x (chartAt FourSpace x x) u v) ∧
    (∀ x y, scaledEDistance h 1 x y = scaledEDistance g c x y) ∧
    (FrameOrientation g → Nonempty (FrameOrientation h))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normal endpoint curves with zero covariant acceleration at zero.
Their quadratic coordinate correction is the actual Christoffel term. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def normalEndpointAcceleration (g : SmoothMetric M) (e : FrameBundle g)
    (a : Fin 3 → ℝ) : JacobiCoordinateVector :=
  -(jacobiConnection (fun i => connectionMatrix g e.base i (chartAt FourSpace e.base e.base))
    (normalEndpointDirection g e a) *ᵥ normalEndpointDirection g e a)

def normalEndpointQuadratic (g : SmoothMetric M) (e : FrameBundle g)
    (a : Fin 3 → ℝ) (s : ℝ) : FourSpace :=
  chartAt FourSpace e.base e.base + s • WithLp.toLp 2 (normalEndpointDirection g e a) +
    (s ^ 2 / 2) • WithLp.toLp 2 (normalEndpointAcceleration g e a)

def normalQuadraticEndpointCurve (g : SmoothMetric M) (e : FrameBundle g)
    (a : Fin 3 → ℝ) (s : ℝ) : M :=
  (chartAt FourSpace e.base).symm (normalEndpointQuadratic g e a s)

structure NormalQuadraticJetData (g : SmoothMetric M) (e : FrameBundle g)
    (c : M) (a : Fin 3 → ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  position : ℝ → FourSpace
  first : ℝ → FourSpace
  second : ℝ → FourSpace
  position_continuous : Continuous position
  first_continuous : Continuous first
  second_continuous : Continuous second
  position_zero : position 0 = chartAt FourSpace c e.base
  first_zero : first 0 = WithLp.toLp 2 (frameChartMatrix g c e *ᵥ Fin.cons 0 a)
  second_zero : second 0 = WithLp.toLp 2
    (chartTransitionSecondJet e.base c (chartAt FourSpace e.base e.base)
      (normalEndpointDirection g e a) (normalEndpointAcceleration g e a))
  derivative : ∀ s ∈ Ioo (-radius) radius,
    HasDerivAt position (first s) s ∧ HasDerivAt first (second s) s
  inside : ∀ s ∈ Icc (-radius) radius, position s ∈ (chartAt FourSpace c).target
  realizes : ∀ s ∈ Icc (-radius) radius,
    (chartAt FourSpace c).symm (position s) = normalQuadraticEndpointCurve g e a s

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Jacobi equation along the constructed parallel-frame flow.
Existence and the compact-interval bounds are derived from the metric
curvature and the linear ODE theorem, with no Jacobi-existence input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Jacobi Set
open scoped Manifold ContDiff _root_.Topology NNReal Matrix.Norms.L2Operator

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualRegularJacobi_R (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (t : ℝ) :
    (actualRegularJacobi g hRic e t).R = actualJacobiCurvature g e :=
  (Classical.choose_spec (exists_actualRegularJacobi g hRic e t)).1

theorem actualRegularJacobi_J (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (t : ℝ) :
    (actualRegularJacobi g hRic e t).J = (actualJacobiSolution g hRic e).J :=
  (Classical.choose_spec (exists_actualRegularJacobi g hRic e t)).2.1

end
end PositiveEinsteinFour.Geometry
end


section

/-! The unique actual Jacobi fields depend continuously on time and frame.
All interval-wise comparison data use these same global fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Jacobi
open scoped Manifold ContDiff _root_.Topology NNReal Matrix.Norms.L2Operator

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobiCurvature_joint_continuous (g : SmoothMetric M) (hRic : RicciThree g) :
    Continuous (fun p : ℝ × FrameBundle g => actualJacobiCurvature g p.2 p.1) :=
  continuous_const.add ((actual_frameCurvature_continuous g hRic).comp
    (parallelFrameFlowMap_continuous g 0))

theorem actualJacobiState_joint_continuous (g : SmoothMetric M) (hRic : RicciThree g) :
    Continuous (fun p : ℝ × FrameBundle g =>
      ((actualJacobiSolution g hRic p.2).J p.1,
        (actualJacobiSolution g hRic p.2).V p.1)) := by
  obtain ⟨K, hK⟩ := actualJacobiCurvature_bounded g hRic
  let A : ℝ × FrameBundle g → JacobiState →L[ℝ] JacobiState :=
    fun p => jacobiStateOperator (actualJacobiCurvature g p.2 p.1)
  let γ : FrameBundle g → ℝ → JacobiState := fun e s =>
    ((actualJacobiSolution g hRic e).J s, (actualJacobiSolution g hRic e).V s)
  have hA : Continuous A := continuous_jacobiStateOperator.comp
    (actualJacobiCurvature_joint_continuous g hRic)
  have hbound (s : ℝ) (e : FrameBundle g) : ‖A (s, e)‖ ≤ ((1 + K : ℝ≥0) : ℝ) := by
    apply (norm_jacobiStateOperator_le _).trans
    simpa only [NNReal.coe_add, NNReal.coe_one, add_comm] using add_le_add_left (hK e s) 1
  have h0 (e : FrameBundle g) : γ e 0 = ((0 : NormalMatrix), (1 : NormalMatrix)) := by
    simp only [γ, MatrixJacobiSolution.initial_position, MatrixJacobiSolution.initial_velocity]
  have hd (e : FrameBundle g) (s : ℝ) : HasDerivAt (γ e) (A (s, e) (γ e s)) s :=
    ((actualJacobiSolution g hRic e).position_derivative s).prodMk
      ((actualJacobiSolution g hRic e).velocity_derivative s)
  exact continuous_linear_solution_family A γ _ hA (1 + K) hbound h0 hd

theorem actualJacobiJ_joint_continuous (g : SmoothMetric M) (hRic : RicciThree g) :
    Continuous (fun p : ℝ × FrameBundle g => (actualJacobiSolution g hRic p.2).J p.1) :=
  (actualJacobiState_joint_continuous g hRic).fst

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

/-! Exact unit-speed length and endpoint distance bounds for the actual
complete geodesics, including their intrinsic unit-tangent formulation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem unitGeodesic_distance_le (g : SmoothMetric M) (o : FrameOrientation g)
    (u : UnitTangentBundle g) (a b : ℝ) :
    metricEDistance g (unitGeodesic g o u a) (unitGeodesic g o u b) ≤
      ENNReal.ofReal |b - a| :=
  frameGeodesic_distance_le g 0 (unitTangentFrame g o u) a b

end
end PositiveEinsteinFour.Geometry
end


section

/-! A finite subdivision of a compact curve segment whose individual
closed pieces lie in single coordinate charts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem exists_finite_curve_chart_partition (γ : ℝ → M) (hγ : Continuous γ)
    (a b : ℝ) (hab : a < b) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : ℕ → M, ∀ i < n,
      MapsTo γ (Icc (affinePartitionTime a b n i) (affinePartitionTime a b n (i + 1)))
        (chartAt FourSpace (c i)).source := by
  let U := fun c : M => γ ⁻¹' (chartAt FourSpace c).source
  have hU : ∀ c, IsOpen (U c) := fun c => (chartAt FourSpace c).open_source.preimage hγ
  have hcov : Icc a b ⊆ ⋃ c : M, U c := by
    intro t _
    exact mem_iUnion.mpr ⟨γ t, mem_chart_source FourSpace (γ t)⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_Icc hU hcov
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ + 1)
  have hnposR : 0 < (n : ℝ) := by
    have : 0 ≤ (b - a) / δ := div_nonneg (sub_nonneg.mpr hab.le) hδ.le
    linarith
  have hnpos : 0 < n := by exact_mod_cast hnposR
  have hstep : (b - a) / (n : ℝ) < δ := by
    apply (div_lt_iff₀ hnposR).mpr
    have h := (div_lt_iff₀ hδ).mp (show (b - a) / δ < (n : ℝ) by linarith)
    nlinarith
  have htime : ∀ i ≤ n, affinePartitionTime a b n i ∈ Icc a b := by
    intro i hi
    have hir : (i : ℝ) ≤ n := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    constructor
    · have hfrac0 : 0 ≤ (b - a) * (i : ℝ) / (n : ℝ) := by positivity
      dsimp [affinePartitionTime]
      linarith
    · dsimp [affinePartitionTime]
      have hfrac : (b - a) * (i : ℝ) / (n : ℝ) ≤ b - a := by
        apply (div_le_iff₀ hnposR).mpr
        nlinarith
      linarith
  have hc : ∀ i < n, ∃ c : M, ball (affinePartitionTime a b n i) δ ⊆ U c := by
    intro i hi
    exact hball _ (htime i hi.le)
  choose c hc using fun i : {i : ℕ // i < n} => hc i.val i.property
  let C : ℕ → M := fun i => if hi : i < n then c ⟨i, hi⟩ else γ a
  refine ⟨n, hnpos, C, fun i hi t ht => ?_⟩
  have hdist : dist t (affinePartitionTime a b n i) < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    have hdiff : affinePartitionTime a b n (i + 1) - affinePartitionTime a b n i =
        (b - a) / (n : ℝ) := by
      simp only [affinePartitionTime, Nat.cast_add, Nat.cast_one]
      ring
    linarith [ht.2]
  have hm := hc ⟨i, hi⟩ (show t ∈ ball (affinePartitionTime a b n i) δ from hdist)
  simpa only [C, dite_eq_left hi, U, Set.mem_preimage] using hm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joining two chart partitions at the corner of a piecewise C1 normal
field, and reconstructing the two index integrals from their finite sums. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]

theorem joinedPartition_chart_cover (γ : ℝ → M) (a c b : ℝ) (n m : ℕ) (hn : 0 < n)
    (C D : ℕ → M)
    (hC : ∀ i < n, MapsTo γ (Icc (affinePartitionTime a c n i)
      (affinePartitionTime a c n (i + 1))) (chartAt FourSpace (C i)).source)
    (hD : ∀ j < m, MapsTo γ (Icc (affinePartitionTime c b m j)
      (affinePartitionTime c b m (j + 1))) (chartAt FourSpace (D j)).source) :
    ∀ i < n + m, MapsTo γ (Icc (joinedPartitionTime a c b n m i)
      (joinedPartitionTime a c b n m (i + 1)))
      (chartAt FourSpace (if i < n then C i else D (i - n))).source := by
  intro i hi
  by_cases hil : i < n
  · rw [ite_eq_left hil, joinedPartitionTime_left _ _ _ _ _ _ hil.le,
      joinedPartitionTime_left _ _ _ _ _ _ hil]
    exact hC i hil
  · have heq : i = n + (i - n) := by omega
    have hj : i - n < m := by omega
    rw [ite_eq_right hil]
    rw [heq, show n + (i - n) + 1 = n + (i - n + 1) by omega,
      joinedPartitionTime_right _ _ _ _ _ _ hn, joinedPartitionTime_right _ _ _ _ _ _ hn,
      Nat.add_sub_cancel_left]
    exact hD (i - n) hj

end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine local normal-coordinate chart for the constructed radial
exponential, obtained from its actual derivative at zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
theorem frameMap_isUnit (g : SmoothMetric M) (e : FrameBundle g) :
    IsUnit e.frame.map.toContinuousLinearMap := by
  have hm : IsUnit e.frame.matrix :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr e.frame.det_ne_zero)
  have h := hm.map (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)).toMonoidHom
  change IsUnit (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) e.frame.matrix) at h
  have heq : e.frame.map.toContinuousLinearMap =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) e.frame.matrix := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rwa [heq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Riemannian volume, evaluated on a measurable
set in one chart. This is the target measure for the weighted area bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

omit [IsManifold I4 ∞ M] [T3Space M] in
theorem chart_image_measurable (c : M) (A : Set M) (hA : MeasurableSet A)
    (hAc : A ⊆ (chartAt FourSpace c).source) :
    MeasurableSet ((chartAt FourSpace c) '' A) := by
  let C := chartAt FourSpace c
  let H := C.toHomeomorphSourceTarget
  have hA' : MeasurableSet ((Subtype.val : C.source → M) ⁻¹' A) :=
    measurable_subtype_coe hA
  have hB' := H.toMeasurableEquiv.measurableSet_image.mpr hA'
  have hB := (MeasurableEmbedding.subtype_coe C.open_target.measurableSet).measurableSet_image' hB'
  convert hB using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨H ⟨x, hAc hx⟩, ⟨⟨x, hAc hx⟩, hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x.val, hx, rfl⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The continuous mean and its kernel on the actual scalar first-jet
completion.  Mean subtraction changes only the value coordinate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

section Probability

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- Pairwise square oscillation is twice the variance for a probability
measure.  Both integrals are ordinary real Bochner integrals. -/
theorem continuous_pairwise_square_integral (a : C(X, ℝ)) :
    (∫ x, ∫ y, (a x - a y) ^ 2 ∂μ ∂μ) =
      2 * ((∫ x, (a x) ^ 2 ∂μ) - (∫ x, a x ∂μ) ^ 2) := by
  have ha : Integrable a μ := a.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have ha₂ : Integrable (fun x => (a x) ^ 2) μ :=
    (a.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hinner (x : X) : (∫ y, (a x - a y) ^ 2 ∂μ) =
      (a x) ^ 2 - 2 * a x * (∫ y, a y ∂μ) + (∫ y, (a y) ^ 2 ∂μ) := by
    calc
      (∫ y, (a x - a y) ^ 2 ∂μ) =
          ∫ y, ((a x) ^ 2 - (2 * a x) * a y) + (a y) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = _ := by
        rw [integral_add (f := fun y => (a x) ^ 2 - (2 * a x) * a y)
            (g := fun y => (a y) ^ 2) ((integrable_const _).sub (ha.const_mul _)) ha₂,
          integral_sub (f := fun _ => (a x) ^ 2) (g := fun y => (2 * a x) * a y)
            (integrable_const _) (ha.const_mul _), integral_const_mul]
        simp
  simp_rw [hinner]
  rw [integral_add (f := fun x => (a x) ^ 2 - 2 * a x * (∫ y, a y ∂μ))
      (g := fun _ => ∫ y, (a y) ^ 2 ∂μ)
      (ha₂.sub ((ha.const_mul 2).mul_const _)) (integrable_const _),
    integral_sub (f := fun x => (a x) ^ 2)
      (g := fun x => 2 * a x * (∫ y, a y ∂μ)) ha₂ ((ha.const_mul 2).mul_const _),
    integral_mul_const,
    integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  ring

end Probability

end
end PositiveEinsteinFour.Geometry
end


section

/-! The trace-three Jacobi equation has no preconjugate interval longer
than π, by finite Dirichlet positivity and its first sine mode. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Matrix
open scoped _root_.Topology

noncomputable section

/-- On the first sine mode a trace-free curvature defect has zero trace. -/
theorem trace_first_mode_curvatureDirichlet {N : ℕ} (hN : 0 < N)
    (t : ℝ) (A : Fin N → NormalMatrix) (hA : ∀ i, (A i).trace = 0) :
    ((modeEmbedding (unitFirstSineVector N))ᵀ * curvatureDirichlet t A *
      modeEmbedding (unitFirstSineVector N)).trace = 3 * firstEigenvalue t N := by
  let E := modeEmbedding (unitFirstSineVector N)
  have heigen : scalarLift (referenceMatrix t N) * E = firstEigenvalue t N • E :=
    scalarLift_mode_eigenvector (referenceMatrix t N) (unitFirstSineVector N)
      (firstEigenvalue t N) (unitFirstSineVector_eigenvector N _)
  have hbase : Eᵀ * scalarLift (referenceMatrix t N) * E =
      firstEigenvalue t N • (1 : NormalMatrix) := by
    rw [Matrix.mul_assoc, heigen, Matrix.mul_smul,
      modeEmbedding_orthonormal _ (unitFirstSineVector_norm hN)]
  have hdefect : (Eᵀ * Matrix.blockDiagonal A * E).trace = 0 :=
    trace_mode_compression_defect A _ hA
  change (Eᵀ * curvatureDirichlet t A * E).trace = _
  rw [curvatureDirichlet, Matrix.mul_sub, Matrix.sub_mul, hbase,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, hdefect]
  norm_num [Matrix.trace_one]
  ring

theorem firstEigenvalue_nonneg_of_curvatureDirichlet {N : ℕ} (hN : 0 < N)
    (t : ℝ) (A : Fin N → NormalMatrix) (hA : ∀ i, (A i).trace = 0)
    (hpos : (curvatureDirichlet t A).PosSemidef) :
    0 ≤ firstEigenvalue t N := by
  have hp := (hpos.conjTranspose_mul_mul_same
    (modeEmbedding (unitFirstSineVector N))).trace_nonneg
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,
    trace_first_mode_curvatureDirichlet hN t A hA] at hp
  linarith

/-- The Einstein trace condition forces a conjugate point by any time strictly greater than π. -/
theorem RegularJacobi.le_pi_of_preconjugate {t : ℝ} (d : RegularJacobi t)
    (htrace : ∀ s, (d.R s).trace = 3)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit (d.J s)) : t ≤ Real.pi := by
  by_contra hnot
  have ht : Real.pi < t := lt_of_not_ge hnot
  have hpos := d.curvatureDirichlet_eventually_posDef (Real.pi_pos.trans ht) hpre
  obtain ⟨N, hNpos, hNneg, hN⟩ :=
    (hpos.and ((firstEigenvalue_eventually_neg ht).and
      (eventually_ge_atTop 1))).exists
  have hA : ∀ i : Fin N,
      (d.R (((i.val + 1 : ℕ) : ℝ) * meshStep t N) - 1).trace = 0 := by
    intro i
    rw [Matrix.trace_sub, htrace, Matrix.trace_one]
    norm_num
  have hnonneg := firstEigenvalue_nonneg_of_curvatureDirichlet
    (show 0 < N by omega) t _ hA hNpos.posSemidef
  exact (not_lt_of_ge hnonneg) hNneg

theorem RegularJacobi.exists_singular_of_pi_lt {t : ℝ} (d : RegularJacobi t)
    (htrace : ∀ s, (d.R s).trace = 3) (ht : Real.pi < t) :
    ∃ s, 0 < s ∧ s ≤ t ∧ ¬ IsUnit (d.J s) := by
  by_contra hnot
  push Not at hnot
  exact (not_le_of_gt ht) (d.le_pi_of_preconjugate htrace hnot)

end
end PositiveEinsteinFour.Jacobi

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualJacobiCurvature_trace (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (s : ℝ) : (actualJacobiCurvature g e s).trace = 3 := by
  apply frameCurvatureField_add_one_trace g _ (actual_einstein_decomposition _ hRic)
    (actual_weyl_traceFree _ hRic).1 (actual_weyl_traceFree _ hRic).2

theorem actualJacobi_le_pi_of_preconjugate (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (t : ℝ)
    (hpre : ∀ s, 0 < s → s ≤ t → IsUnit ((actualJacobiSolution g hRic e).J s)) :
    t ≤ Real.pi := by
  apply (actualRegularJacobi g hRic e t).le_pi_of_preconjugate
  · simpa only [actualRegularJacobi_R] using actualJacobiCurvature_trace g hRic e
  · simpa only [actualRegularJacobi_J] using hpre

theorem actualJacobi_exists_singular_of_pi_lt (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (t : ℝ) (ht : Real.pi < t) :
    ∃ s, 0 < s ∧ s ≤ t ∧ ¬ IsUnit ((actualJacobiSolution g hRic e).J s) := by
  have h := (actualRegularJacobi g hRic e t).exists_singular_of_pi_lt
    (fun s => by rw [actualRegularJacobi_R]; exact actualJacobiCurvature_trace g hRic e s) ht
  simpa only [actualRegularJacobi_J] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth Poincaré estimate passes to the actual first-jet completion.
It makes the Dirichlet form coercive on the closed mean-zero subspace and
therefore supplies a unique mean-zero weak Poisson solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

local instance scalarCoercive_h1Space_r45cbc0_1 (d : ParallelMetricData g μ) :
    NormedSpace ℝ (scalarH1 d) := Submodule.normedSpace (𝕜 := ℝ) (scalarH1 d)
local instance scalarCoercive_meanZeroSpace_r45cbc0_1 (d : ParallelMetricData g μ) :
    NormedSpace ℝ (scalarH1MeanZero d) :=
  Submodule.normedSpace (𝕜 := ℝ) (scalarH1MeanZero d)
local instance scalarCoercive_h1Inner_r45cbc0_1 (d : ParallelMetricData g μ) :
    InnerProductSpace ℝ (scalarH1 d) := Submodule.innerProductSpace _
local instance scalarCoercive_meanZeroInner_r45cbc0_1 (d : ParallelMetricData g μ) :
    InnerProductSpace ℝ (scalarH1MeanZero d) := Submodule.innerProductSpace _
/-- The estimate needed here, stated solely for actual smooth mean-zero
scalars.  The geometric Poincaré theorem supplies this hypothesis. -/
def SmoothScalarPoincare (d : ParallelMetricData g μ) (K : ℝ) : Prop :=
  ∀ a : SmoothScalar (M := M), (∫ e, a.val e.base ∂μ) = 0 →
    ‖smoothScalarValueL2 g μ a‖ ^ 2 ≤
      K * ∑ i : Fin 4, ‖smoothScalarGradientL2 d i a‖ ^ 2

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first positive singular time of the actual Jacobi matrix is attained.
Normalizing by time removes the initial zero; compactness then gives a
positive first zero, and the trace-three comparison bounds it by π. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.L2Operator

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actual_normalizedJacobi_continuous (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) :
    Continuous (normalizedJacobi (actualJacobiSolution g hRic e).J) := by
  let d := actualJacobiSolution g hRic e
  apply continuous_iff_continuousAt.mpr
  intro s
  change ContinuousAt (dslope d.J 0) s
  by_cases hs : s = 0
  · subst s
    exact continuousAt_dslope_same.mpr (d.position_derivative 0).differentiableAt
  · exact (continuousAt_dslope_of_ne hs).mpr d.continuous_J.continuousAt

theorem exists_actualFirstConjugateTime (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) :
    ∃ c : ℝ, 0 < c ∧ c ≤ Real.pi ∧
      ¬ IsUnit ((actualJacobiSolution g hRic e).J c) ∧
      ∀ s, 0 < s → s < c → IsUnit ((actualJacobiSolution g hRic e).J s) := by
  let d := actualJacobiSolution g hRic e
  have hd0 : HasDerivAt d.J 1 0 := by
    simpa only [d.initial_velocity] using d.position_derivative 0
  let S : Set ℝ := Icc 0 (Real.pi + 1) ∩ {s | (normalizedJacobi d.J s).det = 0}
  have hS : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_eq
      (actual_normalizedJacobi_continuous g hRic e).matrix_det continuous_const)
  have hSnonempty : S.Nonempty := by
    obtain ⟨s, hs, hsbound, hsing⟩ :=
      actualJacobi_exists_singular_of_pi_lt g hRic e (Real.pi + 1) (by linarith)
    have hz : (d.J s).det = 0 := by
      by_contra hne
      exact hsing ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))
    refine ⟨s, ⟨⟨hs.le, hsbound⟩, ?_⟩⟩
    change (normalizedJacobi d.J s).det = 0
    rw [normalizedJacobi_pos d.initial_position hs.ne', Matrix.det_smul,
      Fintype.card_fin, hz, mul_zero]
  obtain ⟨c, hc⟩ := hS.exists_isLeast hSnonempty
  have hcpos : 0 < c := by
    have hcne : c ≠ 0 := by
      intro hzero
      have hz := hc.1.2
      change (normalizedJacobi d.J c).det = 0 at hz
      rw [hzero, normalizedJacobi_zero hd0, Matrix.det_one] at hz
      norm_num at hz
    exact lt_of_le_of_ne hc.1.1.1 (Ne.symm hcne)
  have hbefore : ∀ s, 0 < s → s < c → IsUnit (d.J s) := by
    intro s hs hsc
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hsS : s ∈ S := by
      refine ⟨⟨hs.le, hsc.le.trans hc.1.1.2⟩, ?_⟩
      change (normalizedJacobi d.J s).det = 0
      rw [normalizedJacobi_pos d.initial_position hs.ne', Matrix.det_smul,
        Fintype.card_fin, hz, mul_zero]
    exact (not_le_of_gt hsc) (hc.2 hsS)
  have hcbound : c ≤ Real.pi := by
    by_contra hnot
    have hπc : Real.pi < c := lt_of_not_ge hnot
    have ht : Real.pi < (Real.pi + c) / 2 := by linarith
    have htc : (Real.pi + c) / 2 < c := by linarith
    have hle := actualJacobi_le_pi_of_preconjugate g hRic e ((Real.pi + c) / 2)
      (fun s hs hst => hbefore s hs (hst.trans_lt htc))
    exact (not_le_of_gt ht) hle
  have hczero : (d.J c).det = 0 := by
    have hz := hc.1.2
    change (normalizedJacobi d.J c).det = 0 at hz
    rw [normalizedJacobi_pos d.initial_position hcpos.ne', Matrix.det_smul,
      Fintype.card_fin] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (inv_ne_zero hcpos.ne'))
  refine ⟨c, hcpos, hcbound, ?_, hbefore⟩
  intro hu
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero hczero

def actualFirstConjugateTime (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : ℝ :=
  Classical.choose (exists_actualFirstConjugateTime g hRic e)

theorem actualFirstConjugateTime_pos (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : 0 < actualFirstConjugateTime g hRic e :=
  (Classical.choose_spec (exists_actualFirstConjugateTime g hRic e)).1

theorem actualFirstConjugateTime_le_pi (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : actualFirstConjugateTime g hRic e ≤ Real.pi :=
  (Classical.choose_spec (exists_actualFirstConjugateTime g hRic e)).2.1

theorem actualFirstConjugateTime_singular (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) :
    ¬ IsUnit ((actualJacobiSolution g hRic e).J (actualFirstConjugateTime g hRic e)) :=
  (Classical.choose_spec (exists_actualFirstConjugateTime g hRic e)).2.2.1

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration by parts for the actual exterior derivative of one-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_3 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! A conjugate point supplies a nonzero actual normal Jacobi field with
zero endpoint positions and nonzero terminal covariant velocity.  The last
assertion follows from uniqueness of the linear ODE, anchored at that endpoint. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix Set
open scoped _root_.Topology NNReal Matrix.Norms.L2Operator

noncomputable section

theorem MatrixJacobiSolution.kernel_intersection_eq_zero {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (K : ℝ≥0) (hK : ∀ s, ‖R s‖ ≤ K)
    (c : ℝ) (w : Fin 3 → ℝ) (hJ : d.J c *ᵥ w = 0) (hV : d.V c *ᵥ w = 0) :
    w = 0 := by
  let B : NormalMatrix := fun i _ => w i
  let γ : ℝ → JacobiState := fun s => (d.J s * B, d.V s * B)
  let A : ℝ → JacobiState →L[ℝ] JacobiState := fun s => jacobiStateOperator (R s)
  let T : ℝ := |c| + 1
  have hbound (s : ℝ) : ‖A s‖ ≤ ((1 + K : ℝ≥0) : ℝ) := by
    apply (norm_jacobiStateOperator_le _).trans
    simpa only [NNReal.coe_add, NNReal.coe_one, add_comm] using add_le_add_left (hK s) 1
  have hγ : LinearCurveOn A γ (Ioo (-T) T) := by
    intro s _
    have hp := (d.position_derivative s).mul_const B
    have hv := (d.velocity_derivative s).mul_const B
    simpa only [γ, A, jacobiStateOperator_apply, neg_mul, Matrix.mul_assoc] using
      hp.prodMk hv
  have hzero : LinearCurveOn A (fun _ => 0) (Ioo (-T) T) := by
    intro s _
    simpa only [map_zero] using hasDerivAt_const s (0 : JacobiState)
  have hmulzero (Q : NormalMatrix) (hQ : Q *ᵥ w = 0) : Q * B = 0 := by
    ext i j
    change (Q *ᵥ w) i = 0
    exact congrFun hQ i
  have hinit : γ c = 0 := by
    change (d.J c * B, d.V c * B) = (0, 0)
    rw [hmulzero _ hJ, hmulzero _ hV]
  have hc : c ∈ Ioo (-T) T := by
    dsimp [T]
    constructor <;> linarith [neg_abs_le c, le_abs_self c]
  have h0 : (0 : ℝ) ∈ Ioo (-T) T := by
    dsimp [T]
    constructor <;> linarith [abs_nonneg c]
  have heq := linear_curve_eqOn_interval A (1 + K) hbound hγ hzero hc hinit
  have hB : B = 0 := by
    simpa only [γ, d.initial_velocity, Matrix.one_mul, Prod.snd_zero] using
      congrArg Prod.snd (heq h0)
  funext i
  exact congrArg (fun Q : NormalMatrix => Q i 0) hB

theorem MatrixJacobiSolution.velocity_ne_zero_of_kernel {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (K : ℝ≥0) (hK : ∀ s, ‖R s‖ ≤ K)
    (c : ℝ) (w : Fin 3 → ℝ) (hw : w ≠ 0) (hJ : d.J c *ᵥ w = 0) :
    d.V c *ᵥ w ≠ 0 := by
  intro hV
  exact hw (d.kernel_intersection_eq_zero K hK c w hJ hV)

end
end PositiveEinsteinFour.Jacobi

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.L2Operator

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_actualJacobi_conjugate_vector (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (c : ℝ)
    (hc : ¬ IsUnit ((actualJacobiSolution g hRic e).J c)) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧ (actualJacobiSolution g hRic e).J c *ᵥ w = 0 ∧
      (actualJacobiSolution g hRic e).V c *ᵥ w ≠ 0 := by
  have hdet : ((actualJacobiSolution g hRic e).J c).det = 0 := by
    by_contra hne
    exact hc ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))
  obtain ⟨w, hw, hJ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨K, hK⟩ := actualJacobiCurvature_bounded g hRic
  exact ⟨w, hw, hJ,
    (actualJacobiSolution g hRic e).velocity_ne_zero_of_kernel K (hK e) c w hw hJ⟩

theorem exists_actualFirstConjugate_vector (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧
      (actualJacobiSolution g hRic e).J (actualFirstConjugateTime g hRic e) *ᵥ w = 0 ∧
      (actualJacobiSolution g hRic e).V (actualFirstConjugateTime g hRic e) *ᵥ w ≠ 0 :=
  exists_actualJacobi_conjugate_vector g hRic e _
    (actualFirstConjugateTime_singular g hRic e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constructed radial frame lies over the actual exponential map,
by uniqueness of the metric Hamiltonian trajectories. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem HeatRadialFrameFlow.kinetic_eq {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    (K : KineticLocalFlow g c (p.1, 0)) (hT : K.time ≤ F.time)
    (v : FourSpace) (hv : (v, p) ∈ closedBall (0, p) F.radius)
    (hK : heatRadialCotangentState g c v p ∈ ball (p.1, 0) K.radius)
    (t : ℝ) (ht : t ∈ Ioo (-K.time) K.time) :
    K.map (heatRadialCotangentState g c v p, t) =
      heatRadialCotangentState g c v (F.map ((v, p), t)).2 := by
  have he := K.eq_on _ hK
    (fun s => heatRadialCotangentState g c v (F.map ((v, p), s)).2)
    (by rw [F.initial (v, p) hv])
    (fun s hs => F.cotangent_derivative (v, p) hv s
      ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  exact he ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite smooth orthonormal frames over the actual normal exponential
chart, constructed by radial parallel transport through zero velocity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def HeatRadialFrameFlow.restrictTime {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p) (δ : ℝ)
    (hδ : 0 < δ) (hle : δ ≤ F.time) : HeatRadialFrameFlow g c p where
  radius := F.radius
  radius_pos := F.radius_pos
  time := δ
  time_pos := hδ
  map := F.map
  continuous := F.continuous.mono (fun q hq => ⟨hq.1,
    ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩⟩)
  initial := F.initial
  in_chart := fun q hq t ht => F.in_chart q hq t
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  derivative := fun q hq t ht => F.derivative q hq t
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  regular := F.regular

end
end PositiveEinsteinFour.Geometry
end


section

/-! Intrinsic radial differential and Gauss identities for the actual
exponential, expressed in the metric rather than in an output chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Bundle
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metric_inner_abs_le (g : SmoothMetric M) (x : M) (u v : TangentSpace I4 x) :
    |g.inner x u v| ≤ metricTangentNorm g x u * metricTangentNorm g x v := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact abs_real_inner_le_norm u v

end
end PositiveEinsteinFour.Geometry
end


section

/-! The index density in an actual metric chart equals the normal Euclidean
Jacobi index density when evaluated in a parallel orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem jacobiMetricPair_frame (G E : Mat4) (hE : Eᵀ * G * E = 1)
    (u v : JacobiCoordinateVector) :
    jacobiMetricPair G (E *ᵥ u) (E *ᵥ v) = u ⬝ᵥ v := by
  rw [← jacobiMetricPair_left_product, ← jacobiMetricPair_right_product, hE]
  simp only [jacobiMetricPair, Matrix.one_mulVec]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scaling the initial direction scales time in the radial frame ODE. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatRadialDirectionScale (r : ℝ) (q : HeatRadialFrameSpace) : HeatRadialFrameSpace :=
  (r • q.1, q.2)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatRadialFrameField_scale (g : SmoothMetric M) (c : M) (r : ℝ)
    (q : HeatRadialFrameSpace) :
    heatRadialFrameField g c (heatRadialDirectionScale r q) =
      (0, r • (heatRadialFrameField g c q).2) := by
  have hv : heatRadialFrameVelocity (heatRadialDirectionScale r q) =
      r • heatRadialFrameVelocity q := by
    exact Matrix.mulVec_smul _ _ _
  have hC : heatRadialFrameConnection g c (heatRadialDirectionScale r q) =
      r • heatRadialFrameConnection g c q := by
    change (∑ i : Fin 4, heatRadialFrameVelocity (heatRadialDirectionScale r q) i •
      connectionMatrix g c i q.2.1) = r • ∑ i : Fin 4,
        heatRadialFrameVelocity q i • connectionMatrix g c i q.2.1
    rw [hv, Finset.smul_sum]
    simp only [Pi.smul_apply, smul_smul, smul_eq_mul]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext i
    change heatRadialFrameVelocity (heatRadialDirectionScale r q) i =
      r * heatRadialFrameVelocity q i
    rw [hv]
    rfl
  · change -(heatRadialFrameConnection g c (heatRadialDirectionScale r q) * q.2.2) =
      r • -(heatRadialFrameConnection g c q * q.2.2)
    rw [hC, smul_mul_assoc, smul_neg]

theorem hasDerivAt_heatRadialDirectionScale (g : SmoothMetric M) (c : M)
    (α : ℝ → HeatRadialFrameSpace) (r t : ℝ)
    (hα : HasDerivAt α (heatRadialFrameField g c (α (r * t))) (r * t)) :
    HasDerivAt (fun s => heatRadialDirectionScale r (α (r * s)))
      (heatRadialFrameField g c (heatRadialDirectionScale r (α (r * t)))) t := by
  have h : HasDerivAt (fun s => α (r * s))
      (r • heatRadialFrameField g c (α (r * t))) t := by
    simpa only [Function.comp_def, id_eq, mul_one] using!
      hα.scomp t ((hasDerivAt_id t).const_mul r)
  have hv : HasDerivAt (fun s => r • (α (r * s)).1) 0 t := by
    have hd : HasDerivAt (fun s => (α (r * s)).1) 0 t := by
      have hd' : HasDerivAt (fun s => (α (r * s)).1)
          ((r • heatRadialFrameField g c (α (r * t))).1) t := h.fst
      change HasDerivAt (fun s => (α (r * s)).1) (r • (0 : FourSpace)) t at hd'
      simpa only [smul_zero] using hd'
    simpa only [smul_zero] using! hd.const_smul r
  have hp : HasDerivAt (fun s => (α (r * s)).2)
      (r • (heatRadialFrameField g c (α (r * t))).2) t := by
    simpa only [Prod.smul_snd] using! h.snd
  rw [heatRadialFrameField_scale]
  exact hv.prodMk hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local inverses of the actual exponential are C1 wherever its actual
coordinate derivative is invertible. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_chart_local_inverse_contMDiffAt (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (d : M) (x : FourSpace)
    (C : OpenPartialHomeomorph FourSpace M) (hx : x ∈ C.source)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hd : frameExponential g o e x ∈ (chartAt FourSpace d).source)
    (hL : IsUnit (fderiv ℝ (fun v : FourSpace =>
      chartAt FourSpace d (frameExponential g o e v)) x)) :
    ContMDiffAt I4 I4 1 C.symm (frameExponential g o e x) := by
  let F := fun v : FourSpace => chartAt FourSpace d (frameExponential g o e v)
  let E : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hE : (E : FourSpace →L[ℝ] FourSpace) = fderiv ℝ F x := hL.unit_spec
  have hcont : ContDiffAt ℝ 1 F x := frameExponential_chart_contDiffAt g o d e x hd
  have hder : HasFDerivAt F (E : FourSpace →L[ℝ] FourSpace) x := by
    rw [hE]
    exact (hcont.differentiableAt one_ne_zero).hasFDerivAt
  let hf := hcont.hasStrictFDerivAt' hder one_ne_zero
  let H := fun z : FourSpace => C.symm ((chartAt FourSpace d).symm z)
  have hleft : ∀ᶠ v in 𝓝 x, H (F v) = v := by
    have hnear := (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace d).open_source.mem_nhds hd)
    filter_upwards [C.open_source.mem_nhds hx, hnear] with v hv hvc
    change C.symm ((chartAt FourSpace d).symm
      (chartAt FourSpace d (frameExponential g o e v))) = v
    rw [(chartAt FourSpace d).left_inv hvc, ← hC hv]
    exact C.left_inv hv
  have heq := hf.localInverse_unique hleft
  have hcontH : ContDiffAt ℝ 1 H (F x) :=
    (hcont.to_localInverse hder one_ne_zero).congr_of_eventuallyEq heq
  have hchart : ContMDiffAt I4 I4 1 (chartAt FourSpace d) (frameExponential g o e x) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas d) hd
  have h := hcontH.contMDiffAt.comp (frameExponential g o e x) hchart
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace d).open_source.mem_nhds hd] with y hy
  change C.symm y = C.symm ((chartAt FourSpace d).symm (chartAt FourSpace d y))
  rw [(chartAt FourSpace d).left_inv hy]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normal fields along the actual parallel-frame flow.  Their ordinary
coordinate derivatives and their index densities are derived from the
constructed horizontal ODE, rather than supplied as extra field identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix Set
open scoped _root_.Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def normalChartField (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (a : ℝ → Fin 3 → ℝ) (t : ℝ) : JacobiCoordinateVector :=
  frameChartMatrix g c (parallelFrameFlowMap g 0 t e) *ᵥ Fin.cons 0 (a t)

def normalChartFrameRate (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (t : ℝ) : Mat4 :=
  (parallelFrameVectorField g c 0
    (frameCoordinateState g c (parallelFrameFlowMap g 0 t e))).2

def normalChartFieldRate (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (a b : ℝ → Fin 3 → ℝ) (t : ℝ) : JacobiCoordinateVector :=
  normalChartFrameRate g c e t *ᵥ Fin.cons 0 (a t) +
    frameChartMatrix g c (parallelFrameFlowMap g 0 t e) *ᵥ Fin.cons 0 (b t)

theorem normalChartFrame_hasDerivAt (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (fun s => frameChartMatrix g c (parallelFrameFlowMap g 0 s e))
      (normalChartFrameRate g c e t) t := by
  have h := parallelFrameCurveAt_fixedChart g c (parallelFrameFlowMap g 0 · e) t 0
    (parallelFrameFlowMap_curve_continuous g 0 e).continuousAt hc
    (parallelFrameFlowMap_primitive g 0 e t)
  exact (ContinuousLinearMap.snd ℝ FourSpace Mat4).hasFDerivAt.comp_hasDerivAt t h

theorem normalChartFieldRate_eq (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (a b : ℝ → Fin 3 → ℝ) (t : ℝ) :
    normalChartFieldRate g c e a b t =
      frameChartMatrix g c (parallelFrameFlowMap g 0 t e) *ᵥ Fin.cons 0 (b t) -
        jacobiConnection
          (fun i => connectionMatrix g c i (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base))
          (fun i => frameChartMatrix g c (parallelFrameFlowMap g 0 t e) i 0) *ᵥ
            normalChartField g c e a t := by
  simp only [normalChartFieldRate, normalChartFrameRate, normalChartField,
    parallelFrameVectorField, parallelFrameConnection, frameCoordinateState,
    jacobiConnection, Matrix.neg_mulVec, Matrix.mulVec_mulVec, sub_eq_add_neg]
  exact add_comm _ _

theorem continuousOn_matrixVector {S : Set ℝ} {A : ℝ → Mat4}
    {a : ℝ → JacobiCoordinateVector} (hA : ContinuousOn A S) (ha : ContinuousOn a S) :
    ContinuousOn (fun t => A t *ᵥ a t) S := by
  apply continuousOn_pi.mpr
  intro i
  unfold Matrix.mulVec dotProduct
  apply continuousOn_finsetSum
  intro j _
  exact (continuousOn_pi.mp (continuousOn_pi.mp hA i) j).mul (continuousOn_pi.mp ha j)

theorem normalChartFrame_continuousOn (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (S : Set ℝ)
    (hc : ∀ t ∈ S, (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    ContinuousOn (fun t => frameChartMatrix g c (parallelFrameFlowMap g 0 t e)) S := by
  intro t ht
  exact (normalChartFrame_hasDerivAt g c e t (hc t ht)).continuousAt.continuousWithinAt

theorem normalChartFrameRate_continuousOn (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (S : Set ℝ)
    (hc : ∀ t ∈ S, (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    ContinuousOn (normalChartFrameRate g c e) S := by
  intro t ht
  have hs : ContinuousAt (fun s : ℝ =>
      frameCoordinateState g c (parallelFrameFlowMap g 0 s e)) t :=
    (frameCoordinateState_continuousAt g c (parallelFrameFlowMap g 0 t e)
      (hc t ht)).comp (f := fun s : ℝ => parallelFrameFlowMap g 0 s e)
        (parallelFrameFlowMap_curve_continuous g 0 e).continuousAt
  have hp : (frameCoordinateState g c (parallelFrameFlowMap g 0 t e)).1 ∈
      (chartAt FourSpace c).target := (chartAt FourSpace c).map_source (hc t ht)
  have hV : ContinuousAt (fun s : ℝ => parallelFrameVectorField g c 0
      (frameCoordinateState g c (parallelFrameFlowMap g 0 s e))) t :=
    (parallelFrameVectorField_contDiffAt g c 0 _ hp).continuousAt.comp
      (f := fun s : ℝ => frameCoordinateState g c (parallelFrameFlowMap g 0 s e)) hs
  exact hV.snd.continuousWithinAt

theorem normalChartField_continuousOn (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (a : ℝ → Fin 3 → ℝ) (S : Set ℝ)
    (hc : ∀ t ∈ S, (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source)
    (ha : ContinuousOn a S) : ContinuousOn (normalChartField g c e a) S :=
  continuousOn_matrixVector (normalChartFrame_continuousOn g c e S hc)
    (continuousOn_normal_lift a S ha)

theorem normalChartFieldRate_continuousOn (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (a b : ℝ → Fin 3 → ℝ) (S : Set ℝ)
    (hc : ∀ t ∈ S, (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source)
    (ha : ContinuousOn a S) (hb : ContinuousOn b S) :
    ContinuousOn (normalChartFieldRate g c e a b) S :=
  (continuousOn_matrixVector (normalChartFrameRate_continuousOn g c e S hc)
    (continuousOn_normal_lift a S ha)).add
    (continuousOn_matrixVector (normalChartFrame_continuousOn g c e S hc)
      (continuousOn_normal_lift b S hb))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Common geometric domain for normal-frame slices over an open set of
actual frames. Exponential agreement holds throughout the same ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
theorem HeatRadialFrameFlow.kinetic_eq_from {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    {a : CotangentCoordinates} (K : KineticLocalFlow g c a) (hT : K.time ≤ F.time)
    (v : FourSpace) (q : CoordinateFrameSpace)
    (hv : (v, q) ∈ closedBall (0, p) F.radius)
    (hK : heatRadialCotangentState g c v q ∈ ball a K.radius)
    (t : ℝ) (ht : t ∈ Ioo (-K.time) K.time) :
    K.map (heatRadialCotangentState g c v q, t) =
      heatRadialCotangentState g c v (F.map ((v, q), t)).2 := by
  exact K.eq_on _ hK
    (fun s => heatRadialCotangentState g c v (F.map ((v, q), s)).2)
    (by rw [F.initial (v, q) hv])
    (fun s hs => F.cotangent_derivative (v, q) hv s
      ⟨by linarith [hs.1], by linarith [hs.2]⟩) ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! Radial scaling identifies the endpoint derivative with the actual
horizontal frame field. This is the radial parallel-transport identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem HeatRadialFrameFlow.scaling_eventually {g : SmoothMetric M} {c : M}
    {p : CoordinateFrameSpace} (F : HeatRadialFrameFlow g c p)
    (v : FourSpace) (hv : (v, p) ∈ ball (0, p) F.radius)
    (t : ℝ) (ht : 0 < t) (htF : t < F.time) :
    ∀ᶠ r : ℝ in 𝓝 1,
      F.map ((r • v, p), t) = heatRadialDirectionScale r (F.map ((v, p), r * t)) := by
  let ε := (F.time + t) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith [F.time_pos]
  have htε : t < ε := by dsimp [ε]; linarith
  have hεF : ε < F.time := by dsimp [ε]; linarith
  let G := F.restrictTime ε hε hεF.le
  have hbase : ∀ᶠ r : ℝ in 𝓝 1, (r • v, p) ∈ ball (0, p) F.radius := by
    have hc : Continuous (fun r : ℝ => (r • v, p)) :=
      (continuous_id.smul continuous_const).prodMk continuous_const
    have hc1 : ContinuousAt (fun r : ℝ => (r • v, p)) 1 := hc.continuousAt
    exact hc1.preimage_mem_nhds (by
      simpa only [one_smul] using! isOpen_ball.mem_nhds hv)
  have htime : ∀ᶠ r : ℝ in 𝓝 1, r * ε < F.time := by
    have hc : Continuous (fun r : ℝ => r * ε) := continuous_id.mul continuous_const
    have hc1 : ContinuousAt (fun r : ℝ => r * ε) 1 := hc.continuousAt
    exact hc1.preimage_mem_nhds (by
      simpa only [one_mul] using isOpen_Iio.mem_nhds hεF)
  filter_upwards [hbase, htime, eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)]
    with r hrbase hrtime hrpos
  have hsol (s : ℝ) (hs : s ∈ Ioo (-G.time) G.time) :
      HasDerivAt (fun u => heatRadialDirectionScale r (F.map ((v, p), r * u)))
        (heatRadialFrameField g c (heatRadialDirectionScale r (F.map ((v, p), r * s)))) s := by
    apply hasDerivAt_heatRadialDirectionScale g c (fun u => F.map ((v, p), u)) r s
    apply F.derivative (v, p) (ball_subset_closedBall hv)
    change -ε < s ∧ s < ε at hs
    constructor
    · have hh := mul_lt_mul_of_pos_left hs.1 hrpos
      nlinarith
    · have hh := mul_lt_mul_of_pos_left hs.2 hrpos
      nlinarith
  have hzero : heatRadialDirectionScale r (F.map ((v, p), r * 0)) = (r • v, p) := by
    rw [mul_zero, F.initial (v, p) (ball_subset_closedBall hv)]
    rfl
  exact G.eq_on (r • v, p) (ball_subset_closedBall hrbase) _ hzero hsol
    ⟨by change -ε < t; linarith, htε⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual unit geodesic satisfies the ordinary coordinate geodesic
equation in every fixed chart containing the point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped _root_.Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def geodesicChartVelocity (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (t : ℝ) : JacobiCoordinateVector :=
  fun i => frameChartMatrix g c (parallelFrameFlowMap g 0 t e) i 0

theorem geodesicChartVelocity_hasDerivAt (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (geodesicChartVelocity g c e)
      (-(jacobiConnection
        (fun i => connectionMatrix g c i (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base))
        (geodesicChartVelocity g c e t) *ᵥ geodesicChartVelocity g c e t)) t := by
  have hE := normalChartFrame_hasDerivAt g c e t hc
  apply hasDerivAt_pi.mpr
  intro i
  have hi := hasDerivAt_pi.mp (hasDerivAt_pi.mp hE i) 0
  simpa only [geodesicChartVelocity, normalChartFrameRate, parallelFrameVectorField,
    parallelFrameConnection, frameCoordinateState, jacobiConnection,
    Matrix.neg_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.neg_apply] using hi

theorem geodesicChartPosition_hasDerivAt (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (fun s => chartAt FourSpace c (parallelFrameFlowMap g 0 s e).base)
      (WithLp.toLp 2 (geodesicChartVelocity g c e t)) t :=
  frameGeodesic_chart_derivative g 0 e c t hc

theorem geodesicChartPosition_continuousOn (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (S : Set ℝ)
    (hc : ∀ t ∈ S, (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    ContinuousOn (fun t => chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base) S :=
  fun t ht => (geodesicChartPosition_hasDerivAt g c e t (hc t ht)).continuousAt.continuousWithinAt

theorem geodesicChartVelocity_continuousOn (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (S : Set ℝ)
    (hc : ∀ t ∈ S, (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    ContinuousOn (geodesicChartVelocity g c e) S :=
  fun t ht => (geodesicChartVelocity_hasDerivAt g c e t (hc t ht)).continuousAt.continuousWithinAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrating Gauss' lemma bounds the radial displacement of a lifted
C1 curve by the length of its actual exponential image. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_curve_derivative (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (α : ℝ → FourSpace) (hα : ContDiff ℝ 1 α) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) I4 (fun s => frameExponential g o e (α s)) t 1 =
      mfderiv I4 I4 (frameExponential g o e) (α t) (deriv α t) := by
  have he := (frameExponential_contMDiff g o e).mdifferentiable one_ne_zero (α t)
  have ha := hα.contMDiff.mdifferentiable one_ne_zero t
  have hc := mfderiv_comp_apply t he ha (1 : ℝ)
  have hader : mfderiv 𝓘(ℝ, ℝ) I4 α t 1 = deriv α t := by
    rw [mfderiv_eq_fderiv, (hα.differentiable one_ne_zero t).hasDerivAt.hasFDerivAt.fderiv]
    exact one_smul ℝ _
  exact hc.trans (congrArg (mfderiv I4 I4 (frameExponential g o e) (α t)) hader)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_first _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Spatial derivatives of a jointly regular family. The center and initial
frame are parameters; differentiation here changes only the normal vector. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilyPartial (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (i : Fin 4) (z : HeatRadialFrameSpace) : CoordinateFrameSpace :=
  fderiv ℝ P z (coordinateVector i, 0)

theorem heatFamilyPartial_slice (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (z : HeatRadialFrameSpace) (hP : DifferentiableAt ℝ P z) (i : Fin 4) :
    heatFamilyPartial P i z =
      fderiv ℝ (fun x => P (x, z.2)) z.1 (coordinateVector i) := by
  have harg : HasFDerivAt (fun x : FourSpace => (x, z.2))
      ((ContinuousLinearMap.id ℝ FourSpace).prod
        (0 : FourSpace →L[ℝ] CoordinateFrameSpace)) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hd : HasFDerivAt (fun x => P (x, z.2))
      ((fderiv ℝ P z).comp ((ContinuousLinearMap.id ℝ FourSpace).prod
        (0 : FourSpace →L[ℝ] CoordinateFrameSpace))) z.1 := hP.hasFDerivAt.comp z.1 harg
  exact (congrArg (fun L : FourSpace →L[ℝ] CoordinateFrameSpace =>
    L (coordinateVector i)) hd.fderiv).symm

theorem heatFamilyPartial_contDiffAt (n : ℕ)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 1 : ℕ) P z) (i : Fin 4) :
    ContDiffAt ℝ n (heatFamilyPartial P i) z :=
  (hP.fderiv_right (m := n) (by norm_num [Nat.cast_add])).clm_apply contDiffAt_const

theorem heatFamilyMatrixDeterminant_contDiffAt (n : ℕ)
    (A : HeatRadialFrameSpace → Mat4) (z : HeatRadialFrameSpace)
    (hA : ∀ i j, ContDiffAt ℝ n (fun y => A y i j) z) :
    ContDiffAt ℝ n (fun y => (A y).det) z := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  exact contDiffAt_const.mul (contDiffAt_prod fun i _ => hA (σ i) i)

theorem heatFamilyMatrixInverse_contDiffAt (n : ℕ)
    (A : HeatRadialFrameSpace → Mat4) (z : HeatRadialFrameSpace)
    (hA : ∀ i j, ContDiffAt ℝ n (fun y => A y i j) z) (hdet : (A z).det ≠ 0)
    (i j : Fin 4) : ContDiffAt ℝ n (fun y => (A y)⁻¹ i j) z := by
  have hinv : ContDiffAt ℝ n (fun y => ((A y).det)⁻¹) z :=
    (heatFamilyMatrixDeterminant_contDiffAt n A z hA).inv hdet
  have hadj : ContDiffAt ℝ n (fun y => (A y).adjugate i j) z := by
    simp only [Matrix.adjugate_apply]
    apply heatFamilyMatrixDeterminant_contDiffAt
    intro r s
    by_cases hr : r = j
    · subst r
      simpa only [Matrix.updateRow_self] using
        (contDiffAt_const : ContDiffAt ℝ n
          (fun _ : HeatRadialFrameSpace => (Pi.single i (1 : ℝ) : Fin 4 → ℝ) s) z)
    · simpa only [Matrix.updateRow_ne hr] using hA r s
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    using hinv.mul hadj

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Levi-Civita connection of the common radial-frame family varies
jointly with normal vector, center and initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatFamilyConnection (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (i : Fin 4)
    (z : HeatRadialFrameSpace) : Mat4 :=
  (P z).2⁻¹ * ((heatFamilyPartial P i z).2 +
    (∑ r : Fin 4, (heatFamilyPartial P i z).1 r •
      connectionMatrix g c r (P z).1) * (P z).2)

theorem heatFamilyConnection_slice (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (z : HeatRadialFrameSpace) (hP : DifferentiableAt ℝ P z) (i : Fin 4) :
    heatFamilyConnection g c P i z =
      heatNormalFrameConnection g c (fun x => P (x, z.2)) i z.1 := by
  simp only [heatFamilyConnection, heatNormalFrameConnection,
    heatFamilyPartial_slice P z hP i]

theorem heatFamilyConnection_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 1 : ℕ) P z)
    (hz : (P z).1 ∈ (chartAt FourSpace c).target) (hdet : (P z).2.det ≠ 0)
    (i j k : Fin 4) : ContDiffAt ℝ n (fun y => heatFamilyConnection g c P i y j k) z := by
  have hP0 : ContDiffAt ℝ n P z := hP.of_le (by exact_mod_cast Nat.le_succ n)
  have hE (a b : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2 a b) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP0.snd a) b
  have hEi (a b : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2⁻¹ a b) z :=
    heatFamilyMatrixInverse_contDiffAt n (fun y => (P y).2) z hE hdet a b
  have hD := heatFamilyPartial_contDiffAt n P z hP i
  have hDE (a b : Fin 4) : ContDiffAt ℝ n (fun y => (heatFamilyPartial P i y).2 a b) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hD.snd a) b
  have hDZ (a : Fin 4) : ContDiffAt ℝ n (fun y => (heatFamilyPartial P i y).1 a) z := by
    let π : FourSpace →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) a
    exact π.contDiff.contDiffAt.comp z hD.fst
  have hΓ (r a b : Fin 4) : ContDiffAt ℝ n
      (fun y => christoffel g c (P y).1 a r b) z := by
    exact ContDiffAt.comp (f := fun y => (P y).1)
      (g := fun w => christoffel g c w a r b) z
      ((christoffel_contDiffAt g c (P z).1 hz
        (metricInChart_posDef g c (P z).1 hz).det_pos.ne' a r b).of_le (by first | simp | exact_mod_cast le_top)) hP0.fst
  change ContDiffAt ℝ n (fun y => ∑ l : Fin 4, (P y).2⁻¹ j l *
    ((heatFamilyPartial P i y).2 l k +
      ∑ a : Fin 4, (∑ r : Fin 4, (heatFamilyPartial P i y).1 r *
        christoffel g c (P y).1 l r a) * (P y).2 a k)) z
  apply ContDiffAt.sum
  intro l _
  apply (hEi j l).mul
  apply (hDE l k).add
  apply ContDiffAt.sum
  intro a _
  exact (ContDiffAt.sum (fun r _ => (hDZ r).mul (hΓ r l a))).mul (hE a k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The four derivatives of the actual inverse normal chart needed to
transport the local parametrix and its cutoff to the manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heat_normal_inverse_four (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (c : M) (x : FourSpace)
    (C : OpenPartialHomeomorph FourSpace M) (hx : x ∈ C.source)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hc : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hF : ContDiffAt ℝ 4 (fun v => chartAt FourSpace c (frameExponential g o e v)) x)
    (hL : IsUnit (fderiv ℝ (fun v => chartAt FourSpace c (frameExponential g o e v)) x)) :
    ContMDiffAt I4 I4 4 C.symm (frameExponential g o e x) := by
  let F := fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v)
  let E : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hE : (E : FourSpace →L[ℝ] FourSpace) = fderiv ℝ F x := hL.unit_spec
  have hder : HasFDerivAt F (E : FourSpace →L[ℝ] FourSpace) x := by
    rw [hE]
    exact (hF.differentiableAt (by norm_num)).hasFDerivAt
  let hf := hF.hasStrictFDerivAt' hder (by norm_num)
  let H := fun z : FourSpace => C.symm ((chartAt FourSpace c).symm z)
  have hleft : ∀ᶠ v in 𝓝 x, H (F v) = v := by
    have hnear := (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hc)
    filter_upwards [C.open_source.mem_nhds hx, hnear] with v hv hvc
    change C.symm ((chartAt FourSpace c).symm
      (chartAt FourSpace c (frameExponential g o e v))) = v
    rw [(chartAt FourSpace c).left_inv hvc, ← hC hv]
    exact C.left_inv hv
  have heq := hf.localInverse_unique hleft
  have hH : ContDiffAt ℝ 4 H (F x) :=
    (hF.to_localInverse hder (by norm_num)).congr_of_eventuallyEq heq
  have hchart : ContMDiffAt I4 I4 4 (chartAt FourSpace c) (frameExponential g o e x) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) hc
  have h := hH.contMDiffAt.comp (frameExponential g o e x) hchart
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace c).open_source.mem_nhds hc] with y hy
  change C.symm y = C.symm ((chartAt FourSpace c).symm (chartAt FourSpace c y))
  rw [(chartAt FourSpace c).left_inv hy]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finiteness and boundedness of the actual Riemannian distance on the
connected compact manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M]

theorem metricEDistance_continuous (g : SmoothMetric M) :
    Continuous (fun p : M × M => metricEDistance g p.1 p.2) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  exact continuous_edist

theorem metricEDistance_ne_top [PreconnectedSpace M] (g : SmoothMetric M) (x y : M) :
    metricEDistance g x y ≠ (⊤ : ℝ≥0∞) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  have hclopen : IsClopen (eball x (⊤ : ℝ≥0∞)) :=
    ⟨isClosed_eball_top, isOpen_eball⟩
  have heq : eball x (⊤ : ℝ≥0∞) = univ :=
    hclopen.eq_univ ⟨x, mem_eball_self (by simp)⟩
  have hy : y ∈ eball x (⊤ : ℝ≥0∞) := heq ▸ mem_univ y
  have hlt : edist y x < (⊤ : ℝ≥0∞) := hy
  change edist x y ≠ (⊤ : ℝ≥0∞)
  rw [edist_comm]
  exact hlt.ne

theorem metricEDistance_toReal_continuous [PreconnectedSpace M] (g : SmoothMetric M) :
    Continuous (fun p : M × M => (metricEDistance g p.1 p.2).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hp : ContinuousAt (fun q : M × M => metricEDistance g q.1 q.2) p :=
    (metricEDistance_continuous g).continuousAt
  exact ContinuousAt.comp (f := fun q : M × M => metricEDistance g q.1 q.2) (x := p)
    (ENNReal.continuousAt_toReal (metricEDistance_ne_top g p.1 p.2)) hp

theorem metricEDistance_uniform_bound [PreconnectedSpace M] [CompactSpace M]
    (g : SmoothMetric M) (x : M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : M, metricEDistance g x y ≤ ENNReal.ofReal D := by
  have hc : Continuous (fun y : M => (metricEDistance g x y).toReal) :=
    (metricEDistance_toReal_continuous g).comp (continuous_const.prodMk continuous_id)
  obtain ⟨y, _, hmax⟩ := isCompact_univ.exists_isMaxOn ⟨x, mem_univ x⟩ hc.continuousOn
  refine ⟨(metricEDistance g x y).toReal, ENNReal.toReal_nonneg, fun z => ?_⟩
  rw [← ENNReal.ofReal_toReal (metricEDistance_ne_top g x z)]
  exact ENNReal.ofReal_le_ofReal (hmax (mem_univ z))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual cut time is the last time at which a radial geodesic
minimizes distance from its base. Its existence follows from local
minimization, compactness and the metric triangle inequality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def frameMinimizingTimes (g : SmoothMetric M) (e : FrameBundle g) : Set ℝ :=
  {t | 0 ≤ t ∧ metricEDistance g e.base (frameGeodesic g 0 e t) = ENNReal.ofReal t}

theorem frameMinimizingTimes_zero (g : SmoothMetric M) (e : FrameBundle g) :
    0 ∈ frameMinimizingTimes g e := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  refine ⟨le_rfl, ?_⟩
  simp only [frameGeodesic, parallelFrameFlowMap_zero, ENNReal.ofReal_zero]
  exact Manifold.riemannianEDist_self

theorem frameMinimizingTimes_closed (g : SmoothMetric M) (e : FrameBundle g) :
    IsClosed (frameMinimizingTimes g e) := by
  apply IsClosed.inter (isClosed_Ici : IsClosed (Ici (0 : ℝ)))
  exact isClosed_eq ((metricEDistance_continuous g).comp
    (continuous_const.prodMk (frameGeodesic_continuous g 0 e))) ENNReal.continuous_ofReal

theorem frameMinimizingTimes_downward (g : SmoothMetric M) (e : FrameBundle g)
    {s t : ℝ} (ht : t ∈ frameMinimizingTimes g e) (hs : 0 ≤ s) (hst : s ≤ t) :
    s ∈ frameMinimizingTimes g e := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hu : metricEDistance g e.base (frameGeodesic g 0 e s) ≤ ENNReal.ofReal s := by
    simpa only [abs_of_nonneg hs] using frameGeodesic_distance_from_start g 0 e s
  have hfin : metricEDistance g e.base (frameGeodesic g 0 e s) ≠ (⊤ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  have hseg : metricEDistance g (frameGeodesic g 0 e s) (frameGeodesic g 0 e t) ≤
      ENNReal.ofReal (t - s) := by
    simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using
      frameGeodesic_distance_le g 0 e s t
  have htri : ENNReal.ofReal t ≤
      metricEDistance g e.base (frameGeodesic g 0 e s) + ENNReal.ofReal (t - s) := by
    rw [← ht.2]
    exact (Manifold.riemannianEDist_triangle (I := I4) (x := e.base)
      (y := frameGeodesic g 0 e s) (z := frameGeodesic g 0 e t)).trans
        (add_le_add le_rfl hseg)
  refine ⟨hs, le_antisymm hu ?_⟩
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mpr
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.ofReal_ne_top⟩) htri
  rw [ENNReal.toReal_ofReal ht.1, ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hst)] at hreal
  linarith

variable [PreconnectedSpace M]

theorem frameMinimizingTimes_bddAbove (g : SmoothMetric M) (e : FrameBundle g) :
    BddAbove (frameMinimizingTimes g e) := by
  obtain ⟨D, hD, hbound⟩ := metricEDistance_uniform_bound g e.base
  refine ⟨D, fun t ht => ?_⟩
  exact (ENNReal.ofReal_le_ofReal_iff hD).mp (ht.2 ▸ hbound (frameGeodesic g 0 e t))

def actualCutTime (g : SmoothMetric M) (e : FrameBundle g) : ℝ :=
  sSup (frameMinimizingTimes g e)

theorem actualCutTime_mem (g : SmoothMetric M) (e : FrameBundle g) :
    actualCutTime g e ∈ frameMinimizingTimes g e :=
  (frameMinimizingTimes_closed g e).csSup_mem ⟨0, frameMinimizingTimes_zero g e⟩
    (frameMinimizingTimes_bddAbove g e)

theorem frameMinimizingTimes_eq_Icc (g : SmoothMetric M) (e : FrameBundle g) :
    frameMinimizingTimes g e = Icc 0 (actualCutTime g e) := by
  ext t
  constructor
  · intro ht
    exact ⟨ht.1, le_csSup (frameMinimizingTimes_bddAbove g e) ht⟩
  · intro ht
    exact frameMinimizingTimes_downward g e (actualCutTime_mem g e) ht.1 ht.2

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness gives a nearest point on a metric sphere. Every path to
an exterior endpoint crosses that sphere, so the nearest point splits
the actual Riemannian distance exactly. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [CompactSpace M] in
theorem metric_path_crosses_sphere (g : SmoothMetric M) (p q : M)
    (γ : ℝ → M) (hγ : Continuous γ) (hstart : γ 0 = p) (hend : γ 1 = q)
    (r : ℝ) (hr : 0 ≤ r) (hrd : r ≤ (metricEDistance g p q).toReal) :
    ∃ t ∈ Icc (0 : ℝ) 1, metricEDistance g p (γ t) = ENNReal.ofReal r := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let F := fun t => (metricEDistance g p (γ t)).toReal
  have hF : Continuous F := (metricEDistance_toReal_continuous g).comp
    (continuous_const.prodMk hγ)
  have h0 : F 0 = 0 := by
    change (metricEDistance g p (γ 0)).toReal = 0
    rw [hstart]
    simp [metricEDistance, Manifold.riemannianEDist_self]
  have h1 : F 1 = (metricEDistance g p q).toReal := by dsimp [F]; rw [hend]
  obtain ⟨t, ht, htr⟩ := intermediate_value_Icc zero_le_one hF.continuousOn
    (show r ∈ Icc (F 0) (F 1) by rw [h0, h1]; exact ⟨hr, hrd⟩)
  refine ⟨t, ht, ?_⟩
  rw [← ENNReal.ofReal_toReal (metricEDistance_ne_top g p (γ t))]
  exact congrArg ENNReal.ofReal htr

theorem exists_metricDistance_split (g : SmoothMetric M) (p q : M)
    (r : ℝ) (hr : 0 ≤ r) (hrd : r ≤ (metricEDistance g p q).toReal) :
    ∃ z : M, metricEDistance g p z = ENNReal.ofReal r ∧
      metricEDistance g p q = ENNReal.ofReal r + metricEDistance g z q := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let S := {z | metricEDistance g p z = ENNReal.ofReal r}
  have hS : IsCompact S := (isClosed_eq ((metricEDistance_continuous g).comp
    (continuous_const.prodMk continuous_id)) continuous_const).isCompact
  have hSne : S.Nonempty := by
    have hsmall : metricEDistance g p q < ENNReal.ofReal ((metricEDistance g p q).toReal + 1) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal (metricEDistance_ne_top g p q)]
      apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      linarith
    obtain ⟨γ, ha, hb, hγ, _, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hsmall zero_lt_one
    obtain ⟨t, _, ht⟩ := metric_path_crosses_sphere g p q γ hγ.continuous ha hb r hr hrd
    exact ⟨γ t, ht⟩
  have hc : Continuous (fun z : M => (metricEDistance g z q).toReal) :=
    (metricEDistance_toReal_continuous g).comp (continuous_id.prodMk continuous_const)
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn hSne hc.continuousOn
  have hmin' : ∀ w ∈ S, metricEDistance g z q ≤ metricEDistance g w q := by
    intro w hw
    exact (ENNReal.toReal_le_toReal (metricEDistance_ne_top g z q)
      (metricEDistance_ne_top g w q)).mp (hmin hw)
  refine ⟨z, hz, le_antisymm ?_ ?_⟩
  · have htri : metricEDistance g p q ≤ metricEDistance g p z + metricEDistance g z q :=
      Manifold.riemannianEDist_triangle
    rwa [show metricEDistance g p z = ENNReal.ofReal r from hz] at htri
  · by_contra h
    have hlt : metricEDistance g p q < ENNReal.ofReal r + metricEDistance g z q :=
      lt_of_not_ge h
    obtain ⟨γ, ha, hb, hγ, hlen, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hlt zero_lt_one
    obtain ⟨t, ht, htr⟩ := metric_path_crosses_sphere g p q γ hγ.continuous ha hb r hr hrd
    have hleft : ENNReal.ofReal r ≤ Manifold.pathELength I4 γ 0 t := by
      have hh := Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn ha rfl ht.1
      change metricEDistance g p (γ t) ≤ Manifold.pathELength I4 γ 0 t at hh
      rwa [htr] at hh
    have hright : metricEDistance g z q ≤ Manifold.pathELength I4 γ t 1 :=
      (hmin' (γ t) htr).trans
        (Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn rfl hb ht.2)
    have hsum := add_le_add hleft hright
    rw [Manifold.pathELength_add ht.1 ht.2] at hsum
    exact (not_lt_of_ge hsum) hlen

end
end PositiveEinsteinFour.Geometry
end


section

/-! Curvature of the coordinate connection pulled back by the actual
finite-regularity normal-coordinate map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatWeightedConnection (F : FourSpace → FourSpace)
    (C : Fin 4 → FourSpace → Mat4) (i : Fin 4) (x : FourSpace) : Mat4 :=
  weightedConnection (jacobianMatrix F x) (fun a => C a (F x)) i

theorem heatWeightedConnection_partial
    (F : FourSpace → FourSpace) (C : Fin 4 → FourSpace → Mat4)
    (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hC : ∀ a r s, DifferentiableAt ℝ (fun z => C a z r s) (F x))
    (i j : Fin 4) :
    matrixPartial (heatWeightedConnection F C j) i x =
      weightedConnectionDerivative (jacobianMatrix F x)
        (fun r => matrixPartial (jacobianMatrix F) r x)
        (fun a => C a (F x)) (fun b a => matrixPartial (C a) b (F x)) i j := by
  let J := jacobianMatrix F
  let A := fun a z => C a (F z)
  have hdF := hF.differentiableAt (by norm_num)
  have hJ (a : Fin 4) : DifferentiableAt ℝ (fun z => J z a j) x :=
    (heatJacobian_entry_regular 1 hF a j).differentiableAt one_ne_zero
  have hA (a r s : Fin 4) : DifferentiableAt ℝ (fun z => A a z r s) x :=
    (hC a r s).comp x hdF
  change matrixPartial (fun z => ∑ a, J z a j • A a z) i x = _
  rw [matrixPartial_sum_four (fun a z => J z a j • A a z) x
    (fun a r s => (hJ a).mul (hA a r s)) i]
  have hs (a : Fin 4) : matrixPartial (fun z => J z a j • A a z) i x =
      partialDeriv (fun z => J z a j) i x • A a x +
        J x a j • matrixPartial (A a) i x :=
    matrixPartial_smul _ _ x (hJ a) (hA a) i
  have hc (a : Fin 4) : matrixPartial (A a) i x =
      ∑ b, J x b i • matrixPartial (C a) b (F x) :=
    matrixPartial_comp hdF (hC a) i
  simp only [hs, hc]
  rfl

theorem heatWeightedConnection_curvature
    (F : FourSpace → FourSpace) (C : Fin 4 → FourSpace → Mat4)
    (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hC : ∀ a r s, DifferentiableAt ℝ (fun z => C a z r s) (F x))
    (i j : Fin 4) :
    matrixPartial (heatWeightedConnection F C j) i x -
        matrixPartial (heatWeightedConnection F C i) j x +
      heatWeightedConnection F C i x * heatWeightedConnection F C j x -
        heatWeightedConnection F C j x * heatWeightedConnection F C i x =
      ∑ a, ∑ b, (jacobianMatrix F x a i * jacobianMatrix F x b j) •
        (matrixPartial (C b) a (F x) - matrixPartial (C a) b (F x) +
          C a (F x) * C b (F x) - C b (F x) * C a (F x)) := by
  rw [heatWeightedConnection_partial F C x hF hC,
    heatWeightedConnection_partial F C x hF hC]
  exact weightedConnection_curvature _ _ _ _
    (fun a b r => heatJacobian_partials_commute hF r a b) i j

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatWeightedConnection_actual_curvature (g : SmoothMetric M) (c : M)
    (F : FourSpace → FourSpace) (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hx : F x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    matrixPartial (heatWeightedConnection F (connectionMatrix g c) j) i x -
        matrixPartial (heatWeightedConnection F (connectionMatrix g c) i) j x +
      heatWeightedConnection F (connectionMatrix g c) i x *
        heatWeightedConnection F (connectionMatrix g c) j x -
      heatWeightedConnection F (connectionMatrix g c) j x *
        heatWeightedConnection F (connectionMatrix g c) i x =
      ∑ a, ∑ b, (jacobianMatrix F x a i * jacobianMatrix F x b j) •
        coordinateCurvatureMatrix g c a b (F x) := by
  apply heatWeightedConnection_curvature F (connectionMatrix g c) x hF
  intro a r s
  exact (christoffel_contDiffAt g c (F x) hx
    (metricInChart_posDef g c (F x) hx).det_pos.ne' r a s).differentiableAt (by first | simp | exact_mod_cast le_top)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real-valued distance lemmas for the actual Riemannian path metric on
our connected compact manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [PreconnectedSpace M]

def metricDistance (g : SmoothMetric M) (p q : M) : ℝ := (metricEDistance g p q).toReal

omit [T3Space M] [PreconnectedSpace M] in
theorem metricDistance_nonneg (g : SmoothMetric M) (p q : M) :
    0 ≤ metricDistance g p q := ENNReal.toReal_nonneg

theorem ofReal_metricDistance (g : SmoothMetric M) (p q : M) :
    ENNReal.ofReal (metricDistance g p q) = metricEDistance g p q :=
  ENNReal.ofReal_toReal (metricEDistance_ne_top g p q)

theorem metricDistance_eq_iff (g : SmoothMetric M) (p q : M) {r : ℝ} (hr : 0 ≤ r) :
    metricDistance g p q = r ↔ metricEDistance g p q = ENNReal.ofReal r := by
  constructor
  · intro h
    rw [← ofReal_metricDistance g p q, h]
  · intro h
    change (metricEDistance g p q).toReal = r
    rw [h, ENNReal.toReal_ofReal hr]

theorem metricDistance_triangle (g : SmoothMetric M) (p q r : M) :
    metricDistance g p r ≤ metricDistance g p q + metricDistance g q r := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  have h : metricEDistance g p r ≤ metricEDistance g p q + metricEDistance g q r :=
    Manifold.riemannianEDist_triangle
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨metricEDistance_ne_top g p q, metricEDistance_ne_top g q r⟩) h
  rwa [ENNReal.toReal_add (metricEDistance_ne_top g p q) (metricEDistance_ne_top g q r)] at ht

theorem metricDistance_continuous (g : SmoothMetric M) :
    Continuous (fun p : M × M => metricDistance g p.1 p.2) :=
  metricEDistance_toReal_continuous g

theorem metricDistance_eq_zero_iff (g : SmoothMetric M) (p q : M) :
    metricDistance g p q = 0 ↔ p = q := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  rw [metricDistance_eq_iff g p q le_rfl, ENNReal.ofReal_zero]
  change edist p q = 0 ↔ p = q
  exact edist_eq_zero

variable [CompactSpace M]

theorem exists_metricDistance_real_split (g : SmoothMetric M) (p q : M)
    (r : ℝ) (hr : 0 ≤ r) (hrd : r ≤ metricDistance g p q) :
    ∃ z, metricDistance g p z = r ∧ metricDistance g p q = r + metricDistance g z q := by
  obtain ⟨z, hz, hsplit⟩ := exists_metricDistance_split g p q r hr hrd
  refine ⟨z, (metricDistance_eq_iff g p z hr).mpr hz, ?_⟩
  have h := congrArg ENNReal.toReal hsplit
  simpa only [metricDistance, ENNReal.toReal_add ENNReal.ofReal_ne_top
    (metricEDistance_ne_top g z q), ENNReal.toReal_ofReal hr] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint curvature and two-form connection coefficients of the actual
normal-frame family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatFamilyCurvature (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace) :
    CovariantCoordinates 4 := frameTensor (P z).2 (curvatureCoordinates g c (P z).1)

def heatFamilyPotential (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace) :
    TwoFormMatrix := twoFormPotentialMatrix (heatFamilyCurvature g c P z)

def heatFamilyTwoFormConnection (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (i : Fin 4)
    (z : HeatRadialFrameSpace) : TwoFormMatrix :=
  heatTwoFormConnectionMatrix (heatFamilyConnection g c P i z)

theorem heatFamilyTwoFormConnection_slice (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (z : HeatRadialFrameSpace) (hP : DifferentiableAt ℝ P z) (i : Fin 4) :
    heatFamilyTwoFormConnection g c P i z =
      heatTwoFormConnection g c (fun x => P (x, z.2)) i z.1 := by
  rw [heatFamilyTwoFormConnection, heatFamilyConnection_slice g c P z hP i]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiating the actual moving-frame connection law identifies
its curvature with the pullback of Levi-Civita curvature. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_matrixPartial_comm_two (E : FourSpace → Mat4) (x : FourSpace)
    (hE : ∀ r s, ContDiffAt ℝ 2 (fun z => E z r s) x) (i j : Fin 4) :
    matrixPartial (matrixPartial E j) i x = matrixPartial (matrixPartial E i) j x := by
  ext r s
  have hd := ((hE r s).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he (a b : Fin 4) :
      partialDeriv (partialDeriv (fun z => E z r s) b) a x =
        fderiv ℝ (fderiv ℝ (fun z => E z r s)) x (coordinateVector a) (coordinateVector b) := by
    unfold partialDeriv
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  change partialDeriv (partialDeriv (fun z => E z r s) j) i x =
    partialDeriv (partialDeriv (fun z => E z r s) i) j x
  rw [he, he]
  exact ((hE r s).isSymmSndFDerivAt (by norm_num)).eq _ _

theorem heat_connection_law_derivative
    (E C U : FourSpace → Mat4) (x : FourSpace)
    (hE : ∀ r s, ContDiffAt ℝ 2 (fun z => E z r s) x)
    (hC : ∀ r s, DifferentiableAt ℝ (fun z => C z r s) x)
    (hU : ∀ r s, DifferentiableAt ℝ (fun z => U z r s) x)
    (j : Fin 4)
    (hLaw : (fun z => E z * C z) =ᶠ[𝓝 x]
      (fun z => matrixPartial E j z + U z * E z)) (i : Fin 4) :
    matrixPartial E i x * C x + E x * matrixPartial C i x =
      matrixPartial (matrixPartial E j) i x + matrixPartial U i x * E x +
        U x * matrixPartial E i x := by
  have hEd (r s : Fin 4) := (hE r s).differentiableAt (by norm_num)
  have hP (r s : Fin 4) :
      DifferentiableAt ℝ (fun z => matrixPartial E j z r s) x :=
    (((hE r s).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt one_ne_zero
  have hprod (r s : Fin 4) : DifferentiableAt ℝ (fun z => (U z * E z) r s) x := by
    change DifferentiableAt ℝ (fun z => ∑ a, U z r a * E z a s) x
    exact DifferentiableAt.fun_sum (fun a _ => (hU r a).mul (hEd a s))
  have h := matrixPartial_congr hLaw i
  rw [matrixPartial_mul E C x hEd hC i,
    matrixPartial_add (matrixPartial E j) (fun z => U z * E z) x hP hprod i,
    matrixPartial_mul U E x hU hEd i] at h
  simpa only [add_assoc] using h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.connection_law (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ Metric.ball 0 D.radius) (i : Fin 4) :
    (D.point x).2 * heatNormalFrameConnection g c D.point i x =
      matrixPartial (fun z => (D.point z).2) i x +
        heatWeightedConnection (fun z => (D.point z).1) (connectionMatrix g c) i x *
          (D.point x).2 := by
  have hdet : IsUnit (D.point x).2.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hh := congrArg Matrix.det (D.orthonormal x hx)
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  rw [heatFrame_matrixPartial D.point x (D.differentiable x hx) i]
  simp_rw [heatWeightedConnection, weightedConnection,
    heatFrame_baseJacobian D.point x (D.differentiable x hx)]
  exact pulledConnection_equation _ _ _ hdet

theorem HeatNormalFrameData.connection_curvature_intertwining
    (D : HeatNormalFrameData g o c e) (i j : Fin 4) :
    (D.point 0).2 *
      (matrixPartial (heatNormalFrameConnection g c D.point j) i 0 -
        matrixPartial (heatNormalFrameConnection g c D.point i) j 0 +
        heatNormalFrameConnection g c D.point i 0 * heatNormalFrameConnection g c D.point j 0 -
        heatNormalFrameConnection g c D.point j 0 * heatNormalFrameConnection g c D.point i 0) =
      (∑ a, ∑ b, (jacobianMatrix (fun z => (D.point z).1) 0 a i *
        jacobianMatrix (fun z => (D.point z).1) 0 b j) •
          coordinateCurvatureMatrix g c a b (D.point 0).1) * (D.point 0).2 := by
  let E := fun z => (D.point z).2
  let F := fun z => (D.point z).1
  let C := heatNormalFrameConnection g c D.point
  let U := heatWeightedConnection F (connectionMatrix g c)
  have hE (r s : Fin 4) : ContDiffAt ℝ 2 (fun z => E z r s) 0 :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp D.regular.snd r) s).of_le (by norm_num)
  have hF : ContDiffAt ℝ 2 F 0 := D.regular.fst.of_le (by norm_num)
  have hx : F 0 ∈ (chartAt FourSpace c).target :=
    D.in_chart 0 (Metric.mem_ball_self D.radius_pos)
  have hU (a r s : Fin 4) : DifferentiableAt ℝ (fun z => U a z r s) 0 := by
    change DifferentiableAt ℝ (fun z => ∑ b,
      jacobianMatrix F z b a * connectionMatrix g c b (F z) r s) 0
    apply DifferentiableAt.fun_sum
    intro b _
    apply ((heatJacobian_entry_regular 1 hF b a).differentiableAt one_ne_zero).mul
    exact ((christoffel_contDiffAt g c (F 0) hx
      (metricInChart_posDef g c (F 0) hx).det_pos.ne' r b s).differentiableAt
        (by first | simp | exact_mod_cast le_top)).comp 0 (hF.differentiableAt (by norm_num))
  have hC (a r s : Fin 4) : DifferentiableAt ℝ (fun z => C a z r s) 0 :=
    (D.connection_regular a r s).differentiableAt (by norm_num)
  have hLaw (a : Fin 4) : (fun z => E z * C a z) =ᶠ[𝓝 0]
      (fun z => matrixPartial E a z + U a z * E z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos] with z hz
    exact D.connection_law z hz a
  have hder (a b : Fin 4) := heat_connection_law_derivative E (C b) (U b) 0
    hE (hC b) (hU b) b (hLaw b) a
  have hcomm := heat_matrixPartial_comm_two E 0 hE i j
  have hc := curvature_intertwining_of_connection _ _ _ _ _ _ _ _ _ _ _ _
    (hLaw i).self_of_nhds (hLaw j).self_of_nhds (hder i j)
    (by simpa only [hcomm] using hder j i)
  rw [heatWeightedConnection_actual_curvature g c F 0 hF hx i j] at hc
  exact hc

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual kinetic energy bounds for C1 curve segments.  The elementary
square inequality suffices at a unit-speed minimizing reference curve. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal BigOperators

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def metricIntervalSpeed (g : SmoothMetric M) (γ : ℝ → M) (a b t : ℝ) : ℝ :=
  metricTangentNorm g (γ t) (mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc a b) t 1)

def metricCurveEnergy (g : SmoothMetric M) (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, (1 / 2 : ℝ) * (metricIntervalSpeed g γ a b t) ^ 2

theorem metricIntervalSpeed_continuousOn (g : SmoothMetric M) (γ : ℝ → M)
    {a b : ℝ} (hab : a < b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc a b)) :
    ContinuousOn (metricIntervalSpeed g γ a b) (Icc a b) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hinput : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent ∞
      (fun t : ℝ => (⟨t, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hv : ContinuousOn (fun t =>
      (⟨γ t, mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc a b) t 1⟩ : TangentBundle I4 M))
      (Icc a b) :=
    (hγ.continuousOn_tangentMapWithin le_rfl (uniqueDiffOn_Icc hab).uniqueMDiffOn).comp
      hinput.continuous.continuousOn (fun _ ht => ht)
  have hi := hv.inner_bundle hv
  have hs := Real.continuous_sqrt.comp_continuousOn hi
  change ContinuousOn (fun t => Real.sqrt (g.inner (γ t)
    (mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc a b) t 1)
    (mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc a b) t 1))) (Icc a b) at hs
  simpa only [metricIntervalSpeed, metricTangentNorm_eq_sqrt] using! hs

theorem metricIntervalSpeed_nonneg (g : SmoothMetric M) (γ : ℝ → M)
    (a b t : ℝ) : 0 ≤ metricIntervalSpeed g γ a b t := by
  rw [metricIntervalSpeed, metricTangentNorm_eq_sqrt]
  exact Real.sqrt_nonneg _

theorem metric_pathELength_eq_ofReal_integral (g : SmoothMetric M) (γ : ℝ → M)
    {a b : ℝ} (hab : a < b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc a b)) :
    (let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩;
      Manifold.pathELength I4 γ a b) =
      ENNReal.ofReal (∫ t in a..b, metricIntervalSpeed g γ a b t) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  change (∫⁻ t in Icc a b, metricTangentENorm g (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc a b) t 1)) = _
  simp only [metricTangentENorm_eq_ofReal]
  change (∫⁻ t in Icc a b, ENNReal.ofReal (metricIntervalSpeed g γ a b t)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal
    (metricIntervalSpeed_continuousOn g γ hab hγ).integrableOn_Icc
    (Filter.Eventually.of_forall (metricIntervalSpeed_nonneg g γ a b))]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]

variable [T3Space M] [PreconnectedSpace M]

/-- A curve segment joining two points costs at least their distance minus
half its parameter duration, in the actual Riemannian kinetic energy. -/
theorem metricDistance_le_curveEnergy_add (g : SmoothMetric M) (γ : ℝ → M)
    {a b : ℝ} (hab : a < b) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc a b)) :
    metricDistance g (γ a) (γ b) ≤ metricCurveEnergy g γ a b + (b - a) / 2 := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hl : metricEDistance g (γ a) (γ b) ≤
      ENNReal.ofReal (∫ t in a..b, metricIntervalSpeed g γ a b t) := by
    calc
      _ ≤ Manifold.pathELength I4 γ a b :=
        Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab.le
      _ = _ := metric_pathELength_eq_ofReal_integral g γ hab hγ
  have hnonneg : 0 ≤ ∫ t in a..b, metricIntervalSpeed g γ a b t :=
    intervalIntegral.integral_nonneg hab.le (fun t _ => metricIntervalSpeed_nonneg g γ a b t)
  rw [← ofReal_metricDistance g (γ a) (γ b), ENNReal.ofReal_le_ofReal_iff hnonneg] at hl
  exact hl.trans (integral_speed_le_energy_add _ hab.le
    (metricIntervalSpeed_continuousOn g γ hab hγ))


/-- The triangle inequality along a finite chain of actual points. -/
theorem metricDistance_le_sum_chain (g : SmoothMetric M) (p : ℕ → M) (n : ℕ) :
    metricDistance g (p 0) (p n) ≤
      ∑ i ∈ Finset.range n, metricDistance g (p i) (p (i + 1)) := by
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact le_of_eq ((metricDistance_eq_zero_iff g (p 0) (p 0)).mpr rfl)
  | succ n ih =>
      rw [Finset.sum_range_succ]
      exact (metricDistance_triangle g (p 0) (p n) (p (n + 1))).trans
        (_root_.add_le_add ih le_rfl)

/-- A finite piecewise C1 competitor with matching endpoints satisfies the
same energy bound.  There is no regularity requirement at its corners. -/
theorem finite_piece_metric_energy_lower (g : SmoothMetric M) (n : ℕ)
    (p : ℕ → M) (t : ℕ → ℝ) (γ : ℕ → ℝ → M)
    (ht : ∀ i < n, t i < t (i + 1))
    (hγ : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I4 1 (γ i) (Icc (t i) (t (i + 1))))
    (hleft : ∀ i < n, γ i (t i) = p i)
    (hright : ∀ i < n, γ i (t (i + 1)) = p (i + 1)) :
    metricDistance g (p 0) (p n) - (t n - t 0) / 2 ≤
      ∑ i ∈ Finset.range n, metricCurveEnergy g (γ i) (t i) (t (i + 1)) := by
  have hp : ∀ i ∈ Finset.range n,
      metricDistance g (p i) (p (i + 1)) ≤
        metricCurveEnergy g (γ i) (t i) (t (i + 1)) + (t (i + 1) - t i) / 2 := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simpa only [hleft i hi', hright i hi'] using
      metricDistance_le_curveEnergy_add g (γ i) (ht i hi') (hγ i hi')
  have hs := (metricDistance_le_sum_chain g p n).trans (Finset.sum_le_sum hp)
  rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_range_sub] at hs
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identification of the actual Riemannian kinetic energy of a chart
curve with the coordinate energy used in the second-variation calculation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chart_curve_contMDiffOn (c : M) (x : ℝ → FourSpace) {a b : ℝ}
    (hx : ContDiffOn ℝ 1 x (Icc a b))
    (hz : MapsTo x (Icc a b) (chartAt FourSpace c).target) :
    ContMDiffOn 𝓘(ℝ, ℝ) I4 1 (fun t => (chartAt FourSpace c).symm (x t)) (Icc a b) :=
  (contMDiffOn_chart_symm (I := I4) (x := c) (n := 1)).comp hx.contMDiffOn hz

theorem chart_curve_derivativeWithin (c : M) (x : ℝ → FourSpace)
    {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (hz : x t ∈ (chartAt FourSpace c).target) (v : JacobiCoordinateVector)
    (hx : HasDerivWithinAt x (WithLp.toLp 2 v) (Icc a b) t) :
    mfderivWithin 𝓘(ℝ, ℝ) I4 (fun s => (chartAt FourSpace c).symm (x s))
      (Icc a b) t 1 =
      mfderiv I4 I4 (chartAt FourSpace c).symm (x t) (WithLp.toLp 2 v) := by
  have hu : UniqueDiffWithinAt ℝ (Icc a b) t := uniqueDiffOn_Icc hab t ht
  have hxm : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I4 x (Icc a b) t :=
    hx.differentiableWithinAt.mdifferentiableWithinAt
  have hcomp := mfderiv_comp_mfderivWithin t
    ((mdifferentiable_chart (I := I4) c).symm.mdifferentiableAt hz)
    hxm hu.uniqueMDiffWithinAt
  have hd : mfderivWithin 𝓘(ℝ, ℝ) I4 x (Icc a b) t 1 = WithLp.toLp 2 v := by
    rw [mfderivWithin_eq_fderivWithin, hx.hasFDerivWithinAt.fderivWithin hu]
    exact one_smul ℝ _
  exact (congrArg (fun L => L 1) hcomp).trans
    (congrArg (mfderiv I4 I4 (chartAt FourSpace c).symm (x t)) hd)

theorem chart_curve_energy_density (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (hz : x t ∈ (chartAt FourSpace c).target) (v : JacobiCoordinateVector)
    (hx : HasDerivWithinAt x (WithLp.toLp 2 v) (Icc a b) t) :
    (1 / 2 : ℝ) * (metricIntervalSpeed g
      (fun s => (chartAt FourSpace c).symm (x s)) a b t) ^ 2 =
      chartEnergyDensity g c (x t) v := by
  unfold metricIntervalSpeed
  rw [chart_curve_derivativeWithin c x hab ht hz v hx, metricTangentNorm_eq_sqrt]
  let u := mfderiv I4 I4 (chartAt FourSpace c).symm (x t) (WithLp.toLp 2 v)
  have hnonneg : 0 ≤ g.inner ((chartAt FourSpace c).symm (x t)) u u := by
    by_cases hu : u = 0
    · simp [hu]
    · exact (g.pos _ u hu).le
  rw [Real.sq_sqrt hnonneg]
  exact congrArg (fun r : ℝ => (1 / 2 : ℝ) * r)
    (metricInChart_pairing g c (x t) v v).symm

theorem metricCurveEnergy_chart (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (v : ℝ → JacobiCoordinateVector) {a b : ℝ} (hab : a < b)
    (hz : MapsTo x (Icc a b) (chartAt FourSpace c).target)
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (WithLp.toLp 2 (v t)) (Icc a b) t) :
    metricCurveEnergy g (fun t => (chartAt FourSpace c).symm (x t)) a b =
      ∫ t in a..b, chartEnergyDensity g c (x t) (v t) := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab.le] at ht
  exact chart_curve_energy_density g c x hab ht (hz ht) (v t) (hx t ht)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential differential is arbitrarily close to an
isometry near zero, uniformly in the tangent direction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Filter Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_metric_differential_continuous (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) :
    Continuous (fun p : FourSpace × FourSpace =>
      metricTangentNorm g (frameExponential g o e p.1)
        (mfderiv I4 I4 (frameExponential g o e) p.1 p.2)) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hinput : Continuous (fun p : FourSpace × FourSpace =>
      (⟨p.1, p.2⟩ : TangentBundle I4 FourSpace)) :=
    (tangentBundleModelSpaceHomeomorph I4).symm.continuous
  have hv := ((frameExponential_contMDiff g o e).continuous_tangentMap le_rfl).comp hinput
  have hs := Real.continuous_sqrt.comp (hv.inner_bundle hv)
  change Continuous (fun p : FourSpace × FourSpace =>
    Real.sqrt (g.inner (frameExponential g o e p.1)
      (mfderiv I4 I4 (frameExponential g o e) p.1 p.2)
      (mfderiv I4 I4 (frameExponential g o e) p.1 p.2))) at hs
  simpa only [metricTangentNorm_eq_sqrt] using hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual energy of a unit-speed distance-minimizing geodesic is a
local minimum among finite piecewise C1 variations with fixed endpoints. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metricCurveEnergy_congr (g : SmoothMetric M) {γ η : ℝ → M} {a b : ℝ}
    (hab : a ≤ b) (h : EqOn γ η (Icc a b)) :
    metricCurveEnergy g γ a b = metricCurveEnergy g η a b := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  have hv := congrArg (fun p : TangentBundle I4 M => metricTangentNorm g p.1 p.2)
    (tangentMapWithin_congr h (⟨t, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) ht)
  change metricIntervalSpeed g γ a b t = metricIntervalSpeed g η a b t at hv
  dsimp only
  rw [hv]

variable [T3Space M] [CompactSpace M]

theorem frameGeodesic_intervalSpeed (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    metricIntervalSpeed g (frameGeodesic g k e) a b t = 1 := by
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc a b) t :=
    (uniqueDiffOn_Icc hab t ht).uniqueMDiffWithinAt
  have hd := (frameGeodesic_contMDiff g k e).mdifferentiable one_ne_zero t
  unfold metricIntervalSpeed
  rw [mfderivWithin_eq_mfderiv hu hd, frameGeodesic_mfderiv]
  have hn := metricTangentNorm_eq_sqrt g (parallelFrameFlowMap g k t e).base
    (show TangentSpace I4 (parallelFrameFlowMap g k t e).base from
      (parallelFrameFlowMap g k t e).frame.vector k)
  have h := congrArg Real.sqrt ((parallelFrameFlowMap g k t e).frame.inner_vector_self k)
  have heq := hn.trans (by simpa only [Real.sqrt_one] using! h)
  exact heq

theorem frameGeodesic_energy (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) {a b : ℝ} (hab : a < b) :
    metricCurveEnergy g (frameGeodesic g k e) a b = (b - a) / 2 := by
  have h : metricCurveEnergy g (frameGeodesic g k e) a b =
      ∫ _ in a..b, (1 / 2 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    dsimp only
    rw [frameGeodesic_intervalSpeed g k e hab ht, one_pow, mul_one]
  rw [h, intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one_div]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Endpoint-corrected coordinate variations define genuine C1 manifold
curves, and their coordinate energy is the actual Riemannian energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

/-- Extend the two time fields only for the compactness argument.  The
resulting variation and its jets on the original segment are unchanged. -/
theorem endpointCorrectedPosition_inside_on (x y A B : ℝ → FourSpace)
    {a b : ℝ} (hab : a ≤ b) (hx : ContinuousOn x (Icc a b))
    (hy : ContinuousOn y (Icc a b)) (hA : Continuous A) (hB : Continuous B)
    (hA0 : A 0 = x a) (hB0 : B 0 = x b) (U : Set FourSpace) (hU : IsOpen U)
    (hxU : ∀ t ∈ Icc a b, x t ∈ U) :
    ∃ δ > 0, ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      endpointCorrectedPosition x y A B a b ε t ∈ U := by
  let X := IccExtend hab (fun t : Icc a b => x t)
  let Y := IccExtend hab (fun t : Icc a b => y t)
  have hX : Continuous X := hx.domRestrict.Icc_extend'
  have hY : Continuous Y := hy.domRestrict.Icc_extend'
  have hXe (t : ℝ) (ht : t ∈ Icc a b) : X t = x t := IccExtend_of_mem hab _ ht
  have hYe (t : ℝ) (ht : t ∈ Icc a b) : Y t = y t := IccExtend_of_mem hab _ ht
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  obtain ⟨δ, hδ, hinside⟩ := endpointCorrectedPosition_inside X Y A B a b hX hY hA hB
    (hA0.trans (hXe a ha).symm) (hB0.trans (hXe b hb).symm) U hU
    (fun t ht => (hXe t ht).symm ▸ hxU t ht)
  refine ⟨δ, hδ, fun ε hε t ht => ?_⟩
  have h := hinside ε hε t ht
  simpa only [endpointCorrectedPosition, endpointResidual, hXe t ht, hYe t ht,
    hXe a ha, hXe b hb, hYe a ha, hYe b hb] using h

theorem endpointCorrectedPosition_contDiffOn (x y v w A B : ℝ → FourSpace)
    {a b : ℝ} (hab : a < b) (ε : ℝ)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (v t) t)
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (w t) t)
    (hv : ContinuousOn v (Icc a b)) (hw : ContinuousOn w (Icc a b)) :
    ContDiffOn ℝ 1 (endpointCorrectedPosition x y A B a b ε) (Icc a b) := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) :=
    endpointCorrectedPosition_time x y v w A B a b ε t (hx t ht) (hy t ht)
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)).mpr
  refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, ?_⟩
  have hc : ContinuousOn (endpointCorrectedVelocity x y v w A B a b ε) (Icc a b) :=
    ((hv.add (hw.const_smul ε)).sub continuousOn_const).add continuousOn_const
  apply hc.congr
  intro t ht
  exact (hd t ht).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab t ht)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem endpointCorrected_curve_contMDiffOn (c : M) (x y v w A B : ℝ → FourSpace)
    {a b : ℝ} (hab : a < b) (ε : ℝ)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (v t) t)
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (w t) t)
    (hv : ContinuousOn v (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hz : ∀ t ∈ Icc a b,
      endpointCorrectedPosition x y A B a b ε t ∈ (chartAt FourSpace c).target) :
    ContMDiffOn 𝓘(ℝ, ℝ) I4 1
      (fun t => (chartAt FourSpace c).symm (endpointCorrectedPosition x y A B a b ε t))
      (Icc a b) :=
  chart_curve_contMDiffOn c _ (endpointCorrectedPosition_contDiffOn x y v w A B hab ε
    hx hy hv hw) hz

theorem endpointCorrected_actual_energy (g : SmoothMetric M) (c : M)
    (x y v w A B : ℝ → FourSpace) {a b : ℝ} (hab : a < b) (ε : ℝ)
    (hx : ∀ t ∈ Icc a b, HasDerivAt x (v t) t)
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (w t) t)
    (hz : ∀ t ∈ Icc a b,
      endpointCorrectedPosition x y A B a b ε t ∈ (chartAt FourSpace c).target) :
    metricCurveEnergy g (fun t => (chartAt FourSpace c).symm
      (endpointCorrectedPosition x y A B a b ε t)) a b =
      ∫ t in a..b, chartEnergyDensity g c (endpointCorrectedPosition x y A B a b ε t)
        (WithLp.ofLp (endpointCorrectedVelocity x y v w A B a b ε t)) := by
  apply metricCurveEnergy_chart g c _ _ hab hz
  intro t ht
  simpa only [WithLp.toLp_ofLp] using
    (endpointCorrectedPosition_time x y v w A B a b ε t (hx t ht) (hy t ht)).hasDerivWithinAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! Sharp local distance bounds for the actual exponential. These bounds
will exclude corners in distance-minimizing concatenations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_distance_le_of_differential (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (s : Set FourSpace)
    (hs : Convex ℝ s) (K : ℝ≥0)
    (hK : ∀ z ∈ s, ∀ w : FourSpace, metricTangentNorm g (frameExponential g o e z)
      (mfderiv I4 I4 (frameExponential g o e) z w) ≤ K * ‖w‖)
    (u v : FourSpace) (hu : u ∈ s) (hv : v ∈ s) :
    metricEDistance g (frameExponential g o e u) (frameExponential g o e v) ≤
      K * edist u v := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let α : ℝ →ᴬ[ℝ] FourSpace := ContinuousAffineMap.lineMap u v
  let γ := fun t => frameExponential g o e (α t)
  have hα : ContDiff ℝ 1 α := α.contDiff
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I4 1 γ :=
    (frameExponential_contMDiff g o e).comp hα.contMDiff
  have hαs : MapsTo α (Icc 0 1) s := by
    rw [mapsTo_iff_image_subset, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap]
    exact hs.segment_subset hu hv
  have hstart : γ 0 = frameExponential g o e u := by
    simp [γ, α, ContinuousAffineMap.coe_lineMap_eq]
  have hend : γ 1 = frameExponential g o e v := by
    simp [γ, α, ContinuousAffineMap.coe_lineMap_eq]
  have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      metricTangentENorm g (γ t) (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) ≤
        K * ‖v - u‖ₑ := by
    have hd := frameExponential_curve_derivative g o e α hα t
    have hαd : deriv α t = v - u :=
      (AffineMap.hasDerivAt_lineMap (a := u) (b := v)).deriv
    have hbd := hK (α t) (hαs ht) (v - u)
    have hd' := hd.trans (congrArg (mfderiv I4 I4 (frameExponential g o e) (α t)) hαd)
    have heq := congrArg (metricTangentENorm g (γ t)) hd'
    rw [heq]
    have h := ENNReal.ofReal_le_ofReal hbd
    simpa only [metricTangentENorm_eq_ofReal, ENNReal.ofReal_mul K.coe_nonneg,
      ENNReal.ofReal_coe_nnreal, ofReal_norm] using! h
  calc
    _ ≤ Manifold.pathELength I4 γ 0 1 :=
      Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn hstart hend zero_le_one
    _ = ∫⁻ t in Icc (0 : ℝ) 1,
        metricTangentENorm g (γ t) (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) :=
      Manifold.pathELength_eq_lintegral_mfderiv_Icc
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, (K : ℝ≥0∞) * ‖v - u‖ₑ :=
      setLIntegral_mono' measurableSet_Icc hspeed
    _ = K * edist u v := by
      simp only [lintegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
        Measure.restrict_apply_univ, mul_one, edist_eq_enorm_sub, enorm_sub_rev]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Endpoint data and a common chart neighborhood for an actual normal
variation of one geodesic segment.  All endpoint jets come from the same
intrinsic affine curve, even when adjacent segments use different charts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

structure NormalEndpointJetData (g : SmoothMetric M) (e : FrameBundle g)
    (c : M) (a : Fin 3 → ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  position : ℝ → FourSpace
  first : ℝ → FourSpace
  second : ℝ → FourSpace
  position_continuous : Continuous position
  first_continuous : Continuous first
  second_continuous : Continuous second
  position_zero : position 0 = chartAt FourSpace c e.base
  first_zero : first 0 = WithLp.toLp 2 (frameChartMatrix g c e *ᵥ Fin.cons 0 a)
  second_zero : second 0 = endpointChartSecond e.base c (chartAt FourSpace e.base e.base)
    (normalEndpointDirection g e a) 0
  derivative : ∀ ε ∈ Ioo (-radius) radius,
    HasDerivAt position (first ε) ε ∧ HasDerivAt first (second ε) ε
  inside : ∀ ε ∈ Icc (-radius) radius, position ε ∈ (chartAt FourSpace c).target
  realizes : ∀ ε ∈ Icc (-radius) radius,
    (chartAt FourSpace c).symm (position ε) = normalEndpointCurve g e a ε

end
end PositiveEinsteinFour.Geometry
end


section

/-! A distance-minimizing concatenation of radial geodesics has matching
incoming and outgoing tangent directions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Bundle Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_ray_distance (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (q : Directions) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    metricEDistance g (frameExponential g o e (a • q.val))
      (frameExponential g o e (b • q.val)) ≤ ENNReal.ofReal |b - a| := by
  have h := unitGeodesic_distance_le g o (unitTangentTurn e q) a b
  rwa [← frameExponential_radial g o e q ⟨a, ha⟩,
    ← frameExponential_radial g o e q ⟨b, hb⟩] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Time reversal of the actual complete geodesic, using the oriented
frame rotation by minus the identity in dimension four. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

def reverseDirection : Directions := ⟨-firstDirection.val, by simp [firstDirection.property]⟩

def reverseFrameRotation : OrientedOrthogonalFour := directionOrientedMatrix reverseDirection

theorem reverseFrameRotation_matrix : (orientedToOrthogonal reverseFrameRotation).val = -(1 : Mat4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reverseFrameRotation, orientedToOrthogonal, directionOrientedMatrix,
      directionFrameMatrix, reverseDirection, firstDirection, coordinateVector,
      Matrix.one_apply] <;> norm_num

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameAntipode (g : SmoothMetric M) (e : FrameBundle g) : FrameBundle g :=
  e.rotate (orientedToOrthogonal reverseFrameRotation)

theorem frameAntipode_chart (g : SmoothMetric M) (c : M) (e : FrameBundle g) :
    frameChartMatrix g c (frameAntipode g e) = -frameChartMatrix g c e := by
  rw [frameAntipode, frameChartMatrix_rotate, reverseFrameRotation_matrix, mul_neg, mul_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness and the local no-corner argument give a minimizing radial
geodesic to every point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

def frameDistanceSplitTimes (g : SmoothMetric M) (e : FrameBundle g) (q : M) : Set ℝ :=
  {t | 0 ≤ t ∧ metricDistance g e.base (frameGeodesic g 0 e t) = t ∧
    metricDistance g e.base q = t + metricDistance g (frameGeodesic g 0 e t) q}

theorem frameDistanceSplitTimes_compact (g : SmoothMetric M) (e : FrameBundle g) (q : M) :
    IsCompact (frameDistanceSplitTimes g e q) := by
  have hfirst : Continuous (fun t => metricDistance g e.base (frameGeodesic g 0 e t)) :=
    (metricDistance_continuous g).comp (continuous_const.prodMk (frameGeodesic_continuous g 0 e))
  have hlast : Continuous (fun t => metricDistance g (frameGeodesic g 0 e t) q) :=
    (metricDistance_continuous g).comp ((frameGeodesic_continuous g 0 e).prodMk continuous_const)
  have hclosed : IsClosed (frameDistanceSplitTimes g e q) :=
    isClosed_Ici.inter ((isClosed_eq hfirst continuous_id).inter
      (isClosed_eq continuous_const (continuous_id.add hlast)))
  apply isCompact_Icc.of_isClosed_subset hclosed
  intro t ht
  exact ⟨ht.1, by linarith [metricDistance_nonneg g (frameGeodesic g 0 e t) q, ht.2.2]⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact set of minimizing tangent vectors and its polar
cut-time description. Its exponential image is the whole manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

def actualMinimizingTangentDomain (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : Set FourSpace :=
  {v | metricDistance g e.base (frameExponential g o e v) = ‖v‖}

theorem actualMinimizingTangentDomain_closed (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : IsClosed (actualMinimizingTangentDomain g o e) :=
  isClosed_eq ((metricDistance_continuous g).comp
    (continuous_const.prodMk (frameExponential_continuous g o e))) continuous_norm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous intrinsic Jacobian density for the actual exponential.
Its expression in any output chart is the metric density times the
absolute coordinate determinant. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle Set
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem euclideanMatrix_column (D : FourSpace →ₗ[ℝ] FourSpace) (j : Fin 4) :
    WithLp.toLp 2 (fun i => (Matrix.toEuclideanLin.symm D) i j) = D (coordinateVector j) := by
  have h := congrArg (fun L : FourSpace →ₗ[ℝ] FourSpace => L (coordinateVector j))
    (Matrix.toEuclideanLin.apply_symm_apply D)
  change WithLp.toLp 2 ((Matrix.toEuclideanLin.symm D) *ᵥ
    (Pi.single j 1 : Fin 4 → ℝ)) = D (coordinateVector j) at h
  rw [Matrix.mulVec_single_one] at h
  exact h

theorem frameExponentialJacobian_chart (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (d : M) (v : FourSpace)
    (hd : frameExponential g o e v ∈ (chartAt FourSpace d).source) :
    frameExponentialJacobian g o e v =
      chartVolumeDensity g d (chartAt FourSpace d (frameExponential g o e v)) *
        |LinearMap.det (fderiv ℝ (fun z => chartAt FourSpace d
          (frameExponential g o e z)) v).toLinearMap| := by
  let D := fderiv ℝ (fun z => chartAt FourSpace d (frameExponential g o e z)) v
  let A : Mat4 := Matrix.toEuclideanLin.symm D.toLinearMap
  let G := metricInChart g d (chartAt FourSpace d (frameExponential g o e v))
  have hGram : frameExponentialGram g o e v = Aᵀ * (G * A) := by
    ext i j
    change _ = (fun k => A k i) ⬝ᵥ (G *ᵥ (fun k => A k j))
    have hp := metricInChart_pairing g d (chartAt FourSpace d (frameExponential g o e v))
      (fun k => A k i) (fun k => A k j)
    have hi := euclideanMatrix_column D.toLinearMap i
    have hj := euclideanMatrix_column D.toLinearMap j
    change WithLp.toLp 2 (fun k => A k i) = D (coordinateVector i) at hi
    change WithLp.toLp 2 (fun k => A k j) = D (coordinateVector j) at hj
    rw [hi, hj] at hp
    change (fun k => A k i) ⬝ᵥ (G *ᵥ (fun k => A k j)) =
      g.inner ((chartAt FourSpace d).symm (chartAt FourSpace d (frameExponential g o e v)))
        (chartBackwardOperator d (chartAt FourSpace d (frameExponential g o e v)) (D (coordinateVector i)))
        (chartBackwardOperator d (chartAt FourSpace d (frameExponential g o e v)) (D (coordinateVector j))) at hp
    rw [frameExponential_chart_backward g o e d v (coordinateVector i) hd,
      frameExponential_chart_backward g o e d v (coordinateVector j) hd,
      (chartAt FourSpace d).left_inv hd] at hp
    exact hp.symm
  have hdet : LinearMap.det D.toLinearMap = A.det := by
    rw [← Matrix.toEuclideanLin.apply_symm_apply D.toLinearMap, LinearMap.det_toLpLin 2]
  rw [show frameExponentialJacobian g o e v = Real.sqrt (frameExponentialGram g o e v).det from rfl,
    hGram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have halg : A.det * (G.det * A.det) = A.det ^ 2 * G.det := by ring
  rw [halg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  change |A.det| * Real.sqrt G.det = Real.sqrt G.det * |LinearMap.det D.toLinearMap|
  rw [hdet, mul_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The pushforward of the actual exponential Jacobian on minimizing
vectors dominates Riemannian volume. The proof is local in output charts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [MeasurableSpace M] [BorelSpace M]

def chartCoordinateExtension (c : M) : M → FourSpace := by
  classical
  exact (chartAt FourSpace c).source.piecewise (chartAt FourSpace c) (fun _ => 0)

theorem chartCoordinateExtension_measurable (c : M) : Measurable (chartCoordinateExtension c) := by
  classical
  exact (chartAt FourSpace c).continuousOn.measurable_piecewise continuousOn_const
    (chartAt FourSpace c).open_source.measurableSet

omit [MeasurableSpace M] [BorelSpace M] in
theorem chartCoordinateExtension_eq (c x : M) (hx : x ∈ (chartAt FourSpace c).source) :
    chartCoordinateExtension c x = chartAt FourSpace c x := by
  classical
  exact piecewise_eq_of_mem _ _ _ hx

variable [IsManifold I4 ∞ M]

def chartWeight (g : SmoothMetric M) (c : M) : FourSpace → ℝ≥0∞ := by
  classical
  exact (chartAt FourSpace c).target.piecewise
    (fun z => ENNReal.ofReal (chartVolumeDensity g c z)) (fun _ => 0)

omit [MeasurableSpace M] [BorelSpace M] in
theorem chartWeight_eq (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    chartWeight g c z = ENNReal.ofReal (chartVolumeDensity g c z) := by
  classical
  exact piecewise_eq_of_mem _ _ _ hz

omit [MeasurableSpace M] [BorelSpace M] in
theorem chartWeight_measurable (g : SmoothMetric M) (c : M) : Measurable (chartWeight g c) := by
  classical
  apply ContinuousOn.measurable_piecewise _ continuousOn_const (chartAt FourSpace c).open_target.measurableSet
  intro z hz
  exact (ENNReal.continuous_ofReal.continuousAt.comp
    (chartVolumeDensity_contDiffAt g c z hz).continuousAt).continuousWithinAt

variable [T3Space M] [CompactSpace M] [PreconnectedSpace M]

def exponentialAreaMeasure (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : Measure M :=
  riemannianChartFactor • Measure.map (frameExponential g o e)
    ((volume.restrict (actualMinimizingTangentDomain g o e)).withDensity
      (fun v => ENNReal.ofReal (frameExponentialJacobian g o e v)))

omit [PreconnectedSpace M] in
theorem exponentialAreaMeasure_apply (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (A : Set M) (hA : MeasurableSet A) :
    exponentialAreaMeasure g o e A = riemannianChartFactor *
      ∫⁻ v in (frameExponential g o e) ⁻¹' A ∩ actualMinimizingTangentDomain g o e,
        ENNReal.ofReal (frameExponentialJacobian g o e v) := by
  rw [exponentialAreaMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (frameExponential_continuous g o e).measurable hA,
    withDensity_apply _ ((frameExponential_continuous g o e).measurable hA),
    Measure.restrict_restrict ((frameExponential_continuous g o e).measurable hA)]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry06
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Weighted exponential-area domination.  The weight is retained through
actual polar coordinates, for use with scalar oscillations and energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

theorem euclidean_lintegral_polar (F : FourSpace → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v) = polarAngularMass * ∫⁻ q : Directions, ∫⁻ r : Ioi (0 : ℝ),
      ENNReal.ofReal (r.val ^ 3) * F (r.val • q.val)
        ∂((volume : Measure ℝ).comap Subtype.val) ∂sphereMeasure := by
  have hp := euclideanPolarReconstruction_measurePreserving.lintegral_comp hF
  have hm : Measurable (fun p : Directions × Ioi (0 : ℝ) =>
      F (euclideanPolarReconstruction p)) := by
    simpa only [Function.comp_apply] using!
      hF.comp euclideanPolarReconstruction_measurePreserving.measurable
  rw [← hp, lintegral_prod _ hm.aemeasurable, lintegral_smul_measure]
  congr 1
  apply lintegral_congr
  intro q
  rw [Measure.volumeIoiPow,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (by fun_prop : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.val ^ 3)))
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rfl

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_first _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
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

local instance instIsProbabilityMeasureDirectionsSphereMeasure_5 : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability

theorem canonicalFrame_lintegral_sphere_rotations (g : SmoothMetric M)
    (o : FrameOrientation g) (F : FrameBundle g → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ e, ∫⁻ q : Directions,
      F (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))
      ∂sphereMeasure ∂canonicalFrameMeasure g o) =
      ∫⁻ e, F e ∂canonicalFrameMeasure g o := by
  have hm : Measurable (fun p : FrameBundle g × Directions =>
      F (p.1.rotate (orientedToOrthogonal (directionOrientedMatrix p.2)))) :=
    hF.comp ((continuous_frameRotate g).comp
      (continuous_fst.prodMk (continuous_orientedToOrthogonal.comp
        (continuous_directionOrientedMatrix.comp continuous_snd)))).measurable
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hq (q : Directions) :
      (∫⁻ e, F (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))
        ∂canonicalFrameMeasure g o) = ∫⁻ e, F e ∂canonicalFrameMeasure g o :=
    (canonicalFrameMeasure_rotate g o (directionOrientedMatrix q)).lintegral_comp hF
  simp_rw [hq]
  simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform finite radial domination constant, obtained from compactness of
the actual Jacobi family.  No curvature comparison estimate is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_uniform_actualJacobi_det_bound (g : SmoothMetric M) (hRic : RicciThree g) :
    ∃ C : ℝ, 0 < C ∧ ∀ e : FrameBundle g, ∀ r ∈ Icc (0 : ℝ) Real.pi,
      |((actualJacobiSolution g hRic e).J r).det| ≤ C := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  let F : C(Icc (0 : ℝ) Real.pi × FrameBundle g, ℝ) :=
    ⟨fun p => ((actualJacobiSolution g hRic p.2).J p.1.val).det,
      ((actualJacobiJ_joint_continuous g hRic).comp
        (continuous_subtype_val.prodMap continuous_id)).matrix_det⟩
  refine ⟨‖F‖ + 1, by positivity, ?_⟩
  intro e r hr
  exact (F.norm_coe_le_norm (⟨r, hr⟩, e)).trans (by linarith)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normalize the geometric pair estimate and express its left side as
the variance of an actual scalar function. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

section Probability

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [SecondCountableTopology X] [CompactSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem continuous_pairwise_square_lintegral (a : C(X, ℝ)) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal ((a x - a y) ^ 2) ∂μ ∂μ) =
      ENNReal.ofReal (2 * ((∫ x, a x ^ 2 ∂μ) - (∫ x, a x ∂μ) ^ 2)) := by
  have hc : Continuous (fun p : X × X => (a p.1 - a p.2) ^ 2) :=
    ((a.continuous.comp continuous_fst).sub (a.continuous.comp continuous_snd)).pow 2
  have hi := hc.integrable_of_hasCompactSupport (μ := μ.prod μ)
    (HasCompactSupport.of_compactSpace _)
  have hm : Measurable (fun p : X × X => ENNReal.ofReal ((a p.1 - a p.2) ^ 2)) := by
    simpa only [Function.comp_apply] using! (ENNReal.continuous_ofReal.comp hc).measurable
  rw [← lintegral_prod _ hm.aemeasurable,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun p => sq_nonneg (a p.1 - a p.2))),
    integral_prod _ hi, continuous_pairwise_square_integral]

end Probability

end
end PositiveEinsteinFour.Geometry
end


section

/-! Unconditional weak Poisson solvability for the actual metric.  The
Poincaré constant comes from the exponential-map pair estimate.  The value
of the solution is a scalar on the base manifold, and its equation holds
against every element of the actual first-jet completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

local instance actualWeakPoisson_compact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coordinate equation for the same H¹ solution supplied by the
variational solver. This keeps its weak coordinate derivatives and its
distributional Poisson equation attached to one representative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance h1Equation_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coordinate equation with an actual L2 source for the H1 solution supplied by the
variational solver. This keeps its weak coordinate derivatives and its
distributional Poisson equation attached to one representative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance h1EquationL2_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic energy controls the local coordinate L² differential.
These estimates are uniform over the smooth scalars generating H¹. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance chartEnergy_frameCompact_r45cbc0_1 (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g
local instance chartEnergy_baseProbability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coordinate differential extends continuously from smooth scalars
to the actual intrinsic H¹ completion on every compact chart set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance chartH1_frameCompact_r45cbc0_1 (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g
local instance chartH1_baseProbability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The extended coordinate derivative is the weak derivative of the actual
chart representative, verified against genuine compact smooth tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance chartWeak_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The critical Euclidean H1-to-L4 estimate needed by the compact
four-dimensional scalar minimization. The constant here is not sharp;
sharpness on the manifold comes from the nonlinear rigidity argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped ENNReal NNReal

noncomputable section

namespace ScalarEuclideanSobolev

local notation "V" => FourSpace

def toL4 (f : ↥(Euclidean.C1c (E := V))) : Lp ℝ 4 (volume : Measure V) :=
  (f.property.1.continuous.memLp_of_hasCompactSupport f.property.2).toLp f.val

end ScalarEuclideanSobolev

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local H¹ derivatives give genuine global weak derivatives after a
compact cutoff. No differentiability of an L² representative is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance localWeak_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.heatSignedTraceENorm
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Real coordinate L² functions and their weak derivatives embed into
the complex tempered distributions used by the elliptic inverse. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance complexCoordinates_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The ordinary continuous H¹-to-L⁴ embedding for the actual compact
four-manifold, assembled from compact chart cutoffs. No sharp constant is
asserted here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_6
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance manifoldSobolev_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! A linear scalar eigenfunction source remains exactly a multiple of the
weighted chart unknown after localization and affine normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance eigenSource_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local smoothness of the actual intrinsic weak Poisson solution.
All coefficients, cutoffs, affine maps and right-hand sides are constructed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance localPoisson_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Lower-order coefficients contributed by the normal-frame connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatConnectionFirst_contDiffAt (n : ℕ) (a : FourSpace → Mat4)
    (A : Fin 4 → FourSpace → HeatMat6) (x : FourSpace)
    (ha : ∀ i j, ContDiffAt ℝ n (fun y => a y i j) x)
    (hA : ∀ i k l, ContDiffAt ℝ n (fun y => A i y k l) x)
    (i : Fin 4) (k l : Fin 6) :
    ContDiffAt ℝ n (fun y => fourHeatConnectionFirst (a y) (fun j => A j y) i k l) x := by
  change ContDiffAt ℝ n (fun y => (-2 : ℝ) * ∑ j : Fin 4, a y i j * A j y k l) x
  exact contDiffAt_const.mul (ContDiffAt.sum (fun j _ => (ha i j).mul (hA j k l)))

theorem fourHeatConnectionZero_contDiffAt (n : ℕ) (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (A : Fin 4 → FourSpace → HeatMat6)
    (V : FourSpace → HeatMat6) (x : FourSpace)
    (ha : ∀ i j, ContDiffAt ℝ n (fun y => a y i j) x)
    (hb : ∀ i, ContDiffAt ℝ n (fun y => b y i) x)
    (hA : ∀ i k l, ContDiffAt ℝ (n + 1) (fun y => A i y k l) x)
    (hV : ∀ k l, ContDiffAt ℝ n (fun y => V y k l) x) (k l : Fin 6) :
    ContDiffAt ℝ n (fun y => fourHeatConnectionZero (a y) (b y) A (V y) y k l) x := by
  have hA0 (i : Fin 4) (k l : Fin 6) : ContDiffAt ℝ n (fun y => A i y k l) x :=
    (hA i k l).of_le (by exact_mod_cast Nat.le_succ n)
  have hD (i j : Fin 4) (k l : Fin 6) :
      ContDiffAt ℝ n (partialDeriv (fun y => A i y k l) j) x :=
    ((hA i k l).fderiv_right (m := n) (by norm_num [Nat.cast_add])).clm_apply contDiffAt_const
  change ContDiffAt ℝ n (fun y => V y k l +
    (∑ i : Fin 4, b y i * A i y k l) - ∑ i : Fin 4, ∑ j : Fin 4,
      a y i j * (partialDeriv (fun z => A i z k l) j y +
        ∑ q : Fin 6, A j y k q * A i y q l)) x
  apply ((hV k l).add (ContDiffAt.sum (fun i _ => (hb i).mul (hA0 i k l)))).sub
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (ha i j).mul ((hD i j k l).add
    (ContDiffAt.sum (fun q _ => (hA0 j k q).mul (hA0 i q l))))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact subtraction identities for localized sources in the scalar
resolvent chain. Density weighting and affine pullback preserve the equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set TemperedDistribution
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance iteratedSource_compact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! All integer local regularity for actual scalar weak eigenfunctions.
The eigenvalue becomes a compact zeroth-order coefficient; no regularity premise is added. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance localEigenRegularity_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal metric as a jointly regular pullback in the common
radial-frame family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatFamilyBasePartial_slice (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (z : HeatRadialFrameSpace) (hP : DifferentiableAt ℝ P z) (i : Fin 4) :
    (heatFamilyPartial P i z).1 =
      fderiv ℝ (fun x => (P (x, z.2)).1) z.1 (coordinateVector i) := by
  have hs : DifferentiableAt ℝ (fun x : FourSpace => P (x, z.2)) z.1 :=
    hP.comp z.1 (differentiableAt_id.prodMk (differentiableAt_const z.2))
  rw [heatFamilyPartial_slice P z hP i]
  exact (congrArg (fun L : FourSpace →L[ℝ] FourSpace => L (coordinateVector i))
    hs.hasFDerivAt.fst.fderiv).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatFamilyMetric (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace) : Mat4 :=
  fun i j => WithLp.ofLp (heatFamilyPartial P i z).1 ⬝ᵥ
    (metricInChart g c (P z).1 *ᵥ WithLp.ofLp (heatFamilyPartial P j z).1)

theorem heatFamilyMetric_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 1 : ℕ) P z)
    (hz : (P z).1 ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ n (fun y => heatFamilyMetric g c P y i j) z := by
  have hP0 : ContDiffAt ℝ n P z := hP.of_le (by exact_mod_cast Nat.le_succ n)
  have hD (a b : Fin 4) : ContDiffAt ℝ n
      (fun y => (heatFamilyPartial P a y).1 b) z := by
    let π : FourSpace →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) b
    exact π.contDiff.contDiffAt.comp z (heatFamilyPartial_contDiffAt n P z hP a).fst
  have hG (a b : Fin 4) : ContDiffAt ℝ n
      (fun y => metricInChart g c (P y).1 a b) z := by
    exact ContDiffAt.comp (f := fun y => (P y).1)
      (g := fun w => metricInChart g c w a b) z
      ((metricInChart_contDiffAt g c (P z).1 hz a b).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hP0.fst
  unfold heatFamilyMetric dotProduct Matrix.mulVec
  apply ContDiffAt.sum
  intro a _
  apply (hD i a).mul
  apply ContDiffAt.sum
  intro b _
  exact (hG a b).mul (hD j b)

variable [T3Space M] [CompactSpace M]

theorem heatFamilyMetric_exponential_germ (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 1 P (0, frameCoordinateState g c e))
    (hexp : (fun v => (P (v, frameCoordinateState g c e)).1) =ᶠ[𝓝 0]
      (fun v => chartAt FourSpace c (frameExponential g o e v))) :
    (fun v => heatFamilyMetric g c P (v, frameCoordinateState g c e))
      =ᶠ[𝓝 0] heatNormalMetric g o e := by
  let q := frameCoordinateState g c e
  have hi : Tendsto (fun v : FourSpace => (v, q)) (𝓝 0) (𝓝 (0, q)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hr := hi.eventually (hP.eventually (by simp))
  have hs : ∀ᶠ v in 𝓝 (0 : FourSpace), frameExponential g o e v ∈
      (chartAt FourSpace c).source :=
    (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds (by simpa only [frameExponential_zero] using he))
  filter_upwards [hr, hexp.eventuallyEq_nhds, hs] with v hv hvg hvs
  ext i j
  have hd := hvg.fderiv_eq (𝕜 := ℝ)
  rw [heatNormalMetric_chart_pairing g o e c v hvs i j]
  change WithLp.ofLp (heatFamilyPartial P i (v, q)).1 ⬝ᵥ
    (metricInChart g c (P (v, q)).1 *ᵥ WithLp.ofLp (heatFamilyPartial P j (v, q)).1) = _
  rw [heatFamilyBasePartial_slice P (v, q) (hv.differentiableAt one_ne_zero) i,
    heatFamilyBasePartial_slice P (v, q) (hv.differentiableAt one_ne_zero) j]
  dsimp only [Prod.fst, Prod.snd, q]
  have hb : (P (v, frameCoordinateState g c e)).1 =
      chartAt FourSpace c (frameExponential g o e v) := hvg.self_of_nhds
  rw [hb, hd]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Undo the positive chart density and the invertible affine rescaling
in the local smooth representative of the actual scalar weak eigenfunction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance eigenUnweighting_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! All integer local regularity for actual scalar weak eigenfunctions.
The eigenvalue becomes a compact zeroth-order coefficient; no regularity premise is added. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance localChain_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal volume density and leading heat amplitude in a common
family, including their actual exponential identifications. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatFamilyDensity (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace) : ℝ :=
  Real.sqrt (heatFamilyMetric g c P z).det

def heatFamilyLeading (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace) : ℝ :=
  (Real.sqrt (heatFamilyDensity g c P z))⁻¹

theorem heatFamilyDensity_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 1 : ℕ) P z)
    (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (hdet : (heatFamilyMetric g c P z).det ≠ 0) :
    ContDiffAt ℝ n (heatFamilyDensity g c P) z :=
  (heatFamilyMatrixDeterminant_contDiffAt n _ z
    (heatFamilyMetric_contDiffAt n g c P z hP hz)).sqrt hdet

theorem heatFamilyInverse_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 1 : ℕ) P z)
    (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (hdet : (heatFamilyMetric g c P z).det ≠ 0) (i j : Fin 4) :
    ContDiffAt ℝ n (fun y => (heatFamilyMetric g c P y)⁻¹ i j) z :=
  heatFamilyMatrixInverse_contDiffAt n _ z
    (heatFamilyMetric_contDiffAt n g c P z hP hz) hdet i j

variable [T3Space M] [CompactSpace M]

theorem heatFamilyDensity_exponential_germ (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 1 P (0, frameCoordinateState g c e))
    (hexp : (fun v => (P (v, frameCoordinateState g c e)).1) =ᶠ[𝓝 0]
      (fun v => chartAt FourSpace c (frameExponential g o e v))) :
    (fun v => heatFamilyDensity g c P (v, frameCoordinateState g c e))
      =ᶠ[𝓝 0] frameExponentialJacobian g o e := by
  filter_upwards [heatFamilyMetric_exponential_germ g o c e he P hP hexp] with v hv
  exact congrArg (fun A : Mat4 => Real.sqrt A.det) hv

theorem heatFamilyLeading_exponential_germ (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 1 P (0, frameCoordinateState g c e))
    (hexp : (fun v => (P (v, frameCoordinateState g c e)).1) =ᶠ[𝓝 0]
      (fun v => chartAt FourSpace c (frameExponential g o e v))) :
    (fun v => heatFamilyLeading g c P (v, frameCoordinateState g c e))
      =ᶠ[𝓝 0] heatNormalLeadingAmplitude g o e := by
  filter_upwards [heatFamilyDensity_exponential_germ g o c e he P hP hexp] with v hv
  exact congrArg (fun a : ℝ => (Real.sqrt a)⁻¹) hv

end
end PositiveEinsteinFour.Geometry
end


section

/-! Pointwise identification on the whole common normal ball, rather
than only equality of germs at its center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatFamilyMetric_exponential_eq (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (x : FourSpace) (hP : DifferentiableAt ℝ P (x, frameCoordinateState g c e))
    (hsource : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hexp : (fun v => (P (v, frameCoordinateState g c e)).1) =ᶠ[𝓝 x]
      (fun v => chartAt FourSpace c (frameExponential g o e v))) :
    heatFamilyMetric g c P (x, frameCoordinateState g c e) = heatNormalMetric g o e x := by
  let q := frameCoordinateState g c e
  have hd := hexp.fderiv_eq (𝕜 := ℝ)
  have hv : (P (x, q)).1 = chartAt FourSpace c (frameExponential g o e x) := hexp.self_of_nhds
  ext i j
  rw [heatNormalMetric_chart_pairing g o e c x hsource i j]
  change WithLp.ofLp (heatFamilyPartial P i (x, q)).1 ⬝ᵥ
    (metricInChart g c (P (x, q)).1 *ᵥ WithLp.ofLp (heatFamilyPartial P j (x, q)).1) = _
  rw [heatFamilyBasePartial_slice P (x, q) hP i,
    heatFamilyBasePartial_slice P (x, q) hP j]
  dsimp only [Prod.fst, Prod.snd, q]
  rw [hv, hd]

theorem HeatNormalFrameData.metric_slice_eq {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hpoint : D.point = fun v => P (v, frameCoordinateState g c e))
    (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hP : DifferentiableAt ℝ P (x, frameCoordinateState g c e))
    (hsource : frameExponential g o e x ∈ (chartAt FourSpace c).source) :
    heatFamilyMetric g c P (x, frameCoordinateState g c e) = heatNormalMetric g o e x := by
  apply heatFamilyMetric_exponential_eq g o c e P x hP hsource
  filter_upwards [isOpen_ball.mem_nhds hx] with v hv
  simpa only [hpoint] using D.exponential v hv

end
end PositiveEinsteinFour.Geometry
end


section

/-! Global smooth representatives of actual intrinsic weak scalar eigenfunctions, obtained from the proved local coordinate regularity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance eigenSmooth_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance eigenSmooth_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The drift used by the actual normal parametrix has the geometric
coordinate transformation law on a proved neighborhood of its center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.metric_pullback_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source) :
    heatNormalMetric g o e =ᶠ[𝓝 (0 : FourSpace)]
      heatPullbackMetric g c (fun y => (D.point y).1) := by
  have hs : ∀ᶠ x in 𝓝 (0 : FourSpace), frameExponential g o e x ∈
      (chartAt FourSpace c).source :=
    (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds (by simpa only [frameExponential_zero] using he))
  filter_upwards [hs, ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hs hx
  exact D.metric_pullback x hx hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar spectral vectors are smooth functions satisfying the
geometric Laplace eigenvalue equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

local instance eigenPointwise_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar and matrix coefficients of the two-form heat
operator form one finite-regularity family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatFamilyFirst (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (i : Fin 4) : HeatMat6 :=
  fourHeatConnectionFirst (heatFamilyMetric g c P z)⁻¹
    (fun j => heatFamilyTwoFormConnection g c P j z) i

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar and matrix coefficients of the one-form heat
operator form one finite-regularity family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatFamilyOneFirst (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (i : Fin 4) : Mat4 :=
  fourHeatOneConnectionFirst (heatFamilyMetric g c P z)⁻¹
    (fun j => heatFamilyConnection g c P j z) i

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite scalar chain rules and the actual change of normal-coordinate
Laplacian. The Jacobian derivative cancels the density drift exactly. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped Manifold ContDiff _root_.Topology BigOperators Matrix.Norms.Elementwise

noncomputable section

theorem heat_scalar_second_comp (F : FourSpace → FourSpace) (f : FourSpace → ℝ)
    (x : FourSpace) (hF : ContDiffAt ℝ 2 F x) (hf : ContDiffAt ℝ 2 f (F x)) (i j : Fin 4) :
    partialDeriv (partialDeriv (fun y => f (F y)) i) j x =
      (∑ r, partialDeriv (fun y => jacobianMatrix F y r i) j x * partialDeriv f r (F x)) +
        ∑ r, ∑ s, jacobianMatrix F x r i * jacobianMatrix F x s j *
          partialDeriv (partialDeriv f r) s (F x) := by
  have hFd := hF.differentiableAt (by norm_num)
  have hfr (r : Fin 4) : ContDiffAt ℝ 1 (partialDeriv f r) (F x) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hJ (r : Fin 4) : DifferentiableAt ℝ (fun y => jacobianMatrix F y r i) x :=
    (heatJacobian_entry_regular 1 hF r i).differentiableAt one_ne_zero
  have hG (r : Fin 4) : DifferentiableAt ℝ (fun y => partialDeriv f r (F y)) x :=
    ((hfr r).differentiableAt one_ne_zero).comp x hFd
  have he : partialDeriv (fun y => f (F y)) i =ᶠ[𝓝 x]
      (fun y => ∑ r, jacobianMatrix F y r i * partialDeriv f r (F y)) := by
    have hFn := (hF.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by norm_num)
    have hfn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 f (F y) :=
      hF.continuousAt.tendsto.eventually
        ((hf.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by norm_num))
    filter_upwards [hFn, hfn] with y hFy hfy
    exact partialDeriv_comp (hFy.differentiableAt one_ne_zero)
      (hfy.differentiableAt one_ne_zero) i
  have hd := congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector j)) he.fderiv_eq
  change partialDeriv (partialDeriv (fun y => f (F y)) i) j x = _ at hd
  rw [hd]
  rw [fderiv_fun_sum (u := Finset.univ)
    (A := fun r y => jacobianMatrix F y r i * partialDeriv f r (F y))
    (fun r _ => (hJ r).mul (hG r)), _root_.sum_apply]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [fderiv_fun_mul (hJ r) (hG r)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  have hc := partialDeriv_comp hFd ((hfr r).differentiableAt one_ne_zero) j
  change fderiv ℝ (fun y => partialDeriv f r (F y)) x (coordinateVector j) = _ at hc
  rw [hc, Finset.mul_sum]
  simp only [mul_assoc, partialDeriv]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact spatial slices of the lower order family coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatFamilyFirst_slice (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : DifferentiableAt ℝ P z) :
    heatFamilyFirst g c P z = fun i => fourHeatConnectionFirst
      (heatFamilyMetric g c P z)⁻¹
      (fun j => heatTwoFormConnection g c (fun x => P (x, z.2)) j z.1) i := by
  funext i
  simp only [heatFamilyFirst, heatFamilyTwoFormConnection_slice g c P z hP]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Initial mass of the finite Gaussian parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped _root_.Topology

noncomputable section

theorem fourHeatGaussian_amplitude_integrable (f : FourSpace → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) (t : ℝ) (ht : 0 < t) :
    Integrable (fun x => fourHeatGaussian t x * f x) := by
  apply ((fourHeatGaussian_integrable t ht).mul_const C).mono'
    ((fourHeatGaussian_continuous t).mul hf).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    change ‖fourHeatGaussian t x * f x‖ ≤ fourHeatGaussian t x * C
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (fourHeatGaussian_pos t ht x)]
    exact mul_le_mul_of_nonneg_left (hC x) (fourHeatGaussian_pos t ht x).le

theorem fourHeatGaussian_amplitude_limit (f : FourSpace → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) :
    Tendsto (fun t => ∫ x : FourSpace, fourHeatGaussian t x * f x)
      (𝓝[Set.Ioi 0] 0) (𝓝 (f 0)) := by
  simpa only [zero_sub, neg_neg, neg_zero] using
    fourHeatGaussian_approximate_identity (fun y => f (-y))
      (hf.comp continuous_neg) C (fun y => hC (-y)) 0

theorem fourHeatPolynomial_gaussian_integral (u : Fin 4 → FourSpace → ℝ)
    (hu : ∀ i, Continuous (u i)) (C : Fin 4 → ℝ) (hC : ∀ i x, ‖u i x‖ ≤ C i)
    (t : ℝ) (ht : 0 < t) :
    (∫ x : FourSpace, fourHeatGaussian t x * fourHeatPolynomial u t x) =
      (∫ x : FourSpace, fourHeatGaussian t x * u 0 x) +
      t * (∫ x : FourSpace, fourHeatGaussian t x * u 1 x) +
      t ^ 2 * (∫ x : FourSpace, fourHeatGaussian t x * u 2 x) +
      t ^ 3 * (∫ x : FourSpace, fourHeatGaussian t x * u 3 x) := by
  have hi (i : Fin 4) := fourHeatGaussian_amplitude_integrable (u i) (hu i) (C i) (hC i) t ht
  have he (x : FourSpace) : fourHeatGaussian t x * fourHeatPolynomial u t x =
      fourHeatGaussian t x * u 0 x + t * (fourHeatGaussian t x * u 1 x) +
      t ^ 2 * (fourHeatGaussian t x * u 2 x) +
      t ^ 3 * (fourHeatGaussian t x * u 3 x) := by
    unfold fourHeatPolynomial
    ring
  simp_rw [he]
  rw [integral_add (f := fun x => fourHeatGaussian t x * u 0 x +
      t * (fourHeatGaussian t x * u 1 x) + t ^ 2 * (fourHeatGaussian t x * u 2 x))
      (g := fun x => t ^ 3 * (fourHeatGaussian t x * u 3 x))
      (((hi 0).add ((hi 1).const_mul t)).add ((hi 2).const_mul (t ^ 2)))
      ((hi 3).const_mul (t ^ 3)),
    integral_add (f := fun x => fourHeatGaussian t x * u 0 x +
      t * (fourHeatGaussian t x * u 1 x))
      (g := fun x => t ^ 2 * (fourHeatGaussian t x * u 2 x))
      ((hi 0).add ((hi 1).const_mul t)) ((hi 2).const_mul (t ^ 2)),
    integral_add (f := fun x => fourHeatGaussian t x * u 0 x)
      (g := fun x => t * (fourHeatGaussian t x * u 1 x))
      (hi 0) ((hi 1).const_mul t)]
  simp only [integral_const_mul]

theorem fourHeatPolynomial_approximate_identity (u : Fin 4 → FourSpace → ℝ)
    (hu : ∀ i, Continuous (u i)) (C : Fin 4 → ℝ) (hC : ∀ i x, ‖u i x‖ ≤ C i) :
    Tendsto (fun t => ∫ x : FourSpace, fourHeatGaussian t x * fourHeatPolynomial u t x)
      (𝓝[Set.Ioi 0] 0) (𝓝 (u 0 0)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[Set.Ioi 0] 0) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hL (i : Fin 4) := fourHeatGaussian_amplitude_limit (u i) (hu i) (C i) (hC i)
  have h := (((hL 0).add (ht.mul (hL 1))).add ((ht.pow 2).mul (hL 2))).add
    ((ht.pow 3).mul (hL 3))
  simp only [zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_pow (by norm_num : (3 : ℕ) ≠ 0), add_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (fourHeatPolynomial_gaussian_integral u hu C hC t ht).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Global smooth representatives of actual intrinsic weak scalar eigenfunctions, obtained from the proved local coordinate regularity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

local instance heatSmooth_frameCompact_r45cbc0_1 (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g
local instance heatSmooth_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Remove the single inverse-time factor from the cutoff commutator.
The resulting coefficient is continuous also at time zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

def fourHeatScaledCommutator (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → HeatMat6) (χ : FourSpace → ℝ)
    (u : Fin 4 → FourSpace → Fin 6 → ℝ) (t : ℝ) (x : FourSpace) (k : Fin 6) : ℝ :=
  t * fourHeatLocalOperator (a x) (b x) 0 χ x * fourHeatBundlePolynomial u t x k -
  2 * (∑ i, ∑ j, a x i j * partialDeriv χ i x *
    (t * partialDeriv (fun y => fourHeatBundlePolynomial u t y k) j x -
      x j / 2 * fourHeatBundlePolynomial u t x k)) +
  t * (∑ i, ∑ q, B x i k q * partialDeriv χ i x * fourHeatBundlePolynomial u t x q)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial first jet on two-forms is the actual curvature action,
including the sign imposed by covariant tensor slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_matrixPartial_eq_fderiv (B : FourSpace → Mat4) (x : FourSpace)
    (hB : ∀ r s, DifferentiableAt ℝ (fun z => B z r s) x) (i : Fin 4) :
    matrixPartial B i x = fderiv ℝ B x (coordinateVector i) := by
  have hd : DifferentiableAt ℝ B x :=
    differentiableAt_pi.mpr (fun r => differentiableAt_pi.mpr (hB r))
  ext r s
  let L₁ : Mat4 →L[ℝ] (Fin 4 → ℝ) := ContinuousLinearMap.proj r
  let L₂ : (Fin 4 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj s
  let L := L₂.comp L₁
  exact congrArg (fun K : FourSpace →L[ℝ] ℝ => K (coordinateVector i))
    (L.hasFDerivAt.comp x hd.hasFDerivAt).fderiv

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Actual smooth closed and coclosed two-forms. Their inclusion in the
finite weak Hodge kernel proves finite-dimensionality without an index input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothTwoFormExterior : smoothTwoForms o →ₗ[ℝ]
    (FrameBundle g → Fin 4 → Fin 4 → Fin 4 → ℝ) where
  toFun u e i j k := twoFormExteriorComponent
    (fun p q r => twoFormFramedCovariantDerivative o u.val e ![p,q,r]) i j k
  map_add' u v := by
    funext e i j k
    simp only [twoFormExteriorComponent, twoFormFramedCovariantDerivative_add, Pi.add_apply]
    ring
  map_smul' r u := by
    funext e i j k
    change twoFormExteriorComponent (fun p q s =>
      twoFormFramedCovariantDerivative o (r • u.val) e ![p,q,s]) i j k = _
    simp only [twoFormExteriorComponent, twoFormFramedCovariantDerivative_smul,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def smoothHarmonicTwoForms : Submodule ℝ (smoothTwoForms o) :=
  smoothTwoFormExterior.ker ⊓ smoothTwoFormCodifferential.ker

theorem mem_smoothHarmonicTwoForms (u : smoothTwoForms o) :
    u ∈ smoothHarmonicTwoForms ↔
      (∀ e i j k, smoothTwoFormExterior u e i j k = 0) ∧
      ∀ e k, smoothTwoFormCodifferential u e k = 0 := by
  simp only [smoothHarmonicTwoForms, Submodule.mem_inf, LinearMap.mem_ker,
    funext_iff, Pi.zero_apply]

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

/-! Uniform compact bounds for the actual transport family and the
coefficient left by the third transport equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

theorem heatFamilyScalar_compact_jet_bound (f : HeatRadialFrameSpace → ℝ)
    (hf : ContDiff ℝ 4 f) (K : Set HeatRadialFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ n : ℕ, n ≤ 4 → ∀ z ∈ K, ‖iteratedFDeriv ℝ n f z‖ ≤ C := by
  have hb (n : Fin 5) : ∃ C ≥ (0 : ℝ), ∀ z ∈ K, ‖iteratedFDeriv ℝ n.val f z‖ ≤ C := by
    have hc : Continuous (iteratedFDeriv ℝ n.val f) :=
      hf.continuous_iteratedFDeriv (by exact_mod_cast (show n.val ≤ 4 by omega))
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun z hz => (hC z hz).trans (le_max_left _ _)⟩
  choose C hC hb using hb
  refine ⟨∑ n : Fin 5, C n, Finset.sum_nonneg (fun n _ => hC n), ?_⟩
  intro n hn z hz
  let i : Fin 5 := ⟨n, by omega⟩
  exact (hb i z hz).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exterior/codifferential energy is a continuous nonnegative scalar
on the base. Its vanishing detects actual smooth harmonic forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance instIsProbabilityMeasureNormalizedVolume : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiation and radial integration commute with the fixed
Hodge-signed trace on the six-dimensional two-form fiber. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise Interval

noncomputable section

theorem heatSignedTrace_weightedRadial (m : ℕ) (U : FourSpace → ℝ)
    (F : FourSpace → HeatMat6) (hU : Continuous U) (hF : Continuous F)
    (hU0 : ∀ x, U x ≠ 0) (x : FourSpace) :
    (twoFormHodgeMatrix * (show HeatMat6 from fun k l =>
      fourHeatWeightedRadialAverage m U (fun y => F y k l) x)).trace =
      fourHeatWeightedRadialAverage m U (fun y => (twoFormHodgeMatrix * F y).trace) x := by
  let G : ℝ → HeatMat6 := fun s => (s ^ m / U (s • x)) • F (s • x)
  have hs : Continuous (fun s : ℝ => s • x) := continuous_id.smul continuous_const
  have hG : Continuous G :=
    ((continuous_id.pow m).div (hU.comp hs) (fun s => hU0 (s • x))).smul (hF.comp hs)
  have hi : IntervalIntegrable G volume 0 1 := hG.intervalIntegrable 0 1
  have heq : (fun k l => fourHeatWeightedRadialAverage m U (fun y => F y k l) x) =
      U x • ∫ s : ℝ in 0..1, G s := by
    ext k l
    let L₁ : HeatMat6 →L[ℝ] (Fin 6 → ℝ) := ContinuousLinearMap.proj k
    let L₂ : (Fin 6 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj l
    have h := (L₂.comp L₁).intervalIntegral_comp_comm hi
    change (∫ s : ℝ in 0..1, G s k l) = (∫ s : ℝ in 0..1, G s) k l at h
    simp only [fourHeatWeightedRadialAverage, fourHeatRadialAverage, Matrix.smul_apply,
      smul_eq_mul]
    rw [← h]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    change s ^ m * (F (s • x) k l / U (s • x)) = s ^ m / U (s • x) * F (s • x) k l
    ring
  rw [heq]
  let L := heatSignedTraceLinear.toContinuousLinearMap
  have h := L.intervalIntegral_comp_comm hi
  change (∫ s : ℝ in 0..1, (twoFormHodgeMatrix * G s).trace) =
    (twoFormHodgeMatrix * ∫ s : ℝ in 0..1, G s).trace at h
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← h]
  change U x * (∫ s : ℝ in 0..1, (twoFormHodgeMatrix * G s).trace) =
    U x * (∫ s : ℝ in 0..1, s ^ m * ((twoFormHodgeMatrix * F (s • x)).trace / U (s • x)))
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [G, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual adjoint relation between d on one-forms and δ on two-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_10 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar heat output in H1, with its exact smooth realization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_11 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The codifferential bilinear form and the global Hodge energy splitting. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_12 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance instIsProbabilityMeasureNormalizedVolume_1 : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The codifferential squares to zero in degrees two and one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance codifferentialBaseProbability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exterior derivative from actual scalar H1 to actual one-form L2.
The extension is made along the dense range of smooth first jets. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_13 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual closed/exact degree-one quotient vanishes under Ric = 3g. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

abbrev smoothClosedOneForms : Submodule ℝ (smoothCovariantFields M 1) :=
  (smoothOneFormExteriorLinear (o := o)).ker

local instance instAddCommGroupSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFieldsSmoothClosedOneForms : AddCommGroup (smoothClosedOneForms (o := o)) :=
  Submodule.addCommGroup _

def smoothExactOneForms : Submodule ℝ (smoothClosedOneForms (o := o)) :=
  (LinearMap.range (smoothScalarDifferentialLinear g)).comap
    (smoothClosedOneForms (o := o)).subtype

abbrev OneFormDeRhamCohomology :=
  (smoothClosedOneForms (o := o)) ⧸ (smoothExactOneForms (o := o))

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual coclosed/codifferential quotient. This is the upper-degree
Hodge-dual complex written in one-form coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

abbrev smoothCoClosedOneForms (g : SmoothMetric M) : Submodule ℝ (smoothCovariantFields M 1) :=
  (smoothOneFormDivergence g).ker

local instance hodgeDualClosedAddGroup : AddCommGroup (smoothCoClosedOneForms g) :=
  Submodule.addCommGroup _

def smoothCoexactOneForms : Submodule ℝ (smoothCoClosedOneForms g) :=
  (LinearMap.range (smoothTwoFormCodifferentialLinear (o := o))).comap
    (smoothCoClosedOneForms g).subtype

abbrev HodgeDualOneCohomology :=
  (smoothCoClosedOneForms g) ⧸ (smoothCoexactOneForms (o := o))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Derivatives of the actual scalar and two-form eigenfamilies are total
in the one-form L2 completion. No spectral completeness is assumed in degree one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_14 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HeatKernels10
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Normalized gradients of the positive scalar modes form an actual
orthonormal family of exact one-form eigenvectors. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

local instance instCompactSpaceFrameBundle_15 (g : SmoothMetric M) : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Banach space obtained by uniformly completing genuine smooth one-forms.
Frame norms descend to the base, so its L2 realization remains injective. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_17 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
local instance instIsProbabilityMeasureFrameBundleCanonicalFrameMeasure : IsProbabilityMeasure (canonicalFrameMeasure g o) := inferInstance
local instance instIsProbabilityMeasureNormalizedVolume_2 : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A third-order Gaussian remainder has vanishing diagonal in dimension four. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped _root_.Topology

noncomputable section

theorem fourHeatGaussian_diagonal_power (m : ℕ) (t : ℝ) (ht : 0 < t) :
    t ^ (m + 2) * fourHeatGaussian t 0 = t ^ m / (16 * Real.pi ^ 2) := by
  simp only [fourHeatGaussian, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, Real.exp_zero, mul_one, pow_add]
  field_simp [Real.pi_ne_zero]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form reconstruction is contractive in the continuous norm. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}
local instance instCompactSpaceFrameBundle_19 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! A proved uniform Gaussian bound for the residual of the actual local
scalar parametrix. Its diagonal scaling is O(t) in dimension four. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

theorem fourHeatGaussian_le_diagonal (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    fourHeatGaussian t x ≤ fourHeatGaussian t 0 := by
  have hexp : Real.exp (-(4 * t)⁻¹ * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have h : 0 ≤ (4 * t)⁻¹ * ‖x‖ ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
    linarith)
  simpa only [fourHeatGaussian, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, Real.exp_zero, mul_one] using
    mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr (sq_nonneg (4 * Real.pi * t)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded continuous evaluation of actual positive-time one-form heat. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_25 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The time derivative and Hodge image are combined before estimation,
so the actual Gaussian transport cancellations are retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_six_norm_le (v : TwoFormFour) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ k, |v k| ≤ B) : ‖v‖ ≤ 3 * B := by
  have hs : ‖v‖ ^ 2 ≤ 6 * B ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _k : Fin 6, B ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have hk := abs_le.mp (h k)
        nlinarith [sq_nonneg (v k - B), sq_nonneg (v k + B)]
      _ = _ := by simp
  nlinarith [norm_nonneg v]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed zeroth-order coefficient is purely quadratic in the
connection: the potential and the linear connection terms have zero trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

def heatNormalConnectionQuadratic {D : HeatNormalFrameData g o c e}
    (a : FourSpace → Mat4) (x : FourSpace) : ℝ :=
  ∑ i, ∑ j, a x i j * (twoFormHodgeMatrix * heatTwoFormConnection g c D.point j x *
    heatTwoFormConnection g c D.point i x).trace

end
end PositiveEinsteinFour.Geometry
end


section

/-! At the radial center, derivatives of the scalar metric weights do
not contribute to the quadratic connection trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_trace_product_regular (H : HeatMat6) (A B : FourSpace → HeatMat6)
    (hA : ∀ k l, ContDiffAt ℝ 2 (fun x => A x k l) 0)
    (hB : ∀ k l, ContDiffAt ℝ 2 (fun x => B x k l) 0) :
    ContDiffAt ℝ 2 (fun x => (H * A x * B x).trace) 0 := by
  simp_rw [heat_trace_product_expansion]
  exact ContDiffAt.sum (fun k _ => ContDiffAt.sum (fun l _ =>
    ContDiffAt.sum (fun q _ => contDiffAt_const.mul ((hA l q).mul (hB q k)))))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact normal-frame signed polynomial and its first jet. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatSignedGram_contDiff (A B : FourSpace → HeatMat6)
    (hA : ∀ i j, ContDiff ℝ 2 (fun x => A x i j))
    (hB : ∀ i j, ContDiff ℝ 2 (fun x => B x i j)) :
    ContDiff ℝ 2 (fun x => heatSignedGram (A x) (B x)) := by
  simp only [heatSignedGram, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  apply contDiff_const.mul
  apply ContDiff.sum
  intro k _
  exact (hA k j).mul (hB k i)

theorem fourHeat_fderiv_zero_of_partial (f : FourSpace → ℝ)
    (h : ∀ i, partialDeriv f i 0 = 0) : fderiv ℝ f 0 = 0 := by
  ext x
  have hx : (∑ i, x i • coordinateVector i) = x := sum_coordinateVector (WithLp.ofLp x)
  conv_lhs => rw [← hx, map_sum]
  simp only [map_smul, smul_eq_mul]
  change (∑ i, x i * partialDeriv f i 0) = 0
  simp only [h, mul_zero, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! An actual quadratic integral bound for the global normal amplitude.
This keeps Gaussian spatial concentration, unlike the uniform norm bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance instCompactSpaceFrameBundle_29 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
local instance instIsProbabilityMeasureNormalizedVolume_5 : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two coefficients that survive the signed Gaussian limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeat_second_partial_eq_fderiv (f : FourSpace → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (i j : Fin 4) :
    partialDeriv (partialDeriv f i) j 0 =
      fderiv ℝ (fderiv ℝ f) 0 (coordinateVector j) (coordinateVector i) := by
  let L := ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  exact congrArg (fun K : FourSpace →L[ℝ] ℝ => K (coordinateVector j))
    (L.hasFDerivAt.comp 0 hd).fderiv

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact normal-coordinate pairing of two finite-regularity amplitudes
inside the actual two-form Hilbert space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance heatNormalInnerCompact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
local instance heatNormalInnerProbability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

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

/-! A unit Weyl norm forces parallel Weyl curvature and maximal normalized
determinant. The proof differentiates its actual constant norm twice. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}
  {μ : Measure (FrameBundle g)}

theorem MetricGreenData.unit_norm_first_pairing (d : MetricGreenData g μ)
    (hflow : OrientationPreservingFlow d o) (hnorm : ∀ x, plusNorm o x = 1)
    (f : FrameBundle g) (hf : f ∈ o.positive) (i : Fin 4) :
    matrixPairing (plusWeyl g f.base f.frame) (plusWeylGradient g f.base f.frame i) = 0 := by
  obtain ⟨f₀,hf₀⟩ := ((d.flow i).map 0).surjective f
  have hp : f₀ ∈ o.positive := (hflow i 0 f₀).mp (hf₀.symm ▸ hf)
  have hn (s : ℝ) : normalizedBlockNorm (plusWeyl g ((d.flow i).map s f₀).base
      ((d.flow i).map s f₀).frame) = 1 := by
    rw [← actual_plusNorm_frame o _ ((hflow i s f₀).mpr hp)]
    exact hnorm _
  have h := constant_matrix_norm_pairing (d.derivativeWeyl i 0 f₀) hn
  change matrixPairing (plusWeyl g ((d.flow i).map 0 f₀).base ((d.flow i).map 0 f₀).frame)
    (plusWeylGradient g ((d.flow i).map 0 f₀).base ((d.flow i).map 0 f₀).frame i) = 0 at h
  rw [hf₀] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Unit-norm Weyl curvature yields the parallel rank-one orthogonal
projector (W+ + I)/3. The polynomial relation comes from the actual
second derivative and Weyl equation. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}
  {μ : Measure (FrameBundle g)}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.projectorNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.projectorNormedSpace
theorem MetricGreenData.hessian_zero_of_gradient_zero (d : MetricGreenData g μ)
    (hflow : OrientationPreservingFlow d o)
    (hgrad : ∀ f ∈ o.positive, ∀ j, plusWeylGradient g f.base f.frame j = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (i j : Fin 4) :
    plusWeylHessian g e.base e.frame i j = 0 := by
  obtain ⟨f,hf⟩ := ((d.flow i).map 0).surjective e
  have hp : f ∈ o.positive := (hflow i 0 f).mp (hf.symm ▸ he)
  have hd := d.derivativeGradient i j 0 f
  have hz : (fun s => plusWeylGradient g ((d.flow i).map s f).base
      ((d.flow i).map s f).frame j) = fun _ => (0 : Mat) := by
    funext s
    exact hgrad _ ((hflow i s f).mpr hp) j
  rw [hz] at hd
  have h := hd.unique (hasDerivAt_const (0 : ℝ) (0 : Mat))
  change plusWeylHessian g ((d.flow i).map 0 f).base ((d.flow i).map 0 f).frame i j = 0 at h
  rw [hf] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


