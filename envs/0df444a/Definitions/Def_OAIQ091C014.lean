-- Prove2me | Definitions.Def_OAIQ091C014
-- name    : OAIQ091C014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T17:10:47.391653+00:00
-- url     : https://prove2.me/theorems/9c3da5ac-d5fe-4ebf-9fa7-04cd0a0200b5
-- title:
--   Definitions bundle OAIQ091C014 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 326 declarations of OpenAI's Lean: 62 definitions, 7 inductive types or structures, 4 instances and 253 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.BrinKarcherAveraging`, `OAI.PositiveEinsteinFour.Geometry.FrameBundle.rotate`, `OAI.PositiveEinsteinFour.Geometry.FrameReflectionData`, `OAI.PositiveEinsteinFour.Geometry.FrameReflectionData.reflectTest`, `OAI.PositiveEinsteinFour.Geometry.FrameReflectionData.reflectTestDerivative`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData`, `OAI.PositiveEinsteinFour.Geometry.OppositeWeylData`, `OAI.PositiveEinsteinFour.Geometry.OrientedNormRegularity`, `OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.rotate`, `OAI.PositiveEinsteinFour.Geometry.OrthonormalFrame.turn`, `OAI.PositiveEinsteinFour.Geometry.ParallelReflection`, `OAI.PositiveEinsteinFour.Geometry.PetersenPoissonInput`, `OAI.PositiveEinsteinFour.Geometry.PetersenScalarCalculusInput`, `OAI.PositiveEinsteinFour.Geometry.ScalarCovariantData`, `OAI.PositiveEinsteinFour.Geometry.ScalarCovariantData.gradientField`, `OAI.PositiveEinsteinFour.Geometry.ScalarCovariantData.hessianField`, `OAI.PositiveEinsteinFour.Geometry.ScalarCovariantData.valueField`, `OAI.PositiveEinsteinFour.Geometry.WeylCovariantIdentities`, `OAI.PositiveEinsteinFour.Geometry.chartWeightedConnection`, `OAI.PositiveEinsteinFour.Geometry.coordinateMomentum`, `OAI.PositiveEinsteinFour.Geometry.cotangentComponent`, `OAI.PositiveEinsteinFour.Geometry.cotangentDirection`, `OAI.PositiveEinsteinFour.Geometry.cotangentDivergence`, `OAI.PositiveEinsteinFour.Geometry.cotangentJacobian`, `OAI.PositiveEinsteinFour.Geometry.cotangentProjection`, `OAI.PositiveEinsteinFour.Geometry.curvatureDerivativeMatrix`, `OAI.PositiveEinsteinFour.Geometry.curvaturePontryaginDensity`, `OAI.PositiveEinsteinFour.Geometry.curvatureSignatureDensity`, `OAI.PositiveEinsteinFour.Geometry.directionOrientedMatrix`, `OAI.PositiveEinsteinFour.Geometry.frameCurvatureDerivative`, `OAI.PositiveEinsteinFour.Geometry.frameCurvatureField`, `OAI.PositiveEinsteinFour.Geometry.frameTurn`, `OAI.PositiveEinsteinFour.Geometry.geodesicCovariantDerivative`, `OAI.PositiveEinsteinFour.Geometry.hodgeFirstTensor`, `OAI.PositiveEinsteinFour.Geometry.iteratedScalarDerivative`, `OAI.PositiveEinsteinFour.Geometry.iteratedWeylDerivative`, `OAI.PositiveEinsteinFour.Geometry.minusNorm`, `OAI.PositiveEinsteinFour.Geometry.minusWeylGradient`, `OAI.PositiveEinsteinFour.Geometry.minusWeylHessian`, `OAI.PositiveEinsteinFour.Geometry.normalCurvature` and 29 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `EinsteinFour_BianchiSlices`, `EinsteinFour_ChartConnectionTransition`, `EinsteinFour_ChartCurvatureTransition`, `EinsteinFour_ChartMetricTransition`, `EinsteinFour_ChartVolumeDensity`, `EinsteinFour_CoordinateSecondBianchi`, `EinsteinFour_CotangentHamiltonian`, `EinsteinFour_CotangentJacobian`, `EinsteinFour_CotangentVolume`, `EinsteinFour_CurvatureContraction`, `EinsteinFour_CurvatureCoordinateSmoothness`, `EinsteinFour_CurvatureTensors02`, `EinsteinFour_FourHeatGaussianApproximation`, `EinsteinFour_FrameAverages`, `EinsteinFour_FrameBundle`, `EinsteinFour_FrameCurvature`, `EinsteinFour_FrameFlow`, `EinsteinFour_FrameOrientation`, `EinsteinFour_FrameOrientationContinuity`, `EinsteinFour_FrameRotation`, `EinsteinFour_GeodesicJacobiAlgebra`, `EinsteinFour_HodgeTheory08`, `EinsteinFour_MetricChartDistance`, `EinsteinFour_MetricChartLipschitz`, `EinsteinFour_MetricChartPath`, `EinsteinFour_MetricHessian`, `EinsteinFour_MetricLinearChartPath`, `EinsteinFour_MetricTensorCompatibility`, `EinsteinFour_RiemannianVolume`, `EinsteinFour_RiemannianVolumeFinite`, `EinsteinFour_RiemannianVolumePositive`, `EinsteinFour_ScalarPoissonKernelMeasure`, `EinsteinFour_ScalarPoissonKernelPotential`, `EinsteinFour_WeylDerivative`, `EinsteinFour_WeylEstimates01`, `EinsteinFour_WeylEstimates03`, `EinsteinFour_WeylNormal`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C036`, `OAIQ091C007`, `OAIQ091C008`, `OAIQ091C009` and `OAIQ091C010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C017` and `OAIQ091C018`; the statements `OAI_PositiveEinsteinFour_HighestHessian_minus_coordinate_casimir` and `OAI_PositiveEinsteinFour_MomentObstruction_two_constrained_moments`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C036
import Definitions.Def_OAIQ091C007
import Definitions.Def_OAIQ091C008
import Definitions.Def_OAIQ091C009
import Definitions.Def_OAIQ091C010

section
-- module Solutions.OAIQ091_EF.EinsteinFour_BianchiSlices
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

/-- A fixed outer derivative, retaining its actual tangent-vector entries. -/
def innerSlice (X : Hessian) (i : Fin 4) : Tensor where
  diagonal a := WithLp.toLp 2 (fun j => X i j a a)
  off a := WithLp.toLp 2 (fun j => X i j (next a) (previous a))

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ChartMetricTransition
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual metric pullback matrix in a chart. The tangent coordinates
at the image point use its own centered chart, so this congruence is the
zeroth-order part of the curvature coordinate-change calculation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chartTransition_contDiffAt (c d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ ∞ (chartTransition c d) z := by
  have hc : ContMDiffAt I4 I4 ∞ (chartAt FourSpace c).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) hz
  have hd : ContMDiffAt I4 I4 ∞ (chartAt FourSpace d) ((chartAt FourSpace c).symm z) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas d) hx
  exact (hd.comp z hc).contDiffAt

theorem chartTransition_fderiv (c d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    fderiv ℝ (chartTransition c d) z =
      (mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm z)).comp
        (mfderiv I4 I4 (chartAt FourSpace c).symm z) := by
  have hc : MDifferentiableAt I4 I4 (chartAt FourSpace c).symm z :=
    (mdifferentiable_chart (I := I4) c).symm.mdifferentiableAt hz
  have hd : MDifferentiableAt I4 I4 (chartAt FourSpace d)
      ((chartAt FourSpace c).symm z) :=
    (mdifferentiable_chart (I := I4) d).mdifferentiableAt hx
  convert! mfderiv_comp z hd hc using 1
  all_goals try with_reducible_and_instances rfl
  rw [mfderiv_eq_fderiv]
  rfl

theorem metricInChart_transition (g : SmoothMetric M) (c d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    metricInChart g c z = (chartTransitionMatrix c d z)ᵀ *
      (metricInChart g d (chartTransition c d z) * chartTransitionMatrix c d z) := by
  let A : FourSpace →L[ℝ] FourSpace :=
    mfderiv I4 I4 (chartAt FourSpace d) ((chartAt FourSpace c).symm z)
  let B : FourSpace →L[ℝ] FourSpace :=
    mfderiv I4 I4 (chartAt FourSpace d).symm (chartTransition c d z)
  let C : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace c).symm z
  have hBA : B.comp A = ContinuousLinearMap.id ℝ FourSpace :=
    (mdifferentiable_chart (I := I4) d).symm_comp_deriv hx
  have hF : fderiv ℝ (chartTransition c d) z = A.comp C :=
    chartTransition_fderiv c d z hz hx
  have hc : B.comp (fderiv ℝ (chartTransition c d) z) = C := by
    rw [hF, ← ContinuousLinearMap.comp_assoc, hBA, ContinuousLinearMap.id_comp]
  have hv (i : Fin 4) : B (fderiv ℝ (chartTransition c d) z (coordinateVector i)) =
      C (coordinateVector i) := congrArg (fun L : FourSpace →L[ℝ] FourSpace =>
        L (coordinateVector i)) hc
  ext i j
  symm
  change (fun k => chartTransitionMatrix c d z k i) ⬝ᵥ
    (metricInChart g d (chartTransition c d z) *ᵥ
      (fun k => chartTransitionMatrix c d z k j)) = _
  rw [metricInChart_pairing]
  change g.inner ((chartAt FourSpace d).symm (chartTransition c d z))
    (B (fderiv ℝ (chartTransition c d) z (coordinateVector i)))
    (B (fderiv ℝ (chartTransition c d) z (coordinateVector j))) = _
  rw [hv, hv]
  have hi : (chartAt FourSpace d).symm (chartTransition c d z) =
      (chartAt FourSpace c).symm z := (chartAt FourSpace d).left_inv hx
  rw [hi]
  rfl

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ChartConnectionTransition
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The connection coordinate change is derived from the actual metric
pullback, using metric compatibility and zero torsion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def pulledChartConnection (g : SmoothMetric M) (c d : M) (z : FourSpace)
    (i : Fin 4) : Mat4 :=
  pulledConnection (chartTransitionMatrix c d z)
    (matrixPartial (chartTransitionMatrix c d) i z)
    (weightedConnection (chartTransitionMatrix c d z)
      (fun a => connectionMatrix g d a (chartTransition c d z)) i)

theorem chartTransitionMatrix_det_ne_zero (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    (chartTransitionMatrix c d z).det ≠ 0 := by
  intro he
  have h := congrArg Matrix.det (metricInChart_transition g c d z hz hx)
  simp only [Matrix.det_mul, Matrix.det_transpose, he, zero_mul] at h
  exact (metricInChart_posDef g c z hz).det_pos.ne' h

theorem chartTransitionMatrix_contDiffAt (c d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source)
    (r s : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => chartTransitionMatrix c d w r s) z :=
  jacobian_entry_contDiffAt (chartTransition_contDiffAt c d z hz hx) r s

theorem matrixPartial_transition_target_metric (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i : Fin 4) :
    matrixPartial (fun w => metricInChart g d (chartTransition c d w)) i z =
      (weightedConnection (chartTransitionMatrix c d z)
        (fun a => connectionMatrix g d a (chartTransition c d z)) i)ᵀ *
          metricInChart g d (chartTransition c d z) +
      metricInChart g d (chartTransition c d z) *
        weightedConnection (chartTransitionMatrix c d z)
          (fun a => connectionMatrix g d a (chartTransition c d z)) i := by
  have hf := (chartTransition_contDiffAt c d z hz hx).differentiableAt (by first | simp | exact_mod_cast le_top)
  have htarget : chartTransition c d z ∈ (chartAt FourSpace d).target :=
    (chartAt FourSpace d).map_source hx
  have hG : IsUnit (metricInChart g d (chartTransition c d z)).det :=
    isUnit_iff_ne_zero.mpr (metricInChart_posDef g d _ htarget).det_pos.ne'
  rw [matrixPartial_comp hf (fun r s =>
    (metricInChart_contDiffAt g d _ htarget r s).differentiableAt (by first | simp | exact_mod_cast le_top))]
  simp only [matrixPartial_metric g d _ hG]
  simp only [weightedConnection, Matrix.transpose_sum, Matrix.transpose_smul,
    Finset.sum_mul, Finset.mul_sum, smul_add, smul_mul_assoc, mul_smul_comm,
    Finset.sum_add_distrib]
  rfl

theorem pulledChartConnection_metric (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i : Fin 4) :
    matrixPartial (metricInChart g c) i z =
      (pulledChartConnection g c d z i)ᵀ * metricInChart g c z +
        metricInChart g c z * pulledChartConnection g c d z i := by
  let J := chartTransitionMatrix c d
  let H := fun w => metricInChart g d (chartTransition c d w)
  let U := weightedConnection (J z)
    (fun a => connectionMatrix g d a (chartTransition c d z)) i
  have hG : metricInChart g c z = (J z)ᵀ * (H z * J z) :=
    metricInChart_transition g c d z hz hx
  have hcnear : ∀ᶠ w in 𝓝 z, w ∈ (chartAt FourSpace c).target :=
    (chartAt FourSpace c).open_target.mem_nhds hz
  have hcs : ContinuousAt (chartAt FourSpace c).symm z :=
    (contMDiffAt_symm_of_mem_maximalAtlas (I := I4) (n := ∞)
      (IsManifold.chart_mem_maximalAtlas c) hz).continuousAt
  have hdnear : ∀ᶠ w in 𝓝 z,
      (chartAt FourSpace c).symm w ∈ (chartAt FourSpace d).source :=
    hcs.preimage_mem_nhds ((chartAt FourSpace d).open_source.mem_nhds hx)
  have heq : metricInChart g c =ᶠ[𝓝 z] (fun w => (J w)ᵀ * (H w * J w)) := by
    filter_upwards [hcnear, hdnear] with w hcw hdw
    exact metricInChart_transition g c d w hcw hdw
  have hj (r s : Fin 4) : DifferentiableAt ℝ (fun w => J w r s) z :=
    (chartTransitionMatrix_contDiffAt c d z hz hx r s).differentiableAt (by first | simp | exact_mod_cast le_top)
  have ht : chartTransition c d z ∈ (chartAt FourSpace d).target :=
    (chartAt FourSpace d).map_source hx
  have hh (r s : Fin 4) : DifferentiableAt ℝ (fun w => H w r s) z :=
    (metricInChart_contDiffAt g d _ ht r s).differentiableAt (by first | simp | exact_mod_cast le_top) |>.comp z
      ((chartTransition_contDiffAt c d z hz hx).differentiableAt (by first | simp | exact_mod_cast le_top))
  have hpartial : matrixPartial H i z = Uᵀ * H z + H z * U :=
    matrixPartial_transition_target_metric g c d z hz hx i
  have hunit : IsUnit (J z).det :=
    isUnit_iff_ne_zero.mpr (chartTransitionMatrix_det_ne_zero g c d z hz hx)
  rw [matrixPartial_congr heq, matrixPartial_congruence J H z hj hh, hpartial]
  have hk := pulledConnection_metric_compatibility (H z) (J z)
    (matrixPartial J i z) U hunit
  rw [← Matrix.mul_assoc] at hG
  rw [hG]
  exact hk.symm

theorem pulledChartConnection_torsion (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source)
    (i j k : Fin 4) :
    pulledChartConnection g c d z i k j = pulledChartConnection g c d z j k i := by
  unfold pulledChartConnection
  apply pulledConnection_torsion (chartTransitionMatrix c d z)
    (fun r => matrixPartial (chartTransitionMatrix c d) r z)
    (fun a => connectionMatrix g d a (chartTransition c d z))
  · intro r s t
    exact jacobian_partials_commute (chartTransition_contDiffAt c d z hz hx) t r s
  · intro r s t
    exact christoffel_comm g d (chartTransition c d z) t r s

theorem christoffel_transition (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source)
    (k i j : Fin 4) :
    christoffel g c z k i j = pulledChartConnection g c d z i k j := by
  have hG : IsUnit (metricInChart g c z).det :=
    isUnit_iff_ne_zero.mpr (metricInChart_posDef g c z hz).det_pos.ne'
  have he := christoffel_eq_of_compatible g c z hG
    (fun r s t => pulledChartConnection g c d z s r t)
    (fun r s t => pulledChartConnection_torsion g c d z hz hx s t r) ?_
  · exact (congrFun (congrFun (congrFun he k) i) j).symm
  · intro r s t
    have hm := congrArg (fun A : Mat4 => A s t)
      (pulledChartConnection_metric g c d z hz hx r)
    simp only [matrixPartial, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply] at hm
    rw [← Finset.sum_add_distrib] at hm
    rw [hm]
    apply Finset.sum_congr rfl
    intro p _
    rw [metricInChart_comm g c z p t]
    ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ChartCurvatureTransition
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating the actual Christoffel transformation gives the
curvature intertwining equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartWeightedConnection (g : SmoothMetric M) (c d : M) (i : Fin 4)
    (z : FourSpace) : Mat4 :=
  weightedConnection (chartTransitionMatrix c d z)
    (fun a => connectionMatrix g d a (chartTransition c d z)) i

theorem chartWeightedConnection_contDiffAt (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source)
    (i r s : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => chartWeightedConnection g c d i w r s) z := by
  have ht := (chartAt FourSpace d).map_source hx
  have hdet := (metricInChart_posDef g d _ ht).det_pos.ne'
  change ContDiffAt ℝ ∞ (fun w => ∑ a, chartTransitionMatrix c d w a i *
    christoffel g d (chartTransition c d w) r a s) z
  apply ContDiffAt.sum
  intro a _
  have hC : ContDiffAt ℝ ∞ (fun w : FourSpace => christoffel g d w r a s)
      (chartTransition c d z) :=
    christoffel_contDiffAt g d _ ht hdet r a s
  have hcomp : ContDiffAt ℝ ∞
      (fun w => christoffel g d (chartTransition c d w) r a s) z :=
    hC.comp z (chartTransition_contDiffAt c d z hz hx)
  exact (chartTransitionMatrix_contDiffAt c d z hz hx a i).mul
    hcomp

theorem chartWeightedConnection_partial (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i j : Fin 4) :
    matrixPartial (chartWeightedConnection g c d j) i z =
      weightedConnectionDerivative (chartTransitionMatrix c d z)
        (fun r => matrixPartial (chartTransitionMatrix c d) r z)
        (fun a => connectionMatrix g d a (chartTransition c d z))
        (fun b a => matrixPartial (connectionMatrix g d a) b (chartTransition c d z)) i j := by
  let F := chartTransition c d
  let J := chartTransitionMatrix c d
  let A := fun a w => connectionMatrix g d a (F w)
  have ht : F z ∈ (chartAt FourSpace d).target := (chartAt FourSpace d).map_source hx
  have hdet := (metricInChart_posDef g d _ ht).det_pos.ne'
  have hF : DifferentiableAt ℝ F z :=
    (chartTransition_contDiffAt c d z hz hx).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hJ (a : Fin 4) : DifferentiableAt ℝ (fun w => J w a j) z :=
    (chartTransitionMatrix_contDiffAt c d z hz hx a j).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hC (a r s : Fin 4) : DifferentiableAt ℝ
      (fun w => connectionMatrix g d a w r s) (F z) :=
    (christoffel_contDiffAt g d _ ht hdet r a s).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hA (a r s : Fin 4) : DifferentiableAt ℝ (fun w => A a w r s) z :=
    (hC a r s).comp z hF
  change matrixPartial (fun w => ∑ a, J w a j • A a w) i z = _
  rw [matrixPartial_sum_four (fun a w => J w a j • A a w) z
    (fun a r s => (hJ a).mul (hA a r s)) i]
  have hs (a : Fin 4) : matrixPartial (fun w => J w a j • A a w) i z =
      partialDeriv (fun w => J w a j) i z • A a z + J z a j • matrixPartial (A a) i z :=
    matrixPartial_smul _ _ z (hJ a) (hA a) i
  have hc (a : Fin 4) : matrixPartial (A a) i z =
      ∑ b, J z b i • matrixPartial (connectionMatrix g d a) b (F z) :=
    matrixPartial_comp hF (hC a) i
  simp only [hs, hc]
  rfl

theorem chart_connection_intertwining (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i : Fin 4) :
    chartTransitionMatrix c d z * connectionMatrix g c i z =
      matrixPartial (chartTransitionMatrix c d) i z +
        chartWeightedConnection g c d i z * chartTransitionMatrix c d z := by
  have he : connectionMatrix g c i z = pulledChartConnection g c d z i := by
    ext r s
    exact christoffel_transition g c d z hz hx r i s
  rw [he]
  exact pulledConnection_equation _ _ _
    (isUnit_iff_ne_zero.mpr (chartTransitionMatrix_det_ne_zero g c d z hz hx))

theorem chart_connection_intertwining_derivative (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i j : Fin 4) :
    matrixPartial (chartTransitionMatrix c d) i z * connectionMatrix g c j z +
      chartTransitionMatrix c d z * matrixPartial (connectionMatrix g c j) i z =
      matrixPartial (matrixPartial (chartTransitionMatrix c d) j) i z +
        matrixPartial (chartWeightedConnection g c d j) i z * chartTransitionMatrix c d z +
          chartWeightedConnection g c d j z * matrixPartial (chartTransitionMatrix c d) i z := by
  let J := chartTransitionMatrix c d
  have hcnear : ∀ᶠ w in 𝓝 z, w ∈ (chartAt FourSpace c).target :=
    (chartAt FourSpace c).open_target.mem_nhds hz
  have hcs : ContinuousAt (chartAt FourSpace c).symm z :=
    (contMDiffAt_symm_of_mem_maximalAtlas (I := I4) (n := ∞)
      (IsManifold.chart_mem_maximalAtlas c) hz).continuousAt
  have hdnear : ∀ᶠ w in 𝓝 z,
      (chartAt FourSpace c).symm w ∈ (chartAt FourSpace d).source :=
    hcs.preimage_mem_nhds ((chartAt FourSpace d).open_source.mem_nhds hx)
  have he : (fun w => J w * connectionMatrix g c j w) =ᶠ[𝓝 z]
      (fun w => matrixPartial J j w + chartWeightedConnection g c d j w * J w) := by
    filter_upwards [hcnear, hdnear] with w hcw hdw
    exact chart_connection_intertwining g c d w hcw hdw j
  have hJ (r s : Fin 4) : ContDiffAt ℝ ∞ (fun w => J w r s) z :=
    chartTransitionMatrix_contDiffAt c d z hz hx r s
  have hC (r s : Fin 4) : DifferentiableAt ℝ (fun w => connectionMatrix g c j w r s) z :=
    (christoffel_contDiffAt g c z hz (metricInChart_posDef g c z hz).det_pos.ne'
      r j s).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hU (r s : Fin 4) : DifferentiableAt ℝ
      (fun w => chartWeightedConnection g c d j w r s) z :=
    (chartWeightedConnection_contDiffAt g c d z hz hx j r s).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hP (r s : Fin 4) : DifferentiableAt ℝ (fun w => matrixPartial J j w r s) z :=
    (((hJ r s).fderiv_right (m := ∞) (by first | simp | exact_mod_cast le_top)).clm_apply contDiffAt_const).differentiableAt
      (by first | simp | exact_mod_cast le_top)
  have hprod (r s : Fin 4) : DifferentiableAt ℝ
      (fun w => (chartWeightedConnection g c d j w * J w) r s) z := by
    change DifferentiableAt ℝ (fun w => ∑ p,
      chartWeightedConnection g c d j w r p * J w p s) z
    exact DifferentiableAt.fun_sum (fun p _ => (hU r p).mul
      ((hJ p s).differentiableAt (by simp)))
  have h := matrixPartial_congr he i
  rw [matrixPartial_mul J (connectionMatrix g c j) z
      (fun r s => (hJ r s).differentiableAt (by simp)) hC i,
    matrixPartial_add (matrixPartial J j) (fun w => chartWeightedConnection g c d j w * J w)
      z hP hprod i,
    matrixPartial_mul (chartWeightedConnection g c d j) J z hU
      (fun r s => (hJ r s).differentiableAt (by simp)) i] at h
  simpa only [add_assoc] using h

theorem chart_curvature_intertwining (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i j : Fin 4) :
    chartTransitionMatrix c d z * coordinateCurvatureMatrix g c i j z =
      (matrixPartial (chartWeightedConnection g c d j) i z -
        matrixPartial (chartWeightedConnection g c d i) j z +
          chartWeightedConnection g c d i z * chartWeightedConnection g c d j z -
            chartWeightedConnection g c d j z * chartWeightedConnection g c d i z) *
              chartTransitionMatrix c d z := by
  have hcomm := matrixPartial_comm (chartTransitionMatrix c d) z
    (chartTransitionMatrix_contDiffAt c d z hz hx) i j
  exact curvature_intertwining_of_connection _ _ _ _ _ _ _ _ _ _ _ _
    (chart_connection_intertwining g c d z hz hx i)
    (chart_connection_intertwining g c d z hz hx j)
    (chart_connection_intertwining_derivative g c d z hz hx i j)
    (by simpa only [hcomm] using
      chart_connection_intertwining_derivative g c d z hz hx j i)

theorem chartWeightedConnection_curvature (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i j : Fin 4) :
    matrixPartial (chartWeightedConnection g c d j) i z -
        matrixPartial (chartWeightedConnection g c d i) j z +
      chartWeightedConnection g c d i z * chartWeightedConnection g c d j z -
        chartWeightedConnection g c d j z * chartWeightedConnection g c d i z =
      ∑ a, ∑ b, (chartTransitionMatrix c d z a i * chartTransitionMatrix c d z b j) •
        coordinateCurvatureMatrix g d a b (chartTransition c d z) := by
  rw [chartWeightedConnection_partial g c d z hz hx,
    chartWeightedConnection_partial g c d z hz hx]
  simpa only [chartWeightedConnection, coordinateCurvatureMatrix] using
    weightedConnection_curvature (chartTransitionMatrix c d z)
      (fun r => matrixPartial (chartTransitionMatrix c d) r z)
      (fun a => connectionMatrix g d a (chartTransition c d z))
      (fun b a => matrixPartial (connectionMatrix g d a) b (chartTransition c d z))
      (fun r s t => jacobian_partials_commute (chartTransition_contDiffAt c d z hz hx) t r s)
      i j

/-- The actual (1,3)-curvature in two overlapping metric charts. -/
theorem coordinateCurvatureMatrix_transition (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) (i j : Fin 4) :
    coordinateCurvatureMatrix g c i j z = (chartTransitionMatrix c d z)⁻¹ *
      (∑ a, ∑ b, (chartTransitionMatrix c d z a i * chartTransitionMatrix c d z b j) •
        coordinateCurvatureMatrix g d a b (chartTransition c d z)) *
          chartTransitionMatrix c d z := by
  have h := congrArg (fun A : Mat4 => (chartTransitionMatrix c d z)⁻¹ * A)
    (chart_curvature_intertwining g c d z hz hx i j)
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr
    (chartTransitionMatrix_det_ne_zero g c d z hz hx)),
    chartWeightedConnection_curvature g c d z hz hx i j] at h
  simpa only [Matrix.mul_assoc] using h

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ChartVolumeDensity
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local metric volume density and its exact coordinate change law.
Identification with the metric Hausdorff measure is a separate step. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chartVolumeDensity_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (chartVolumeDensity g c) z := by
  have hd : ContDiffAt ℝ ∞ (fun w => (metricInChart g c w).det) z := by
    simp only [Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ _
    exact contDiffAt_const.mul
      (contDiffAt_prod fun i _ => metricInChart_contDiffAt g c z hz (σ i) i)
  exact hd.sqrt (metricInChart_posDef g c z hz).det_pos.ne'

/-- In orthonormal frame coordinates the metric density cancels the
absolute determinant of the frame matrix. -/
theorem chartVolumeDensity_mul_frame_det (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (E : Mat4)
    (hE : Eᵀ * metricInChart g c z * E = 1) :
    chartVolumeDensity g c z * |E.det| = 1 := by
  have hd : (metricInChart g c z).det * E.det ^ 2 = 1 := by
    have he := congrArg Matrix.det hE
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at he
    calc
      _ = E.det * (metricInChart g c z).det * E.det := by ring
      _ = 1 := he
  have hs := congrArg Real.sqrt hd
  rw [Real.sqrt_mul (metricInChart_posDef g c z hz).det_pos.le,
    Real.sqrt_sq_eq_abs, Real.sqrt_one] at hs
  exact hs

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CoordinateSecondBianchi
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Specialization of the second Bianchi algebra to the actual smooth
Christoffel symbols, with all four curvature slots differentiated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem matrixPartial_coordinateCurvature (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k : Fin 4) :
    matrixPartial (coordinateCurvatureMatrix g c j k) i z =
      CovariantBianchi.curvatureDerivative
        (fun r => connectionMatrix g c r z)
        (fun r s => matrixPartial (connectionMatrix g c s) r z)
        (fun r s t => matrixPartial (matrixPartial (connectionMatrix g c t) s) r z)
        i j k := by
  let A := connectionMatrix g c j
  let B := connectionMatrix g c k
  let F := matrixPartial B j
  let H := matrixPartial A k
  have hA : ∀ a b, DifferentiableAt ℝ (fun w => A w a b) z := fun a b =>
    (christoffel_contDiffAt g c z hz hdet a j b).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hB : ∀ a b, DifferentiableAt ℝ (fun w => B w a b) z := fun a b =>
    (christoffel_contDiffAt g c z hz hdet a k b).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hF : ∀ a b, DifferentiableAt ℝ (fun w => F w a b) z := fun a b =>
    (connectionMatrix_partial_contDiffAt g c z hz hdet j k a b).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hH : ∀ a b, DifferentiableAt ℝ (fun w => H w a b) z := fun a b =>
    (connectionMatrix_partial_contDiffAt g c z hz hdet k j a b).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hFH : ∀ a b, DifferentiableAt ℝ (fun w => (F w - H w) a b) z :=
    fun a b => (hF a b).sub (hH a b)
  have hAB := product_entries_differentiable A B z hA hB
  have hBA := product_entries_differentiable B A z hB hA
  have hsum : ∀ a b,
      DifferentiableAt ℝ (fun w => ((F w - H w) + A w * B w) a b) z :=
    fun a b => (hFH a b).add (hAB a b)
  change matrixPartial (fun w => (F w - H w) + A w * B w - B w * A w) i z = _
  rw [matrixPartial_sub _ _ z hsum hBA i,
    matrixPartial_add _ _ z hFH hAB i, matrixPartial_sub F H z hF hH i,
    matrixPartial_mul A B z hA hB i, matrixPartial_mul B A z hB hA i]
  dsimp only [A, B, F, H, CovariantBianchi.curvatureDerivative]
  abel

theorem coordinateCovariantCurvatureDerivative_eq_algebra
    (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k : Fin 4) :
    coordinateCovariantCurvatureDerivative g c z i j k =
      CovariantBianchi.tensorCurvatureDerivative
        (fun r => connectionMatrix g c r z)
        (fun r s => matrixPartial (connectionMatrix g c s) r z)
        (fun r s t => matrixPartial (matrixPartial (connectionMatrix g c t) s) r z)
        i j k := by
  unfold coordinateCovariantCurvatureDerivative
  rw [matrixPartial_coordinateCurvature g c z hz hdet]
  simp only [coordinateCurvatureMatrix_eq_algebra]
  rfl

theorem coordinate_second_bianchi (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k : Fin 4) :
    coordinateCovariantCurvatureDerivative g c z i j k +
      coordinateCovariantCurvatureDerivative g c z j k i +
      coordinateCovariantCurvatureDerivative g c z k i j = 0 := by
  simp only [coordinateCovariantCurvatureDerivative_eq_algebra g c z hz hdet]
  apply CovariantBianchi.tensorCurvatureDerivative_cyclic
  · intro r s p
    exact christoffel_comm g c z p r s
  · intro r s t
    exact matrixPartial_comm (connectionMatrix g c t) z
      (fun a b => christoffel_contDiffAt g c z hz hdet a t b) r s

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CotangentHamiltonian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cotangent-coordinate calculation used by the geodesic measure
argument: a Hamiltonian vector field has zero coordinate divergence.
Only the four-dimensional position and momentum coordinates needed here
are introduced. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

/-- Coordinate divergence in the position and momentum basis. -/
def cotangentDivergence (X : CotangentCoordinates → CotangentCoordinates)
    (z : CotangentCoordinates) : ℝ :=
  ∑ r, (fderiv ℝ (fun w => (X w).1 r) z (positionDirection r) +
    fderiv ℝ (fun w => (X w).2 r) z (momentumDirection r))

theorem hamiltonian_partial_derivative
    (H : CotangentCoordinates → ℝ) (z u v : CotangentCoordinates)
    (hH : ContDiffAt ℝ ∞ H z) :
    fderiv ℝ (fun w => fderiv ℝ H w u) z v =
      fderiv ℝ (fderiv ℝ H) z v u := by
  have hd := ((hH.fderiv_right (m := ∞) (by first | simp | exact_mod_cast le_top)).differentiableAt (by first | simp | exact_mod_cast le_top)).hasFDerivAt
  have h := congrArg (fun L : CotangentCoordinates →L[ℝ] ℝ => L v)
    (hd.clm_apply (hasFDerivAt_const u z)).fderiv
  simpa using h

/-- The two mixed derivatives cancel in each position--momentum pair.
This proves the local divergence statement; flow Jacobians and restriction
to the unit-energy shell are separate geometric steps. -/
theorem cotangentHamiltonian_divergence_zero
    (H : CotangentCoordinates → ℝ) (z : CotangentCoordinates)
    (hH : ContDiffAt ℝ ∞ H z) :
    cotangentDivergence (cotangentHamiltonianField H) z = 0 := by
  unfold cotangentDivergence
  apply Finset.sum_eq_zero
  intro r _
  change fderiv ℝ (fun w => fderiv ℝ H w (momentumDirection r)) z
      (positionDirection r) +
    fderiv ℝ (fun w => -fderiv ℝ H w (positionDirection r)) z
      (momentumDirection r) = 0
  rw [fderiv_fun_neg, neg_apply,
    hamiltonian_partial_derivative H z (momentumDirection r) (positionDirection r) hH,
    hamiltonian_partial_derivative H z (positionDirection r) (momentumDirection r) hH]
  have hs := hH.isSymmSndFDerivAt (by simp) (positionDirection r) (momentumDirection r)
  rw [hs]
  exact add_neg_cancel _

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CotangentJacobian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The eight-coordinate Jacobian calculation for the cotangent flow.
The variational equation is kept explicit here; it will be supplied by
the derivative of the actual flow with respect to its initial value. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

def cotangentComponent (z : CotangentCoordinates) : CotangentIndex → ℝ :=
  Sum.elim (fun r => z.1 r) (fun r => z.2 r)

def cotangentDirection : CotangentIndex → CotangentCoordinates :=
  Sum.elim positionDirection momentumDirection

theorem cotangentBasis_apply (i : CotangentIndex) :
    cotangentBasis i = cotangentDirection i := by
  cases i <;>
    simp [cotangentBasis, cotangentDirection, Module.Basis.prod_apply,
      positionDirection, momentumDirection, coordinateVector]

theorem cotangentBasis_repr (z : CotangentCoordinates) (i : CotangentIndex) :
    cotangentBasis.repr z i = cotangentComponent z i := by
  cases i <;> simp [cotangentBasis, cotangentComponent]

def cotangentProjection (i : CotangentIndex) :
    CotangentCoordinates →L[ℝ] ℝ :=
  (cotangentBasis.coord i).toContinuousLinearMap

theorem cotangentProjection_apply (i : CotangentIndex)
    (z : CotangentCoordinates) :
    cotangentProjection i z = cotangentComponent z i :=
  cotangentBasis_repr z i

def cotangentJacobian (X : CotangentCoordinates → CotangentCoordinates)
    (z : CotangentCoordinates) : CotangentMatrix :=
  fun i j => fderiv ℝ (fun w => cotangentComponent (X w) i) z
    (cotangentDirection j)

theorem cotangentJacobian_eq_toMatrix
    (X : CotangentCoordinates → CotangentCoordinates) (z : CotangentCoordinates)
    (hX : DifferentiableAt ℝ X z) :
    cotangentJacobian X z =
      LinearMap.toMatrix cotangentBasis cotangentBasis (fderiv ℝ X z).toLinearMap := by
  ext i j
  have h := (cotangentProjection i).hasFDerivAt.comp z hX.hasFDerivAt
  have he : (cotangentProjection i) ∘ X =
      fun w => cotangentComponent (X w) i := by
    funext w
    exact cotangentProjection_apply i (X w)
  rw [he] at h
  have hd : fderiv ℝ (fun w => cotangentComponent (X w) i) z =
      (cotangentProjection i).comp (fderiv ℝ X z) := by
    exact h.fderiv
  change fderiv ℝ (fun w => cotangentComponent (X w) i) z (cotangentDirection j) = _
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, cotangentProjection_apply,
    LinearMap.toMatrix_apply, cotangentBasis_apply, cotangentBasis_repr]
  rfl

theorem cotangentJacobian_det
    (X : CotangentCoordinates → CotangentCoordinates) (z : CotangentCoordinates)
    (hX : DifferentiableAt ℝ X z) :
    (cotangentJacobian X z).det = (fderiv ℝ X z).det := by
  rw [cotangentJacobian_eq_toMatrix X z hX]
  exact LinearMap.det_toMatrix cotangentBasis (fderiv ℝ X z).toLinearMap

theorem cotangentJacobian_trace (X : CotangentCoordinates → CotangentCoordinates)
    (z : CotangentCoordinates) :
    (cotangentJacobian X z).trace = cotangentDivergence X z := by
  simp only [Matrix.trace, Matrix.diag, cotangentJacobian, Fintype.sum_sum_type,
    cotangentComponent, cotangentDirection, Sum.elim_inl, Sum.elim_inr]
  exact (Finset.sum_add_distrib).symm

theorem cotangentHamiltonian_jacobian_trace
    (H : CotangentCoordinates → ℝ) (z : CotangentCoordinates)
    (hH : ContDiffAt ℝ ∞ H z) :
    (cotangentJacobian (cotangentHamiltonianField H) z).trace = 0 := by
  rw [cotangentJacobian_trace]
  exact cotangentHamiltonian_divergence_zero H z hH

/-- Once the actual flow derivative satisfies its variational equation,
the Hamiltonian mixed-derivative identity makes its determinant constant. -/
theorem cotangentHamiltonian_variational_det
    (H : CotangentCoordinates → ℝ) (γ : ℝ → CotangentCoordinates)
    (J : ℝ → CotangentMatrix) (a b s t : ℝ)
    (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b)
    (hH : ∀ r ∈ Set.Ioo a b, ContDiffAt ℝ ∞ H (γ r))
    (hJ : ∀ r ∈ Set.Ioo a b, ∀ i j,
      HasDerivAt (fun u => J u i j)
        ((cotangentJacobian (cotangentHamiltonianField H) (γ r) * J r) i j) r) :
    (J s).det = (J t).det := by
  have hd (r : ℝ) (hr : r ∈ Set.Ioo a b) :=
    hasDerivAt_cotangentDeterminant J
      (cotangentJacobian (cotangentHamiltonianField H) (γ r)) r (hJ r hr)
  have hz (r : ℝ) (hr : r ∈ Set.Ioo a b) :
      HasDerivAt (fun u => (J u).det) 0 r := by
    simpa only [cotangentHamiltonian_jacobian_trace H (γ r) (hH r hr), zero_mul]
      using hd r hr
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun r hr => (hz r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hz r hr).deriv) hs ht

/-- The derivative with respect to the initial point starts at the
identity matrix, so the constant Jacobian determinant is exactly one. -/
theorem cotangentHamiltonian_variational_det_one
    (H : CotangentCoordinates → ℝ) (γ : ℝ → CotangentCoordinates)
    (J : ℝ → CotangentMatrix) (a b t : ℝ)
    (hzero : 0 ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b)
    (hH : ∀ r ∈ Set.Ioo a b, ContDiffAt ℝ ∞ H (γ r))
    (hJ : ∀ r ∈ Set.Ioo a b, ∀ i j,
      HasDerivAt (fun u => J u i j)
        ((cotangentJacobian (cotangentHamiltonianField H) (γ r) * J r) i j) r)
    (hinit : J 0 = 1) : (J t).det = 1 := by
  have h := cotangentHamiltonian_variational_det H γ J a b 0 t hzero ht hH hJ
  rw [hinit, Matrix.det_one] at h
  exact h.symm

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CotangentVolume
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The change-of-variables step for local cotangent maps. The determinant
condition is the conclusion of the variational calculation, not an
assumption of measure preservation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set

noncomputable section

/-- A locally injective map with unit absolute derivative determinant
preserves coordinate volume on its domain. -/
theorem cotangent_map_volume_of_det_one
    (f : CotangentCoordinates → CotangentCoordinates)
    (s : Set CotangentCoordinates) (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) (hinj : InjOn f s)
    (hdet : ∀ x ∈ s, |(cotangentJacobian f x).det| = 1) :
    Measure.map f (volume.restrict s) = volume.restrict (f '' s) := by
  let : IsAddHaarMeasure (volume : Measure CotangentCoordinates) :=
    inferInstanceAs (IsAddHaarMeasure
      ((volume : Measure FourSpace).prod (volume : Measure FourSpace)))
  have hd : ∀ x ∈ s, |(fderiv ℝ f x).det| = 1 := by
    intro x hx
    rw [← cotangentJacobian_det f x (hf x hx)]
    exact hdet x hx
  have hden : (volume.restrict s).withDensity
      (fun x => ENNReal.ofReal |(fderiv ℝ f x).det|) = volume.restrict s := by
    calc
      _ = (volume.restrict s).withDensity 1 := by
        apply withDensity_congr_ae
        filter_upwards [ae_restrict_mem hs] with x hx
        simp only [hd x hx, ENNReal.ofReal_one, Pi.one_apply]
      _ = _ := withDensity_one
  have h := map_withDensity_abs_det_fderiv_eq_addHaar volume hs.nullMeasurableSet
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) hinj
  rwa [hden] at h

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureContraction
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quaternion contractions in the derivative-slot Green formula. -/

namespace PositiveEinsteinFour.CurvatureContraction

open scoped BigOperators
open TraceHessian Bianchi Angular

noncomputable section

/-- Orthogonality includes the normalization of the curvature two-forms. -/
theorem plus_twoForm_pairing (s r : Fin 3) :
    (∑ i, ∑ k, quaternionMatrix s i k * quaternionMatrix r i k) =
      if s = r then (4 : ℝ) else 0 := by
  simp only [Fin.sum_univ_succ]
  fin_cases s <;> fin_cases r <;> simp [TraceHessian.quaternionMatrix] <;> (try split_ifs) <;> norm_num

end

end PositiveEinsteinFour.CurvatureContraction

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylDerivative
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate covariant derivatives of the actual curvature tensor. The
scalar-curvature contribution is subtracted in the Ricci=3g normalization.
The definitions retain all tensor slots until after differentiation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The actual plus-block covariant gradient in an orthonormal frame. -/
def plusWeylGradient (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (i : Fin 4) : Mat3 :=
  gradientBlock (frameTensor e.matrix
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c)))
    TraceHessian.quaternionMatrix i

/-- The actual plus-block covariant Hessian, before any trace decomposition. -/
def plusWeylHessian (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (i j : Fin 4) : Mat3 :=
  hessianBlock (frameTensor e.matrix
    (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
      (chartAt FourSpace c c))) TraceHessian.quaternionMatrix i j

/-- The opposite block is differentiated in the same actual coordinate
connection, before the orthonormal frame and Hodge basis are applied. -/
def minusWeylGradient (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (i : Fin 4) : Mat3 :=
  gradientBlock (frameTensor e.matrix
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c)))
    oppositeQuaternion i

def minusWeylHessian (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (i j : Fin 4) : Mat3 :=
  hessianBlock (frameTensor e.matrix
    (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
      (chartAt FourSpace c c))) oppositeQuaternion i j

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureCoordinateSmoothness
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local regularity of the actual curvature and its coordinate covariant
derivatives, on the nonsingular part of a metric chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_contDiffAt (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) {n : ℕ}
    (T : FourSpace → CovariantCoordinates n)
    (hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z) (a : Fin (n + 1) → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => covariantDerivative g c T w a) z := by
  unfold covariantDerivative
  apply (((hT _).fderiv_right (m := ∞) (by first | simp | exact_mod_cast le_top)).clm_apply contDiffAt_const).sub
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro b _
  exact (christoffel_contDiffAt g c z hz hdet b (a 0) (a i.succ)).mul (hT _)

/-- Linearity is proved for differentiable coordinate tensors, so it also
applies to the actual curvature fields on a metric chart. -/
theorem covariantDerivative_sub (g : SmoothMetric M) (c : M) (z : FourSpace)
    {n : ℕ} (S T : FourSpace → CovariantCoordinates n)
    (hS : ∀ a, DifferentiableAt ℝ (fun w => S w a) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z) :
    covariantDerivative g c (fun w => S w - T w) z =
      covariantDerivative g c S z - covariantDerivative g c T z := by
  funext a
  have hd : partialDeriv (fun w => S w (fun i => a i.succ) -
        T w (fun i => a i.succ)) (a 0) z =
      partialDeriv (fun w => S w (fun i => a i.succ)) (a 0) z -
        partialDeriv (fun w => T w (fun i => a i.succ)) (a 0) z := by
    exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector (a 0)))
      (fderiv_fun_sub (hS _) (hT _))
  simp only [covariantDerivative, Pi.sub_apply, hd, mul_sub,
    Finset.sum_sub_distrib]
  ring

theorem covariantDerivative_congr (g : SmoothMetric M) (c : M) {z : FourSpace}
    {n : ℕ} {S T : FourSpace → CovariantCoordinates n}
    (h : S =ᶠ[nhds z] T) :
    covariantDerivative g c S z = covariantDerivative g c T z := by
  funext a
  have hv : S z = T z := h.eq_of_nhds
  have hd : (fun w => S w (fun i => a i.succ)) =ᶠ[nhds z]
      (fun w => T w (fun i => a i.succ)) :=
    h.mono fun w hw => congrFun hw _
  simp only [covariantDerivative, partialDeriv, hd.fderiv_eq, hv]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameBundle
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual orthonormal frames with the topology inherited from tangent
vectors. Using the tangent-bundle topology is essential: chart coordinates
at varying base points do not give a global product trivialization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

instance instBorelSpaceFrameBundle (g : SmoothMetric M) : BorelSpace (FrameBundle g) := ⟨rfl⟩

theorem frameBase_surjective (g : SmoothMetric M) :
    Function.Surjective (FrameBundle.base : FrameBundle g → M) :=
  fun c => ⟨frameAt g c, rfl⟩

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameRotation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_one _root_.OAI.PositiveEinsteinFour.SectionalPlane.act_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete each unit direction to its quaternionic orthonormal frame.
This relates spherical fiber averages to actual orthonormal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular
open scoped Manifold ContDiff

noncomputable section

theorem directionFrameMatrix_orthogonal (q : Directions) :
    (directionFrameMatrix q)ᵀ * directionFrameMatrix q = 1 := by
  ext i j
  change (∑ k, directionFrameMatrix q k i * directionFrameMatrix q k j) =
    if i = j then 1 else 0
  calc
    _ = (∑ k, q.val k ^ 2) * (if i = j then 1 else 0) := by
      fin_cases i <;> fin_cases j <;>
        simp [directionFrameMatrix, Fin.sum_univ_succ]
      all_goals ring
    _ = _ := by rw [direction_sum_sq]; simp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def OrthonormalFrame.turn {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (q : Directions) : OrthonormalFrame g c where
  matrix := e.matrix * directionFrameMatrix q
  orthonormal := by
    calc
      (e.matrix * directionFrameMatrix q)ᵀ * chartMetric g c *
          (e.matrix * directionFrameMatrix q) =
          (directionFrameMatrix q)ᵀ *
            (e.matrixᵀ * chartMetric g c * e.matrix) * directionFrameMatrix q := by
        rw [Matrix.transpose_mul]
        noncomm_ring
      _ = 1 := by rw [e.orthonormal, mul_one, directionFrameMatrix_orthogonal]

theorem OrthonormalFrame.turn_first {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (q : Directions) :
    (e.turn q).vector 0 = e.map q.val := by
  ext i
  change (∑ j, e.matrix i j * directionFrameMatrix q j 0) =
    ∑ j, e.matrix i j * q.val j
  simp only [directionFrameMatrix_zero]

def frameTurn {g : SmoothMetric M} {c : M} (e : OrthonormalFrame g c)
    (q : Directions) : FrameBundle g := ⟨c, e.turn q⟩

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylNormal
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

local instance instNormedAddCommGroupMat3_r57b6aa_1 : NormedAddCommGroup Mat3 := Matrix.frobeniusNormedAddCommGroup
def normalCurvature (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c)
    (q : Directions) : Mat3 := fun i j =>
  normalEvaluation q i j (frameCurvature g c e)

def normalCurvatureDeviation (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (q : Directions) : Mat3 :=
  normalCurvature g c e q - 1

/-- The derivative field uses the metric's actual covariant derivatives. -/
def normalCurvatureDerivative (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (q : Directions) : Mat3 :=
  normalDerivative (plusWeylGradient g c e) (minusWeylGradient g c e) q

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameCurvature
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two fields on the actual orthonormal frame bundle that enter the
geodesic mean-square argument. They are evaluations of the metric curvature
and its covariant derivative, with no independent curvature field. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular
open scoped Manifold ContDiff

noncomputable section

theorem firstDirection_normal (i : Fin 3) (a : Fin 4) :
    normalVector firstDirection i a = if a = i.succ then 1 else 0 := by
  fin_cases i <;> fin_cases a <;>
    simp [normalVector, firstDirection, coordinateVector,
      TraceHessian.quaternionMatrix]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameCurvatureField (g : SmoothMetric M) (e : FrameBundle g) : Mat3 :=
  normalCurvatureDeviation g e.base e.frame firstDirection

def frameCurvatureDerivative (g : SmoothMetric M) (e : FrameBundle g) : Mat3 :=
  normalCurvatureDerivative g e.base e.frame firstDirection

theorem frameCurvatureField_apply (g : SmoothMetric M) (e : FrameBundle g)
    (i j : Fin 3) :
    frameCurvatureField g e i j =
      frameCurvature g e.base e.frame i.succ 0 0 j.succ - if i = j then 1 else 0 := by
  simp only [frameCurvatureField, normalCurvatureDeviation, normalCurvature,
    Matrix.sub_apply, Matrix.one_apply, normalEvaluation, firstDirection_normal,
    firstDirection_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rfl

theorem frameCurvatureDerivative_eq (g : SmoothMetric M) (e : FrameBundle g) :
    frameCurvatureDerivative g e =
      normalDeviation (plusWeylGradient g e.base e.frame 0)
        (minusWeylGradient g e.base e.frame 0) firstDirection := by
  simp only [frameCurvatureDerivative, normalCurvatureDerivative, normalDerivative,
    directional, firstDirection_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RiemannianVolume
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measure in the geometric application is fixed by the metric. In four
Euclidean dimensions the diameter-normalized Hausdorff measure is multiplied
by the unit-ball factor `(pi^2 / 2) / 2^4`. Positivity and finiteness are kept
separate from the elementary probability normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Bundle
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem normalizedVolume_isProbability {g : SmoothMetric M} (h : FinitePositiveVolume g) :
    IsProbabilityMeasure (normalizedVolume g) := by
  constructor
  change ((volumeMeasure g Set.univ)⁻¹ • volumeMeasure g) Set.univ = 1
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt h.positive) (ne_of_lt h.finite)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameAverages
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

/-- Generic spherical disintegration, parameterized by the frame measure. -/
structure BrinKarcherAveraging (g : SmoothMetric M) (μ : Measure (FrameBundle g)) : Prop where
  probability : IsProbabilityMeasure μ
  fiberFormula : ∀ (F : FrameBundle g → ℝ) (A : M → ℝ),
    Integrable F μ → Integrable A (normalizedVolume g) → DirectionInvariant F →
    (∀ c (e : OrthonormalFrame g c), (∫ q, F (frameTurn e q) ∂sphereMeasure) = A c) →
    (∫ e, F e ∂μ) = ∫ c, A c ∂normalizedVolume g

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameOrientation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

def plusNorm {g : SmoothMetric M} (o : FrameOrientation g) (c : M) : ℝ :=
  normalizedBlockNorm (plusWeyl g c (o.frame c))

def minusNorm {g : SmoothMetric M} (o : FrameOrientation g) (c : M) : ℝ :=
  normalizedBlockNorm (minusWeyl g c (o.frame c))

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameFlow
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

theorem FrameFlow.continuous_slice {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (φ : FrameFlow g μ) (t : ℝ) : Continuous (φ.map t) :=
  φ.continuous.comp (continuous_const.prodMk continuous_id)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricHessian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

/-- Three successive covariant derivatives, retaining all derivative slots. -/
def plusWeylThirdDerivative (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i j k : Fin 4) : Mat3 :=
  blockCoordinates (fun a =>
    frameTensor e.matrix
      (covariantDerivative g c
        (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c)))
        (chartAt FourSpace c c))
      (Fin.cons i (Fin.cons j (Fin.cons k a)))) quaternionMatrix

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricTensorCompatibility
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric compatibility for the actual coordinate tensor derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_metricTensor (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hG : IsUnit (metricInChart g c z).det) :
    covariantDerivative g c (metricTensorCoordinates g c) z = 0 := by
  funext a
  have hm := christoffel_metric_compatibility g c z hG (a 0) (a 1) (a 2)
  rw [Finset.sum_add_distrib] at hm
  have hfirst : (∑ b, christoffel g c z b (a 0) (a 1) *
      metricInChart g c z b (a 2)) =
      ∑ b, metricInChart g c z (a 2) b * christoffel g c z b (a 0) (a 1) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [show metricInChart g c z b (a 2) = metricInChart g c z (a 2) b from g.symm _ _ _]
    ring
  have hsecond : (∑ b, christoffel g c z b (a 0) (a 2) *
      metricInChart g c z (a 1) b) =
      ∑ b, metricInChart g c z (a 1) b * christoffel g c z b (a 0) (a 2) := by
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp only [covariantDerivative, metricTensorCoordinates, Fin.sum_univ_two]
  change partialDeriv (fun w => metricInChart g c w (a 1) (a 2)) (a 0) z -
    ((∑ b, christoffel g c z b (a 0) (a 1) * metricInChart g c z b (a 2)) +
     (∑ b, christoffel g c z b (a 0) (a 2) * metricInChart g c z (a 1) b)) = 0
  rw [hfirst, hsecond, ← hm]
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
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

/-- The precise algebraic and covariant identities used from the classical
Einstein/Weyl calculus, specialized to the plus block and Ricci `3g`.
All fields refer to the metric's actual tensors. -/
structure WeylCovariantIdentities (g : SmoothMetric M) : Prop where
  symmetric : ∀ e : FrameBundle g, TraceHessian.symmetric (plusWeyl g e.base e.frame)
  traceFree : ∀ e : FrameBundle g, TraceHessian.traceFree (plusWeyl g e.base e.frame)
  hessianMatrix : ∀ (e : FrameBundle g) i j,
    TraceHessian.symmetric (plusWeylHessian g e.base e.frame i j) ∧
      TraceHessian.traceFree (plusWeylHessian g e.base e.frame i j)
  hessianBianchi : ∀ (e : FrameBundle g) i r,
    HighestHessian.divergence (plusWeylHessian g e.base e.frame) i r = 0
  hessianCommutator : ∀ (e : FrameBundle g) i j a b,
    plusWeylHessian g e.base e.frame i j a b -
      plusWeylHessian g e.base e.frame j i a b =
        bundleCurvatureAction (plusWeyl g e.base e.frame) i j
          (plusWeyl g e.base e.frame) a b

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

local instance greenDataNormedRing_r57b6aa_1 : NormedRing Mat := Matrix.frobeniusNormedRing
local instance greenDataNormedSpace_r57b6aa_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
local instance greenDataNormedAlgebra_r57b6aa_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
/-- Petersen's tensor commutators and ordinary differentiation in parallel
frames, with Brin--Karcher measure-preserving flows. Ricci is normalized to
`3g`; the last two curvature entries are reversed for the covector action.
The normalization of an arbitrary Einstein metric is separate. -/
structure MetricGreenData (g : SmoothMetric M) (μ : Measure (FrameBundle g)) where
  flow : Fin 4 → FrameFlow g μ
  weyl : WeylCovariantIdentities g
  continuousWeyl : Continuous (fun e : FrameBundle g => plusWeyl g e.base e.frame)
  continuousGradient : ∀ i, Continuous
    (fun e : FrameBundle g => plusWeylGradient g e.base e.frame i)
  continuousHessian : ∀ i j, Continuous
    (fun e : FrameBundle g => plusWeylHessian g e.base e.frame i j)
  continuousThird : ∀ i j k, Continuous
    (fun e : FrameBundle g => plusWeylThirdDerivative g e.base e.frame i j k)
  derivativeWeyl : ∀ k t e, HasDerivAt
    (fun s => plusWeyl g ((flow k).map s e).base ((flow k).map s e).frame)
    (plusWeylGradient g ((flow k).map t e).base ((flow k).map t e).frame k) t
  derivativeGradient : ∀ k j t e, HasDerivAt
    (fun s => plusWeylGradient g ((flow k).map s e).base ((flow k).map s e).frame j)
    (plusWeylHessian g ((flow k).map t e).base ((flow k).map t e).frame k j) t
  derivativeHessian : ∀ k i j t e, HasDerivAt
    (fun s => plusWeylHessian g ((flow k).map s e).base ((flow k).map s e).frame i j)
    (plusWeylThirdDerivative g ((flow k).map t e).base ((flow k).map t e).frame k i j) t
  gradientBianchi : ∀ (e : FrameBundle g) r i,
    gradientDivergence (plusWeylGradient g e.base e.frame) r i = 0
  innerCommutator : ∀ (e : FrameBundle g) i k j,
    plusWeylThirdDerivative g e.base e.frame i k j -
      plusWeylThirdDerivative g e.base e.frame i j k =
    bundleCurvatureDerivative (plusWeylGradient g e.base e.frame i) k j
      (plusWeyl g e.base e.frame) +
    bundleCurvatureAction (plusWeyl g e.base e.frame) k j
      (plusWeylGradient g e.base e.frame i)
  outerCommutator : ∀ (e : FrameBundle g) i k j,
    plusWeylThirdDerivative g e.base e.frame i k j -
      plusWeylThirdDerivative g e.base e.frame k i j =
    bundleCurvatureAction (plusWeyl g e.base e.frame) i k
      (plusWeylGradient g e.base e.frame j) +
    ∑ a, frameCurvature g e.base e.frame i k a j • plusWeylGradient g e.base e.frame a
  ricci : ∀ (e : FrameBundle g) j a,
    (∑ i, frameCurvature g e.base e.frame i j a i) = if j = a then 3 else 0

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

def scalarGradient (g : SmoothMetric M) (a : M → ℝ) (e : FrameBundle g) (i : Fin 4) : ℝ :=
  frameTensor e.frame.matrix
    (covariantDerivative g e.base (scalarCoordinates a e.base) (chartAt FourSpace e.base e.base)) ![i]

def scalarHessian (g : SmoothMetric M) (a : M → ℝ) (e : FrameBundle g) (i j : Fin 4) : ℝ :=
  frameTensor e.frame.matrix
    (covariantDerivative g e.base (covariantDerivative g e.base (scalarCoordinates a e.base))
      (chartAt FourSpace e.base e.base)) ![i, j]

def scalarThird (g : SmoothMetric M) (a : M → ℝ) (e : FrameBundle g) (i j k : Fin 4) : ℝ :=
  frameTensor e.frame.matrix
    (covariantDerivative g e.base (covariantDerivative g e.base
      (covariantDerivative g e.base (scalarCoordinates a e.base)))
      (chartAt FourSpace e.base e.base)) ![i, j, k]

def scalarLaplacian (g : SmoothMetric M) (a : M → ℝ) (e : FrameBundle g) : ℝ :=
  ∑ i, scalarHessian g a e i i

/-- Raw classical scalar calculus, stated on the actual metric tensors. -/
structure ScalarCovariantData {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) (a : M → ℝ) where
  continuousValue : Continuous (fun e : FrameBundle g => a e.base)
  continuousGradient : ∀ i, Continuous (fun e : FrameBundle g => scalarGradient g a e i)
  continuousHessian : ∀ i j, Continuous (fun e : FrameBundle g => scalarHessian g a e i j)
  continuousThird : ∀ i j k, Continuous (fun e : FrameBundle g => scalarThird g a e i j k)
  derivativeValue : ∀ i t e, HasDerivAt (fun s => a ((d.flow i).map s e).base)
    (scalarGradient g a ((d.flow i).map t e) i) t
  derivativeGradient : ∀ i j t e, HasDerivAt
    (fun s => scalarGradient g a ((d.flow i).map s e) j)
    (scalarHessian g a ((d.flow i).map t e) i j) t
  derivativeHessian : ∀ i j k t e, HasDerivAt
    (fun s => scalarHessian g a ((d.flow i).map s e) j k)
    (scalarThird g a ((d.flow i).map t e) i j k) t
  hessianSymmetric : ∀ e i j, scalarHessian g a e i j = scalarHessian g a e j i
  commutator : ∀ e i j k, scalarThird g a e i j k - scalarThird g a e j i k =
    ∑ l, frameCurvature g e.base e.frame i j l k * scalarGradient g a e l

end
end PositiveEinsteinFour.Geometry
end


section

/-! The opposite Weyl block acts on the derivative slots of the plus
Hessian. All derivatives of the opposite coefficient are retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Bianchi HighestHessian CurvatureContraction MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The same classical first-order calculus for the opposite Weyl block,
using the already specified actual parallel frame flow. -/
structure OppositeWeylData {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
    (d : MetricGreenData g μ) where
  symmetric : ∀ e : FrameBundle g, TraceHessian.symmetric (minusWeyl g e.base e.frame)
  traceFree : ∀ e : FrameBundle g, TraceHessian.traceFree (minusWeyl g e.base e.frame)
  continuousWeyl : Continuous (fun e : FrameBundle g => minusWeyl g e.base e.frame)
  continuousGradient : ∀ i, Continuous
    (fun e : FrameBundle g => minusWeylGradient g e.base e.frame i)
  derivativeWeyl : ∀ i t e, HasDerivAt
    (fun s => minusWeyl g ((d.flow i).map s e).base ((d.flow i).map s e).frame)
    (minusWeylGradient g ((d.flow i).map t e).base ((d.flow i).map t e).frame i) t
  gradientBianchi : ∀ (e : FrameBundle g) s i,
    (∑ r, ∑ k, Angular.oppositeMatrix r i k * minusWeylGradient g e.base e.frame k r s) = 0

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

theorem scalar_flow_green (i : Fin 4)
    (f df h dh : C(FrameBundle g, ℝ))
    (hf : ∀ t e, HasDerivAt (fun r => f ((d.flow i).map r e)) (df ((d.flow i).map t e)) t)
    (hh : ∀ t e, HasDerivAt (fun r => h ((d.flow i).map r e)) (dh ((d.flow i).map t e)) t) :
    (∫ e, df e * h e ∂μ) = -(∫ e, f e * dh e ∂μ) := by
  have hg := Averages.weighted_flow_green μ (d.flow i).map (d.flow i).continuous
    (d.flow i).preserves (ContinuousMap.const _ 1) (ContinuousMap.const _ 0)
    f df h dh (fun t _ => hasDerivAt_const t 1) hf hh
  simpa only [ContinuousMap.coe_const, Function.const_apply, one_mul, zero_mul, add_zero,
    RCLike.inner_apply, conj_trivial, mul_comm] using hg

namespace ScalarCovariantData

variable {a b : M → ℝ} (s : ScalarCovariantData d a)

def valueField : C(FrameBundle g, ℝ) := ⟨fun e => a e.base, s.continuousValue⟩

def gradientField (i : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => scalarGradient g a e i, s.continuousGradient i⟩

def hessianField (i j : Fin 4) : C(FrameBundle g, ℝ) :=
  ⟨fun e => scalarHessian g a e i j, s.continuousHessian i j⟩

include s

theorem scalar_pairing_green (t : ScalarCovariantData d b) :
    (∫ e, ∑ i, scalarGradient g a e i * scalarGradient g b e i ∂μ) =
      -(∫ e, a e.base * scalarLaplacian g b e ∂μ) := by
  have hi (i : Fin 4) := scalar_flow_green (d := d) i s.valueField (s.gradientField i)
    (t.gradientField i) (t.hessianField i i) (s.derivativeValue i) (t.derivativeGradient i i)
  have hl (i : Fin 4) : Integrable
      (fun e => scalarGradient g a e i * scalarGradient g b e i) μ :=
    ((s.continuousGradient i).mul (t.continuousGradient i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hr (i : Fin 4) : Integrable (fun e => a e.base * scalarHessian g b e i i) μ :=
    (s.continuousValue.mul (t.continuousHessian i i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun i _ => hl i)]
  simp only [valueField, gradientField, hessianField, ContinuousMap.coe_mk] at hi
  simp_rw [hi]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hr i)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with e
  exact (Finset.mul_sum _ _ _).symm

end ScalarCovariantData

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth scalar Poisson solvability and covariant differentiation.

Petersen, Riemannian Geometry, third edition author text, §9.1,
Theorem 9.1.2 proof (p.287): the orthogonal image/kernel decomposition
of the Hodge Laplacian. In degree zero on a closed connected manifold,
the kernel is the constants, so every smooth mean-zero function is in
the image. Our Laplacian has the opposite sign, which does not change
its image. The scalar-calculus statement specializes the classical parallel-frame
covariant derivative identities of §3.1.1. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

def PetersenScalarCalculusInput (d : MetricGreenData g μ) : Prop :=
  ∀ a : M → ℝ, ContMDiff I4 𝓘(ℝ, ℝ) ∞ a → Nonempty (ScalarCovariantData d a)

def PetersenPoissonInput (g : SmoothMetric M) (μ : Measure (FrameBundle g)) : Prop :=
  ∀ a : M → ℝ, ContMDiff I4 𝓘(ℝ, ℝ) ∞ a →
    ∃ φ : M → ℝ, ContMDiff I4 𝓘(ℝ, ℝ) ∞ φ ∧
      ∀ e : FrameBundle g, scalarLaplacian g φ e = a e.base - ∫ f, a f.base ∂μ

end
end PositiveEinsteinFour.Geometry

end


section

/-! Reflection of one axis in the actual orthonormal frame. It exchanges
the two Weyl blocks, with one sign for each covariant derivative slot. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian Matrix Bundle
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem plusWeylGradient_reflect (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i : Fin 4) :
    plusWeylGradient g c e.reflect i = orientationSign i • minusWeylGradient g c e i :=
  gradientBlock_frame_reflect e _ i

end
end PositiveEinsteinFour.Geometry
end


section

/-! Lowering the actual curvature derivative and transporting the second
Bianchi identity to the coordinate/frame tensor used by the Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_four_apply (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 4) (z : FourSpace) (i j k l m : Fin 4) :
    covariantDerivative g c T z ![i, j, k, l, m] =
      partialDeriv (fun w => T w ![j, k, l, m]) i z -
      ((∑ p, christoffel g c z p i j * T z ![p, k, l, m]) +
       (∑ p, christoffel g c z p i k * T z ![j, p, l, m]) +
       (∑ p, christoffel g c z p i l * T z ![j, k, p, m]) +
       (∑ p, christoffel g c z p i m * T z ![j, k, l, p])) := by
  have h0 (p : Fin 4) : Function.update ![j, k, l, m] 0 p = ![p, k, l, m] := by
    funext a
    fin_cases a <;> rfl
  have h1 (p : Fin 4) : Function.update ![j, k, l, m] 1 p = ![j, p, l, m] := by
    funext a
    fin_cases a <;> rfl
  have h2 (p : Fin 4) : Function.update ![j, k, l, m] 2 p = ![j, k, p, m] := by
    funext a
    fin_cases a <;> rfl
  have h3 (p : Fin 4) : Function.update ![j, k, l, m] 3 p = ![j, k, l, p] := by
    funext a
    fin_cases a <;> rfl
  change partialDeriv (fun w => T w ![j, k, l, m]) i z -
    (∑ s : Fin 4, ∑ p, christoffel g c z p i (![j, k, l, m] s) *
      T z (Function.update ![j, k, l, m] s p)) = _
  rw [Fin.sum_univ_four]
  simp only [h0, h1, h2, h3]
  rfl

theorem covariantDerivative_curvature_lowering (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k l m : Fin 4) :
    covariantDerivative g c (curvatureCoordinates g c) z ![i, j, k, l, m] =
      (metricInChart g c z * coordinateCovariantCurvatureDerivative g c z i j k) m l := by
  rw [← lowered_derivative_matrix g c z hz hdet i j k]
  rw [covariantDerivative_four_apply]
  have heq (r s t u : Fin 4) :
      (fun w => curvatureCoordinates g c w ![r, s, t, u]) =
      (fun w => (metricInChart g c w * coordinateCurvatureMatrix g c r s w) u t) :=
    funext fun w => (loweredCurvatureMatrix_apply g c w r s t u).symm
  rw [heq]
  simp only [matrixPartial, Matrix.sub_apply, Matrix.sum_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    connectionMatrix, ← loweredCurvatureMatrix_apply, Finset.sum_add_distrib]
  simp only [mul_comm]
  ring

/-- Differential Bianchi for the actual fully covariant curvature tensor. -/
theorem curvatureCoordinates_second_bianchi (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) :
    AlgebraicCurvature.DifferentialBianchi
      (curvatureDerivativeArray (covariantDerivative g c (curvatureCoordinates g c) z)) := by
  intro i j k l m
  change covariantDerivative g c (curvatureCoordinates g c) z ![i, j, k, l, m] +
    covariantDerivative g c (curvatureCoordinates g c) z ![j, k, i, l, m] +
    covariantDerivative g c (curvatureCoordinates g c) z ![k, i, j, l, m] = 0
  simp only [covariantDerivative_curvature_lowering g c z hz hdet]
  have h := congrArg (fun A : Mat4 => (metricInChart g c z * A) m l)
    (coordinate_second_bianchi g c z hz hdet i j k)
  simpa only [mul_add, Matrix.add_apply, mul_zero, Matrix.zero_apply] using h

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

theorem frame_weyl_traceFree_of_lastSkew (e : OrthonormalFrame g c)
    (hl : AlgebraicCurvature.LastSkew (frameCurvature g c e)) (hRic : RicciThree g) :
    TraceHessian.traceFree (plusWeyl g c e) ∧
      TraceHessian.traceFree (minusWeyl g c e) :=
  AlgebraicCurvature.weyl_blocks_traceFree (frameCurvature g c e)
    (frame_algebraic_firstSkew e) hl (frame_algebraic_firstBianchi e)
    (frame_algebraic_ricciThree e hRic)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
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

theorem actual_weyl_traceFree (e : OrthonormalFrame g c) (hRic : RicciThree g) :
    TraceHessian.traceFree (plusWeyl g c e) ∧
      TraceHessian.traceFree (minusWeyl g c e) :=
  frame_weyl_traceFree_of_lastSkew e (frame_algebraic_lastSkew e) hRic

end
end PositiveEinsteinFour.Geometry
end


section

/-! Tracing the actual curvature derivative commutes with covariant
 differentiation.  The connection terms in the contracted input/output
 slots cancel; no Einstein equation is differentiated here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_two_apply (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 2) (z : FourSpace) (i j k : Fin 4) :
    covariantDerivative g c T z ![i, j, k] =
      partialDeriv (fun w => T w ![j, k]) i z -
        ((∑ p, christoffel g c z p i j * T z ![p, k]) +
          ∑ p, christoffel g c z p i k * T z ![j, p]) := by
  have h0 (p : Fin 4) : Function.update ![j, k] 0 p = ![p, k] := by
    funext a
    fin_cases a <;> rfl
  have h1 (p : Fin 4) : Function.update ![j, k] 1 p = ![j, p] := by
    funext a
    fin_cases a <;> rfl
  change partialDeriv (fun w => T w ![j, k]) i z -
    (∑ s : Fin 2, ∑ p, christoffel g c z p i (![j, k] s) *
      T z (Function.update ![j, k] s p)) = _
  rw [Fin.sum_univ_two]
  simp only [h0, h1]
  rfl

/-- The contracted connection terms cancel in the same fixed chart. -/
theorem covariantDerivative_ricci_eq_curvature_trace (g : SmoothMetric M)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k : Fin 4) :
    covariantDerivative g c (ricciTensorCoordinates g c) z ![i, j, k] =
      ∑ r, coordinateCovariantCurvatureDerivative g c z i r j r k := by
  rw [covariantDerivative_two_apply]
  change partialDeriv (fun w => ricciInChart g c w j k) i z -
    ((∑ p, christoffel g c z p i j * ricciInChart g c z p k) +
      ∑ p, christoffel g c z p i k * ricciInChart g c z j p) = _
  rw [partialDeriv_ricciInChart g c z hz hdet]
  simp only [ricciInChart_eq_curvatureMatrix_trace]
  exact (curvature_trace_connection (connectionMatrix g c i z)
    (fun r s => coordinateCurvatureMatrix g c r s z)
    (fun r s => matrixPartial (coordinateCurvatureMatrix g c r s) i z) j k).symm

/-- Lowering and contracting the actual curvature derivative gives the
actual derivative of Ricci.  Invertibility is used only at the evaluation
point; no derivative of the inverse metric is required. -/
theorem lowered_curvature_derivative_contraction (g : SmoothMetric M)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j k : Fin 4) :
    (∑ r, ∑ s, (metricInChart g c z)⁻¹ r s *
      covariantDerivative g c (curvatureCoordinates g c) z ![i, r, j, k, s]) =
      covariantDerivative g c (ricciTensorCoordinates g c) z ![i, j, k] := by
  rw [covariantDerivative_ricci_eq_curvature_trace g c z hz hdet]
  apply Finset.sum_congr rfl
  intro r _
  simp only [covariantDerivative_curvature_lowering g c z hz hdet]
  change ((metricInChart g c z)⁻¹ *
    (metricInChart g c z * coordinateCovariantCurvatureDerivative g c z i r j)) r k = _
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hdet)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constant sectional-curvature tensor is parallel for the actual
metric connection. Thus subtracting it preserves differential Bianchi. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_unitCurvature (g : SmoothMetric M) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) :
    covariantDerivative g c (unitCurvatureCoordinates g c) z = 0 := by
  funext a
  let G := metricInChart g c
  let C := christoffel g c z
  let d := a 0
  let i := a 1
  let j := a 2
  let k := a 3
  let l := a 4
  have hd (r s : Fin 4) : DifferentiableAt ℝ (fun w => G w r s) z :=
    (metricInChart_contDiffAt g c z hz r s).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hpartial (r s : Fin 4) : partialDeriv (fun w => G w r s) d z =
      ∑ p, (G z p s * C p d r + G z r p * C p d s) := by
    rw [← christoffel_metric_compatibility g c z (isUnit_iff_ne_zero.mpr hdet)]
    apply Finset.sum_congr rfl
    intro p _
    change G z s p * C p d r + G z r p * C p d s = _
    rw [show G z s p = G z p s from g.symm _ _ _]
  have ha : a = ![d, i, j, k, l] := by
    funext s
    fin_cases s <;> rfl
  change covariantDerivative g c (unitCurvatureCoordinates g c) z a = 0
  rw [ha, covariantDerivative_four_apply]
  simp only [unitCurvatureCoordinates, Matrix.cons_val_zero]
  change partialDeriv (fun w => G w j k * G w i l - G w i k * G w j l) d z -
    ((∑ p, C p d i * (G z j k * G z p l - G z p k * G z j l)) +
      (∑ p, C p d j * (G z p k * G z i l - G z i k * G z p l)) +
      (∑ p, C p d k * (G z j p * G z i l - G z i p * G z j l)) +
      (∑ p, C p d l * (G z j k * G z i p - G z i k * G z j p))) = 0
  rw [partial_difference (f := fun w => G w j k * G w i l)
      (h := fun w => G w i k * G w j l)
      ((hd j k).mul (hd i l)) ((hd i k).mul (hd j l)) d,
    partial_product (hd j k) (hd i l) d, partial_product (hd i k) (hd j l) d]
  simp only [hpartial, mul_add, mul_sub, add_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro p _
  ring

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

theorem frameJacobiMatrix_apply (e : FrameBundle g) (i j : Fin 3) :
    (1 + frameCurvatureField g e) i j =
      frameCurvature g e.base e.frame i.succ 0 0 j.succ := by
  rw [Matrix.add_apply, Matrix.one_apply, frameCurvatureField_apply]
  ring

theorem frameJacobiMatrix_symmetric (e : FrameBundle g) :
    (1 + frameCurvatureField g e)ᵀ = 1 + frameCurvatureField g e := by
  ext i j
  simp only [Matrix.transpose_apply, frameJacobiMatrix_apply]
  have hp := frame_algebraic_pairSymmetric e.frame (frame_algebraic_lastSkew e.frame)
  rw [← hp j.succ 0 0 i.succ,
    frameCurvature_first_skew e.frame 0 i.succ j.succ 0,
    frameCurvature_last_skew e.frame i.succ 0 j.succ 0, neg_neg]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite frame transport for the differentiated Ricci contraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

/-- All three derivative/Ricci slots transform by the same frame. -/
theorem frame_curvature_derivative_trace (e : OrthonormalFrame g c)
    (a j k : Fin 4) :
    (∑ i, frameTensor e.matrix
      (covariantDerivative g c (curvatureCoordinates g c) (chartAt FourSpace c c))
      ![a, i, j, k, i]) =
      frameTensor e.matrix
        (covariantDerivative g c (ricciTensorCoordinates g c) (chartAt FourSpace c c))
        ![a, j, k] := by
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  have hdet := (chartMetric_posDef g c).det_pos.ne'
  change (∑ i, frameTensor e.matrix
    (covariantDerivative g c (curvatureCoordinates g c) (chartAt FourSpace c c))
    (Fin.cons a ![i, j, k, i])) = _
  simp only [frameTensor_cons (n := 4)]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, frameTensor_trace_inverse, frameTensor_three]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  have h := lowered_curvature_derivative_contraction g c (chartAt FourSpace c c)
    hz hdet t b d
  simp only [← Finset.mul_sum]
  change e.matrix t a * (e.matrix b j * e.matrix d k *
    (∑ r, ∑ s, (chartMetric g c)⁻¹ r s *
      covariantDerivative g c (curvatureCoordinates g c) (chartAt FourSpace c c)
        ![t, r, b, d, s])) = _
  calc
    _ = e.matrix t a * (e.matrix b j * e.matrix d k *
        covariantDerivative g c (ricciTensorCoordinates g c) (chartAt FourSpace c c)
          ![t, b, d]) :=
      congrArg (fun x : ℝ => e.matrix t a * (e.matrix b j * e.matrix d k * x)) h
    _ = _ := by ring

theorem frame_curvature_derivative_trace_zero (e : OrthonormalFrame g c)
    (hRic : covariantDerivative g c (ricciTensorCoordinates g c)
      (chartAt FourSpace c c) = 0) (a j k : Fin 4) :
    (∑ i, frameTensor e.matrix
      (covariantDerivative g c (curvatureCoordinates g c) (chartAt FourSpace c c))
      ![a, i, j, k, i]) = 0 := by
  rw [frame_curvature_derivative_trace, hRic]
  simp [frameTensor]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A chartwise Einstein identity may be differentiated because it holds
on an open set. The center-only `RicciThree` identity is deliberately not
used here; curvature naturality supplies this stronger local identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_const_smul (g : SmoothMetric M) (c : M)
    {n : ℕ} (r : ℝ) (T : FourSpace → CovariantCoordinates n) (z : FourSpace) :
    covariantDerivative g c (fun w => r • T w) z = r • covariantDerivative g c T z := by
  funext a
  have hd : partialDeriv (fun w => r * T w (fun i => a i.succ)) (a 0) z =
      r * partialDeriv (fun w => T w (fun i => a i.succ)) (a 0) z := by
    change fderiv ℝ (r • fun w => T w (fun i => a i.succ)) z (coordinateVector (a 0)) = _
    rw [fderiv_const_smul_field]
    rfl
  simp only [covariantDerivative, Pi.smul_apply, smul_eq_mul, hd, mul_sub,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem ricci_parallel_of_chart_equation (g : SmoothMetric M) (c : M)
    (hRic : ∀ w ∈ (chartAt FourSpace c).target, ∀ i j,
      ricciInChart g c w i j = 3 * metricInChart g c w i j)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    covariantDerivative g c (ricciTensorCoordinates g c) z = 0 := by
  have he : ricciTensorCoordinates g c =ᶠ[𝓝 z]
      (fun w => (3 : ℝ) • metricTensorCoordinates g c w) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    funext a
    exact hRic w hw (a 0) (a 1)
  rw [covariantDerivative_congr g c he, covariantDerivative_const_smul,
    covariantDerivative_metricTensor g c z
      (isUnit_iff_ne_zero.mpr (metricInChart_posDef g c z hz).det_pos.ne'), smul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Subtracting the parallel unit-curvature tensor preserves the actual
differential Bianchi identity. No Einstein or divergence assertion is
needed for this cyclic identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_normalizedWeyl (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) :
    covariantDerivative g c (normalizedWeylCoordinates g c) z =
      covariantDerivative g c (curvatureCoordinates g c) z := by
  unfold normalizedWeylCoordinates
  rw [covariantDerivative_sub]
  · rw [covariantDerivative_unitCurvature g c z hz hdet, sub_zero]
  · intro a
    exact (curvatureCoordinates_contDiffAt g c z hz hdet a).differentiableAt (by first | simp | exact_mod_cast le_top)
  · intro a
    exact (unitCurvatureCoordinates_contDiffAt g c z hz a).differentiableAt (by first | simp | exact_mod_cast le_top)

theorem normalizedWeylCoordinates_second_bianchi (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) :
    AlgebraicCurvature.DifferentialBianchi
      (curvatureDerivativeArray
        (covariantDerivative g c (normalizedWeylCoordinates g c) z)) := by
  rw [covariantDerivative_normalizedWeyl g c z hz hdet]
  exact curvatureCoordinates_second_bianchi g c z hz hdet

theorem frame_normalizedWeyl_second_bianchi (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) :
    AlgebraicCurvature.DifferentialBianchi
      (curvatureDerivativeArray (frameTensor e.matrix
        (covariantDerivative g c (normalizedWeylCoordinates g c)
          (chartAt FourSpace c c)))) := by
  apply frameTensor_differentialBianchi
  apply normalizedWeylCoordinates_second_bianchi
  · exact (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  · exact (chartMetric_posDef g c).det_pos.ne'

end
end PositiveEinsteinFour.Geometry
end


section

/-! The center-wise Einstein hypothesis holds in every fixed metric chart
by Ricci naturality. It can therefore be differentiated on that chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem ricciInChart_transition (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    ricciInChart g c z = (chartTransitionMatrix c d z)ᵀ *
      ((show Mat4 from ricciInChart g d (chartTransition c d z)) * chartTransitionMatrix c d z) := by
  have htrace (q : M) (w : FourSpace) :
      ricciMatrix (fun i j => coordinateCurvatureMatrix g q i j w) =
        (show Mat4 from ricciInChart g q w) := by
    ext i j
    exact (ricciInChart_eq_curvatureMatrix_trace g q w i j).symm
  have h := ricciMatrix_pullback (chartTransitionMatrix c d z)
      (fun i j => coordinateCurvatureMatrix g d i j (chartTransition c d z))
      (fun i j => coordinateCurvatureMatrix g c i j z)
      (isUnit_iff_ne_zero.mpr (chartTransitionMatrix_det_ne_zero g c d z hz hx))
      (coordinateCurvatureMatrix_transition g c d z hz hx)
  rw [htrace c z, htrace d (chartTransition c d z)] at h
  exact h

theorem ricciThree_in_chart (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    ricciInChart g c z = (3 : ℝ) • metricInChart g c z := by
  change (show Mat4 from ricciInChart g c z) = (3 : ℝ) • metricInChart g c z
  let d := (chartAt FourSpace c).symm z
  have hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source :=
    mem_chart_source FourSpace d
  have hd : ricciInChart g d (chartAt FourSpace d d) =
      (3 : ℝ) • metricInChart g d (chartAt FourSpace d d) := by
    ext i j
    exact congrFun (congrFun (hRic d) i) j
  rw [ricciInChart_transition g c d z hz hx]
  change (chartTransitionMatrix c d z)ᵀ *
    ((show Mat4 from ricciInChart g d (chartAt FourSpace d d)) *
      chartTransitionMatrix c d z) = (3 : ℝ) • metricInChart g c z
  rw [hd, smul_mul_assoc, mul_smul_comm]
  change (3 : ℝ) • ((chartTransitionMatrix c d z)ᵀ *
    (metricInChart g d (chartTransition c d z) * chartTransitionMatrix c d z)) = _
  exact congrArg (fun A : Mat4 => (3 : ℝ) • A)
    (metricInChart_transition g c d z hz hx).symm

theorem actual_ricci_parallel (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    covariantDerivative g c (ricciTensorCoordinates g c) z = 0 := by
  apply ricci_parallel_of_chart_equation g c _ z hz
  intro w hw i j
  exact congrFun (congrFun (ricciThree_in_chart g hRic c w hw) i) j

theorem actual_ricci_parallel_at_center (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) :
    covariantDerivative g c (ricciTensorCoordinates g c) (chartAt FourSpace c c) = 0 :=
  actual_ricci_parallel g hRic c _ ((chartAt FourSpace c).map_source
    (mem_chart_source FourSpace c))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariant differentiation preserves the algebraic slot symmetries.
The statements here apply to the actual coordinate curvature and its
actual orthonormal-frame pullback. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_permute {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (σ : Equiv.Perm (Fin n))
    (z : FourSpace) (d : Fin 4) (a : Fin n → Fin 4) :
    covariantDerivative g c (fun w b => T w (b ∘ σ)) z (Fin.cons d a) =
      covariantDerivative g c T z (Fin.cons d (a ∘ σ)) := by
  change partialDeriv (fun w => T w (a ∘ σ)) d z -
    (∑ i, ∑ b, christoffel g c z b d (a i) * T z ((Function.update a i b) ∘ σ)) =
    partialDeriv (fun w => T w (a ∘ σ)) d z -
    (∑ i, ∑ b, christoffel g c z b d (a (σ i)) *
      T z (Function.update (a ∘ σ) i b))
  congr 1
  rw [← Equiv.sum_comp σ (fun i => ∑ b,
    christoffel g c z b d (a i) * T z ((Function.update a i b) ∘ σ))]
  simp only [Function.update_comp_eq_of_injective a σ.injective]

theorem covariantDerivative_neg {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace) :
    covariantDerivative g c (fun w => -T w) z = -covariantDerivative g c T z := by
  have hp (a : Fin n → Fin 4) (d : Fin 4) :
      partialDeriv (fun w => -T w a) d z = -partialDeriv (fun w => T w a) d z := by
    change (fderiv ℝ (-(fun w => T w a)) z) (coordinateVector d) = _
    rw [fderiv_neg]
    rfl
  funext a
  change partialDeriv (fun w => -T w (fun i => a i.succ)) (a 0) z -
    (∑ i, ∑ b, christoffel g c z b (a 0) (a i.succ) *
      (-T z (Function.update (fun i => a i.succ) i b))) = _
  simp only [hp, mul_neg, Finset.sum_neg_distrib]
  simp only [Pi.neg_apply, covariantDerivative]
  ring

theorem covariantDerivative_permute_eq {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (σ : Equiv.Perm (Fin n))
    (z : FourSpace)
    (h : (fun w b => T w (b ∘ σ)) =ᶠ[nhds z] T)
    (d : Fin 4) (a : Fin n → Fin 4) :
    covariantDerivative g c T z (Fin.cons d (a ∘ σ)) =
      covariantDerivative g c T z (Fin.cons d a) := by
  rw [← covariantDerivative_permute]
  exact congrFun (covariantDerivative_congr g c h) (Fin.cons d a)

theorem covariantDerivative_permute_neg {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (σ : Equiv.Perm (Fin n))
    (z : FourSpace)
    (h : (fun w b => T w (b ∘ σ)) =ᶠ[nhds z] fun w => -T w)
    (d : Fin 4) (a : Fin n → Fin 4) :
    covariantDerivative g c T z (Fin.cons d (a ∘ σ)) =
      -covariantDerivative g c T z (Fin.cons d a) := by
  rw [← covariantDerivative_permute]
  have hc := congrFun (covariantDerivative_congr g c h) (Fin.cons d a)
  simpa only [covariantDerivative_neg, Pi.neg_apply] using hc

end
end PositiveEinsteinFour.Geometry
end


section

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem curvatureDerivative_firstSkew (g : SmoothMetric M) (c : M)
    (z : FourSpace) (d : Fin 4) : AlgebraicCurvature.FirstSkew
      (curvatureDerivativeArray (covariantDerivative g c (curvatureCoordinates g c) z) d) := by
  have h : (fun w b => curvatureCoordinates g c w (b ∘ Equiv.swap 0 1)) =ᶠ[nhds z]
      fun w => -curvatureCoordinates g c w := by
    filter_upwards [] with w
    funext a
    exact firstSkew_permute (curvatureCoordinates g c w) (coordinate_curvature_firstSkew g c w) a
  intro i j k l
  have hv : ![i, j, k, l] ∘ Equiv.swap 0 1 = ![j, i, k, l] := by
    funext a
    fin_cases a <;> rfl
  have he := covariantDerivative_permute_neg g c (curvatureCoordinates g c)
    (Equiv.swap 0 1) z h d ![i, j, k, l]
  rw [hv] at he
  exact he

theorem curvatureDerivative_lastSkew (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (d : Fin 4) :
    AlgebraicCurvature.LastSkew
      (curvatureDerivativeArray (covariantDerivative g c (curvatureCoordinates g c) z) d) := by
  have h : (fun w b => curvatureCoordinates g c w (b ∘ Equiv.swap 2 3)) =ᶠ[nhds z]
      fun w => -curvatureCoordinates g c w := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    funext a
    exact lastSkew_permute (curvatureCoordinates g c w) (coordinate_curvature_lastSkew g c w hw
      (metricInChart_posDef g c w hw).det_pos.ne') a
  intro i j k l
  have hv : ![i, j, k, l] ∘ Equiv.swap 2 3 = ![i, j, l, k] := by
    funext a
    fin_cases a <;> rfl
  have he := covariantDerivative_permute_neg g c (curvatureCoordinates g c)
    (Equiv.swap 2 3) z h d ![i, j, k, l]
  rw [hv] at he
  exact he

theorem curvatureDerivative_pairSymmetric (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (d : Fin 4) :
    AlgebraicCurvature.PairSymmetric
      (curvatureDerivativeArray (covariantDerivative g c (curvatureCoordinates g c) z) d) := by
  have h : (fun w b => curvatureCoordinates g c w (b ∘ pairSwap)) =ᶠ[nhds z]
      curvatureCoordinates g c := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    funext a
    exact pairSymmetric_permute (curvatureCoordinates g c w) (coordinate_curvature_pairSymmetric g c w hw
      (metricInChart_posDef g c w hw).det_pos.ne') a
  intro i j k l
  have hv : ![i, j, k, l] ∘ pairSwap = ![k, l, i, j] := by
    funext a
    fin_cases a <;> rfl
  have he := covariantDerivative_permute_eq g c (curvatureCoordinates g c)
    pairSwap z h d ![i, j, k, l]
  rw [hv] at he
  exact he


/-- Every derivative slice of the actual Weyl tensor retains all three
algebraic curvature symmetries in any actual orthonormal frame. -/
theorem frame_normalizedWeyl_derivative_symmetries (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (d : Fin 4) :
    let D := curvatureDerivativeArray (frameTensor e.matrix
      (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))) d
    AlgebraicCurvature.FirstSkew D ∧ AlgebraicCurvature.LastSkew D ∧
      AlgebraicCurvature.PairSymmetric D := by
  dsimp only
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  rw [covariantDerivative_normalizedWeyl g c (chartAt FourSpace c c) hz (chartMetric_posDef g c).det_pos.ne']
  let T := covariantDerivative g c (curvatureCoordinates g c) (chartAt FourSpace c c)
  exact ⟨frameTensor_firstSkew e.matrix T
      (curvatureDerivative_firstSkew g c (chartAt FourSpace c c)) d,
    frameTensor_lastSkew e.matrix T
      (curvatureDerivative_lastSkew g c (chartAt FourSpace c c) hz) d,
    frameTensor_pairSymmetric e.matrix T
      (curvatureDerivative_pairSymmetric g c (chartAt FourSpace c c) hz) d⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual commutation of the coordinate Levi-Civita derivative on the
covariant tensors used for the Weyl Hessian and its first derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_direction {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (i : Fin 4) (a : Fin n → Fin 4) :
    covariantDerivative g c T z (Fin.cons i a) =
      tensorCovariantDirection (connectionMatrix g c) T i z a := rfl

theorem covariantDerivative_iterated_direction {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (i j : Fin 4) (a : Fin n → Fin 4) :
    covariantDerivative g c (covariantDerivative g c T) z (Fin.cons i (Fin.cons j a)) =
      tensorCovariantDirection (connectionMatrix g c)
        (tensorCovariantDirection (connectionMatrix g c) T j) i z a -
          ∑ b, christoffel g c z b i j *
            tensorCovariantDirection (connectionMatrix g c) T b z a := by
  rw [covariantDerivative_direction, tensorCovariantDirection_cons]
  have he (r : Fin 4) :
      (fun w b => covariantDerivative g c T w (Fin.cons r b)) =
        tensorCovariantDirection (connectionMatrix g c) T r := by
    funext w b
    exact covariantDerivative_direction g c T w r b
  rw [he j]
  simp only [covariantDerivative_direction, connectionMatrix]

/-- The actual Ricci commutator. Torsion freedom removes the extra
connection term from the derivative slot. -/
theorem covariantDerivative_commutator {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0)
    (hT : ∀ a, ContDiffAt ℝ ∞ (fun w => T w a) z)
    (i j : Fin 4) (a : Fin n → Fin 4) :
    covariantDerivative g c (covariantDerivative g c T) z (Fin.cons i (Fin.cons j a)) -
      covariantDerivative g c (covariantDerivative g c T) z (Fin.cons j (Fin.cons i a)) =
        -tensorSlotAction (coordinateCurvatureMatrix g c i j z) (T z) a := by
  have hG (r b d : Fin 4) :
      ContDiffAt ℝ ∞ (fun w => connectionMatrix g c r w b d) z :=
    christoffel_contDiffAt g c z hz hdet b r d
  have h := congrFun (tensorCovariantDirection_commutator
    (connectionMatrix g c) T z hG hT i j) a
  rw [covariantDerivative_iterated_direction, covariantDerivative_iterated_direction]
  simp_rw [christoffel_comm g c z _ j i]
  have hC : coordinateCurvatureMatrix g c i j z =
      matrixPartial (connectionMatrix g c j) i z -
        matrixPartial (connectionMatrix g c i) j z +
          (connectionMatrix g c i z * connectionMatrix g c j z -
            connectionMatrix g c j z * connectionMatrix g c i z) := by
    unfold coordinateCurvatureMatrix
    abel
  rw [hC]
  simp only [Pi.sub_apply, Pi.neg_apply] at h
  linarith only [h]


/-- The rank-four instance used by the Weyl Hessian. -/
theorem normalizedWeyl_commutator (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j : Fin 4)
    (a : Fin 4 → Fin 4) :
    covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c)) z
      (Fin.cons i (Fin.cons j a)) -
      covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c)) z
        (Fin.cons j (Fin.cons i a)) =
      -tensorSlotAction (coordinateCurvatureMatrix g c i j z)
        (normalizedWeylCoordinates g c z) a :=
  covariantDerivative_commutator g c (normalizedWeylCoordinates g c) z hz hdet
    (normalizedWeylCoordinates_contDiffAt g c z hz hdet) i j a

/-- The rank-five instance used by the outer commutator of the Weyl gradient. -/
theorem normalizedWeyl_gradient_commutator (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (i j : Fin 4)
    (a : Fin 5 → Fin 4) :
    covariantDerivative g c
      (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))) z
        (Fin.cons i (Fin.cons j a)) -
      covariantDerivative g c
        (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))) z
          (Fin.cons j (Fin.cons i a)) =
      -tensorSlotAction (coordinateCurvatureMatrix g c i j z)
        (covariantDerivative g c (normalizedWeylCoordinates g c) z) a :=
  covariantDerivative_commutator g c
    (covariantDerivative g c (normalizedWeylCoordinates g c)) z hz hdet
    (covariantDerivative_contDiffAt g c z hz hdet (normalizedWeylCoordinates g c)
      (normalizedWeylCoordinates_contDiffAt g c z hz hdet)) i j a

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

theorem covariantDerivative_add {n : ℕ} (g : SmoothMetric M) (c : M)
    (S T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hS : ∀ a, DifferentiableAt ℝ (fun w => S w a) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z) :
    covariantDerivative g c (fun w => S w + T w) z =
      covariantDerivative g c S z + covariantDerivative g c T z := by
  funext a
  have hd : partialDeriv (fun w => S w (fun i => a i.succ) +
        T w (fun i => a i.succ)) (a 0) z =
      partialDeriv (fun w => S w (fun i => a i.succ)) (a 0) z +
        partialDeriv (fun w => T w (fun i => a i.succ)) (a 0) z := by
    exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector (a 0)))
      (fderiv_fun_add (hS _) (hT _))
  simp only [covariantDerivative, Pi.add_apply, hd, mul_add, Finset.sum_add_distrib]
  ring

theorem covariantDerivative_firstBianchi (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 4) (z : FourSpace)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z)
    (hB : ∀ w i j k l, T w ![i, j, k, l] + T w ![j, k, i, l] +
      T w ![k, i, j, l] = 0) (d : Fin 4) :
    AlgebraicCurvature.FirstBianchi
      (curvatureDerivativeArray (covariantDerivative g c T z) d) := by
  let P : FourSpace → CovariantCoordinates 4 := fun w a => T w (a ∘ curvatureCycle)
  let V : FourSpace → CovariantCoordinates 4 :=
    fun w a => T w (a ∘ (curvatureCycle.trans curvatureCycle))
  have hP : ∀ a, DifferentiableAt ℝ (fun w => P w a) z := fun a => hT _
  have hV : ∀ a, DifferentiableAt ℝ (fun w => V w a) z := fun a => hT _
  have hfield : (fun w => T w + P w + V w) = fun _ => 0 := by
    funext w a
    have ha : a = ![a 0, a 1, a 2, a 3] := by
      funext i
      fin_cases i <;> rfl
    have hp : a ∘ curvatureCycle = ![a 1, a 2, a 0, a 3] := by
      funext i
      fin_cases i <;> rfl
    have hv : a ∘ (curvatureCycle.trans curvatureCycle) = ![a 2, a 0, a 1, a 3] := by
      funext i
      fin_cases i <;> rfl
    change T w a + T w (a ∘ curvatureCycle) +
      T w (a ∘ (curvatureCycle.trans curvatureCycle)) = 0
    rw [hp, hv, ha]
    exact hB _ _ _ _ _
  have hd : covariantDerivative g c T z + covariantDerivative g c P z +
      covariantDerivative g c V z = 0 := by
    rw [← covariantDerivative_add g c T P z hT hP,
      ← covariantDerivative_add g c (fun w => T w + P w) V z
        (fun a => (hT a).add (hP a)) hV, hfield]
    funext a
    simp [covariantDerivative, partialDeriv]
  intro i j k l
  have h := congrFun hd (Fin.cons d ![i, j, k, l])
  change covariantDerivative g c T z (Fin.cons d ![i, j, k, l]) +
    covariantDerivative g c P z (Fin.cons d ![i, j, k, l]) +
    covariantDerivative g c V z (Fin.cons d ![i, j, k, l]) = 0 at h
  change covariantDerivative g c T z (Fin.cons d ![i, j, k, l]) +
    covariantDerivative g c (fun w a => T w (a ∘ curvatureCycle)) z
      (Fin.cons d ![i, j, k, l]) +
    covariantDerivative g c (fun w a => T w (a ∘ (curvatureCycle.trans curvatureCycle))) z
      (Fin.cons d ![i, j, k, l]) = 0 at h
  rw [covariantDerivative_permute, covariantDerivative_permute] at h
  have hv1 : ![i, j, k, l] ∘ curvatureCycle = ![j, k, i, l] := by
    funext a
    fin_cases a <;> rfl
  have hv2 : ![i, j, k, l] ∘ (curvatureCycle.trans curvatureCycle) = ![k, i, j, l] := by
    funext a
    fin_cases a <;> rfl
  rw [hv1, hv2] at h
  exact h

theorem curvatureDerivative_firstBianchi (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hdet : (metricInChart g c z).det ≠ 0) (d : Fin 4) :
    AlgebraicCurvature.FirstBianchi
      (curvatureDerivativeArray (covariantDerivative g c (curvatureCoordinates g c) z) d) := by
  apply covariantDerivative_firstBianchi
  · intro a
    exact (curvatureCoordinates_contDiffAt g c z hz hdet a).differentiableAt (by first | simp | exact_mod_cast le_top)
  · intro w i j k l
    exact coordinate_curvature_firstBianchi g c w i j k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! Algebraic curvature symmetries persist through a second covariant
derivative; all derivative slots remain separate from curvature slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem curvatureHessian_firstSkew (g : SmoothMetric M) (c : M)
    (z : FourSpace) (d e : Fin 4) : AlgebraicCurvature.FirstSkew
      (curvatureHessianArray
        (covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c)) z) d e) := by
  let T := covariantDerivative g c (curvatureCoordinates g c)
  have he : (fun w b => T w (b ∘ Equiv.swap 1 2)) =ᶠ[𝓝 z]
      (fun w => -T w) := by
    filter_upwards [] with w
    funext b
    have h1 : b ∘ Equiv.swap 1 2 = ![b 0, b 2, b 1, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have h0 : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h0]
    exact curvatureDerivative_firstSkew g c w (b 0) (b 1) (b 2) (b 3) (b 4)
  intro i j k l
  have hp : ![e, i, j, k, l] ∘ Equiv.swap 1 2 = ![e, j, i, k, l] := by
    funext a
    fin_cases a <;> rfl
  have h := covariantDerivative_permute_neg g c T (Equiv.swap 1 2) z he d ![e, i, j, k, l]
  rw [hp] at h
  exact h

theorem curvatureHessian_lastSkew (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (d e : Fin 4) :
    AlgebraicCurvature.LastSkew (curvatureHessianArray
      (covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c)) z) d e) := by
  let T := covariantDerivative g c (curvatureCoordinates g c)
  have he : (fun w b => T w (b ∘ Equiv.swap 3 4)) =ᶠ[𝓝 z]
      (fun w => -T w) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    funext b
    have h1 : b ∘ Equiv.swap 3 4 = ![b 0, b 1, b 2, b 4, b 3] := by
      funext i
      fin_cases i <;> rfl
    have h0 : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h0]
    exact curvatureDerivative_lastSkew g c w hw (b 0) (b 1) (b 2) (b 3) (b 4)
  intro i j k l
  have hp : ![e, i, j, k, l] ∘ Equiv.swap 3 4 = ![e, i, j, l, k] := by
    funext a
    fin_cases a <;> rfl
  have h := covariantDerivative_permute_neg g c T (Equiv.swap 3 4) z he d ![e, i, j, k, l]
  rw [hp] at h
  exact h

theorem curvatureHessian_pairSymmetric (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (d e : Fin 4) :
    AlgebraicCurvature.PairSymmetric (curvatureHessianArray
      (covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c)) z) d e) := by
  let T := covariantDerivative g c (curvatureCoordinates g c)
  have he : (fun w b => T w (b ∘ hessianPairSwap)) =ᶠ[𝓝 z] T := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    funext b
    have h1 : b ∘ hessianPairSwap = ![b 0, b 3, b 4, b 1, b 2] := by
      funext i
      fin_cases i <;> rfl
    have h0 : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    rw [h1, h0]
    exact curvatureDerivative_pairSymmetric g c w hw (b 0) (b 1) (b 2) (b 3) (b 4)
  intro i j k l
  have hp : ![e, i, j, k, l] ∘ hessianPairSwap = ![e, k, l, i, j] := by
    funext a
    fin_cases a <;> rfl
  have h := covariantDerivative_permute_eq g c T hessianPairSwap z he d ![e, i, j, k, l]
  rw [hp] at h
  exact h

theorem covariantHessian_normalizedWeyl (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c)) z =
      covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c)) z := by
  apply covariantDerivative_congr g c
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
  exact covariantDerivative_normalizedWeyl g c w hw
    (metricInChart_posDef g c w hw).det_pos.ne'

theorem frame_normalizedWeyl_hessian_symmetries (g : SmoothMetric M) (c : M)
    (f : OrthonormalFrame g c) (d e : Fin 4) :
    let H := curvatureHessianArray (frameTensor f.matrix
      (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
        (chartAt FourSpace c c))) d e
    AlgebraicCurvature.FirstSkew H ∧ AlgebraicCurvature.LastSkew H ∧
      AlgebraicCurvature.PairSymmetric H := by
  dsimp only
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  rw [covariantHessian_normalizedWeyl g c (chartAt FourSpace c c) hz]
  let T := covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c))
    (chartAt FourSpace c c)
  exact ⟨frameHessian_firstSkew f.matrix T
      (curvatureHessian_firstSkew g c (chartAt FourSpace c c)) d e,
    frameHessian_lastSkew f.matrix T
      (curvatureHessian_lastSkew g c (chartAt FourSpace c c) hz) d e,
    frameHessian_pairSymmetric f.matrix T
      (curvatureHessian_pairSymmetric g c (chartAt FourSpace c c) hz) d e⟩

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

/-- The Ricci-parallel hypothesis concerns the fixed-chart Ricci field
throughout the chart. -/
theorem plusWeylGradient_bianchi_of_ricci_parallel (e : OrthonormalFrame g c)
    (hRic : covariantDerivative g c (ricciTensorCoordinates g c)
      (chartAt FourSpace c c) = 0) (r : Fin 3) (i : Fin 4) :
    gradientDivergence (plusWeylGradient g c e) r i = 0 := by
  let T := frameTensor e.matrix
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))
  have hs := frame_normalizedWeyl_derivative_symmetries g c e
  have hR (a j k : Fin 4) : (∑ l, T ![a, l, j, k, l]) = 0 := by
    dsimp only [T]
    have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
    rw [covariantDerivative_normalizedWeyl g c (chartAt FourSpace c c) hz (chartMetric_posDef g c).det_pos.ne']
    exact frame_curvature_derivative_trace_zero e hRic a j k
  exact gradientBlock_divergence_of_ricci_parallel T
    (fun a => (hs a).1) (fun a => (hs a).2.1) (fun a => (hs a).2.2)
    (frame_normalizedWeyl_second_bianchi g c e) hR r i

/-- The Ricci-parallel hypothesis concerns the fixed-chart Ricci field
throughout the chart. -/
theorem minusWeylGradient_bianchi_of_ricci_parallel (e : OrthonormalFrame g c)
    (hRic : covariantDerivative g c (ricciTensorCoordinates g c)
      (chartAt FourSpace c c) = 0) (r : Fin 3) (i : Fin 4) :
    (∑ s, ∑ j, Angular.oppositeMatrix s i j * minusWeylGradient g c e j s r) = 0 := by
  let T := frameTensor e.matrix
    (covariantDerivative g c (normalizedWeylCoordinates g c) (chartAt FourSpace c c))
  have hs := frame_normalizedWeyl_derivative_symmetries g c e
  have hR (a j k : Fin 4) : (∑ l, T ![a, l, j, k, l]) = 0 := by
    dsimp only [T]
    have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
    rw [covariantDerivative_normalizedWeyl g c (chartAt FourSpace c c) hz (chartMetric_posDef g c).det_pos.ne']
    exact frame_curvature_derivative_trace_zero e hRic a j k
  exact opposite_gradientBlock_divergence_of_ricci_parallel T
    (fun a => (hs a).1) (fun a => (hs a).2.1) (fun a => (hs a).2.2)
    (frame_normalizedWeyl_second_bianchi g c e) hR r i

end
end PositiveEinsteinFour.Geometry
end


section

/-! Curvature-slot identities of the actual Weyl Hessian, kept separate
from its derivative-slot commutator and trace equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem actual_weylHessian_symmetric (e : OrthonormalFrame g c) (i j : Fin 4) :
    TraceHessian.symmetric (plusWeylHessian g c e i j) ∧
      TraceHessian.symmetric (minusWeylHessian g c e i j) := by
  let T := frameTensor e.matrix
    (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
      (chartAt FourSpace c c))
  have hs := frame_normalizedWeyl_hessian_symmetries g c e i j
  have hp := AlgebraicCurvature.curvaturePairing_symmetric
    (curvatureHessianArray T i j) hs.1 hs.2.1 hs.2.2
  have hsym (Q : Fin 3 → Mat4) : TraceHessian.symmetric (hessianBlock T Q i j) := by
    have hh := curvatureBlock_symmetric hp Q
    intro a b
    exact congrArg (fun A : Mat3 => A b a) hh
  exact ⟨hsym _, hsym _⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Einstein curvature Hessian has zero Ricci contraction.
The first Ricci contraction vanishes on an open chart before differentiating. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantDerivative_five_apply (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 5) (z : FourSpace)
    (d a b j k l : Fin 4) :
    covariantDerivative g c T z ![d, a, b, j, k, l] =
      partialDeriv (fun w => T w ![a, b, j, k, l]) d z -
      ((∑ p, christoffel g c z p d a * T z ![p, b, j, k, l]) +
       (∑ p, christoffel g c z p d b * T z ![a, p, j, k, l]) +
       (∑ p, christoffel g c z p d j * T z ![a, b, p, k, l]) +
       (∑ p, christoffel g c z p d k * T z ![a, b, j, p, l]) +
       (∑ p, christoffel g c z p d l * T z ![a, b, j, k, p])) := by
  have hu (s : Fin 5) (p : Fin 4) :
      Function.update ![a, b, j, k, l] s p =
        ![(if s = 0 then p else a), (if s = 1 then p else b),
          (if s = 2 then p else j), (if s = 3 then p else k),
          (if s = 4 then p else l)] := by
    funext t
    fin_cases s <;> fin_cases t <;> rfl
  change partialDeriv (fun w => T w ![a, b, j, k, l]) d z -
    (∑ s : Fin 5, ∑ p, christoffel g c z p d (![a, b, j, k, l] s) *
      T z (Function.update ![a, b, j, k, l] s p)) = _
  rw [sum_five]
  simp only [hu]
  norm_num only [Fin.reduceEq, ite_true, ite_false]
  change partialDeriv (fun w => T w ![a, b, j, k, l]) d z -
    ((∑ p, christoffel g c z p d a * T z ![p, b, j, k, l]) +
      ((∑ p, christoffel g c z p d b * T z ![a, p, j, k, l]) +
       (∑ p, christoffel g c z p d j * T z ![a, b, p, k, l]) +
       (∑ p, christoffel g c z p d k * T z ![a, b, j, p, l]) +
       (∑ p, christoffel g c z p d l * T z ![a, b, j, k, p]))) = _
  ring

theorem fiveTensorMatrix_covariantDerivative (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 5) (z : FourSpace) (d a j k : Fin 4) :
    (fun p q => covariantDerivative g c T z ![d, a, q, j, k, p]) =
      matrixPartial (fiveTensorMatrix T a j k) d z -
        (connectionMatrix g c d z)ᵀ * fiveTensorMatrix T a j k z -
        fiveTensorMatrix T a j k z * connectionMatrix g c d z -
        (∑ b, christoffel g c z b d a • fiveTensorMatrix T b j k z) -
        (∑ b, christoffel g c z b d j • fiveTensorMatrix T a b k z) -
        (∑ b, christoffel g c z b d k • fiveTensorMatrix T a j b z) := by
  have hright (p q : Fin 4) :
      (fiveTensorMatrix T a j k z * connectionMatrix g c d z) p q =
        ∑ b, christoffel g c z b d q * T z ![a, b, j, k, p] := by
    simp only [Matrix.mul_apply, fiveTensorMatrix, connectionMatrix]
    apply Finset.sum_congr rfl
    intro b _
    ring
  ext p q
  rw [covariantDerivative_five_apply]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, matrixPartial,
    fiveTensorMatrix, connectionMatrix] at hright ⊢
  rw [hright]
  ring

def curvatureDerivativeMatrix (g : SmoothMetric M) (c : M) (a j k : Fin 4) :
    FourSpace → Mat4 :=
  fiveTensorMatrix (covariantDerivative g c (curvatureCoordinates g c)) a j k

theorem curvatureDerivativeMatrix_trace_zero (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (a j k : Fin 4) :
    ((metricInChart g c z)⁻¹ * curvatureDerivativeMatrix g c a j k z).trace = 0 := by
  change (∑ r, ∑ s, (metricInChart g c z)⁻¹ r s *
    covariantDerivative g c (curvatureCoordinates g c) z ![a, r, j, k, s]) = 0
  rw [lowered_curvature_derivative_contraction g c z hz
    (metricInChart_posDef g c z hz).det_pos.ne', actual_ricci_parallel g hRic c z hz]
  rfl

theorem curvatureHessian_contraction_zero (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (d a j k : Fin 4) :
    (∑ r, ∑ s, (metricInChart g c z)⁻¹ r s *
      covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c)) z
        ![d, a, r, j, k, s]) = 0 := by
  let T := covariantDerivative g c (curvatureCoordinates g c)
  let S := curvatureDerivativeMatrix g c
  have hzero (b l m : Fin 4) :
      ((metricInChart g c z)⁻¹ * S b l m z).trace = 0 :=
    curvatureDerivativeMatrix_trace_zero g hRic c z hz b l m
  have he : (fun w => ((metricInChart g c w)⁻¹ * S a j k w).trace) =ᶠ[𝓝 z]
      (fun _ => 0) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    exact curvatureDerivativeMatrix_trace_zero g hRic c w hw a j k
  have hd : partialDeriv (fun w => ((metricInChart g c w)⁻¹ * S a j k w).trace) d z = 0 := by
    simp only [partialDeriv, he.fderiv_eq, fderiv_const_apply, _root_.zero_apply]
  have hdet := (metricInChart_posDef g c z hz).det_pos.ne'
  have hS (p q : Fin 4) : DifferentiableAt ℝ (fun w => S a j k w p q) z :=
    (covariantDerivative_contDiffAt g c z hz hdet (curvatureCoordinates g c)
      (curvatureCoordinates_contDiffAt g c z hz hdet) ![a, q, j, k, p]).differentiableAt
        (by first | simp | exact_mod_cast le_top)
  rw [partialDeriv_metric_contraction g c (S a j k) z hz hS d] at hd
  change ((metricInChart g c z)⁻¹ *
    (show Mat4 from fun p q => covariantDerivative g c T z ![d, a, q, j, k, p])).trace = 0
  rw [fiveTensorMatrix_covariantDerivative g c T z d a j k]
  change ((metricInChart g c z)⁻¹ *
    (matrixPartial (S a j k) d z - (connectionMatrix g c d z)ᵀ * S a j k z -
      S a j k z * connectionMatrix g c d z -
      (∑ b, christoffel g c z b d a • S b j k z) -
      (∑ b, christoffel g c z b d j • S a b k z) -
      (∑ b, christoffel g c z b d k • S a j b z))).trace = 0
  simp only [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, hzero, smul_zero, Finset.sum_const_zero, sub_zero]
  simpa only [Matrix.mul_sub, Matrix.trace_sub] using hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! The raw orthogonal-frame invariance used from Brin--Karcher, §1:
the uniform frame measure is invariant under a fixed reflection, and
parallel transport intertwines reflection with reversal of the first
flow direction. This gives integral and tensor identities for reflected frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

/-- The two elementary reflection compatibilities of uniform parallel
frame flow. These are classical input, not a curvature estimate. -/
structure FrameReflectionData (d : MetricGreenData g μ) where
  preserves : MeasurePreserving (frameReflection : FrameBundle g → FrameBundle g) μ μ
  parallel : ∀ i t e, frameReflection ((d.flow i).map t e) =
    (d.flow i).map (orientationSign i * t) (frameReflection e)

namespace FrameReflectionData

variable {d : MetricGreenData g μ} (r : FrameReflectionData d)

def reflectTest (_r : FrameReflectionData d) (k : C(FrameBundle g, ℝ)) : C(FrameBundle g, ℝ) :=
  k.comp ⟨frameReflection, continuous_frameReflection g⟩

def reflectTestDerivative (_r : FrameReflectionData d)
    (dk : Fin 4 → C(FrameBundle g, ℝ)) (i : Fin 4) :
    C(FrameBundle g, ℝ) :=
  ⟨fun e => orientationSign i * dk i (frameReflection e),
    continuous_const.mul ((dk i).continuous.comp (continuous_frameReflection g))⟩

end FrameReflectionData

end
end PositiveEinsteinFour.Geometry
end


section

/-! The quaternion basis converts the actual four covector actions into
the matrix commutator used by the Weyl block equations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators

noncomputable section

/-- The negative of the actual covector action is the spin-two matrix action. -/
theorem blockCoordinates_quaternion_action (T : CovariantCoordinates 4) (s : Fin 3) :
    blockCoordinates (tensorSlotAction (quaternionMatrix s) T) quaternionMatrix =
      -matrixAction s (blockCoordinates T quaternionMatrix) := by
  ext a b
  rw [blockCoordinates_pairing,
    twoFormPairing_skew_slotAction (quaternionMatrix s) (Angular.quaternionMatrix_transpose s),
    quaternion_generator_commutator s a, quaternion_generator_commutator s b]
  simp only [Fin.sum_univ_three, twoFormPairing_add_left, twoFormPairing_add_right,
    twoFormPairing_smul_left, twoFormPairing_smul_right, Matrix.neg_apply,
    matrixAction]
  simp only [← blockCoordinates_pairing]
  rw [rotation_skew s 0 a, rotation_skew s 1 a, rotation_skew s 2 a]
  ring

/-- The commuting quaternion triple has no action on the positive Weyl block. -/
theorem blockCoordinates_opposite_action (T : CovariantCoordinates 4) (s : Fin 3) :
    blockCoordinates (tensorSlotAction (Angular.oppositeMatrix s) T) quaternionMatrix = 0 := by
  ext a b
  rw [blockCoordinates_pairing,
    twoFormPairing_skew_slotAction (Angular.oppositeMatrix s)
      (QuaternionFrame.oppositeMatrix_transpose s),
    Angular.oppositeMatrix_commute s a, Angular.oppositeMatrix_commute s b,
    sub_self, sub_self, twoFormPairing_zero_left, twoFormPairing_zero_right, add_zero]
  rfl

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

theorem actual_plusWeylGradient_bianchi (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (r : Fin 3) (i : Fin 4) :
    gradientDivergence (plusWeylGradient g c e) r i = 0 :=
  plusWeylGradient_bianchi_of_ricci_parallel e (actual_ricci_parallel_at_center g hRic c) r i

theorem actual_minusWeylGradient_bianchi (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (r : Fin 3) (i : Fin 4) :
    (∑ s, ∑ j, Angular.oppositeMatrix s i j * minusWeylGradient g c e j s r) = 0 :=
  minusWeylGradient_bianchi_of_ricci_parallel e (actual_ricci_parallel_at_center g hRic c) r i

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature endomorphism acts on the quaternionic Weyl block.
This is a finite contraction of the full tensor, before any diagonalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators

noncomputable section

theorem blockCoordinates_blockTensor_plus_action (A : Mat3)
    (T : CovariantCoordinates 4) (i j : Fin 4) :
    blockCoordinates (tensorSlotAction
      (curvatureEndomorphism (Angular.blockTensor A quaternionMatrix) i j) T)
      quaternionMatrix =
      -(1 / 2 : ℝ) • ∑ r, ∑ s,
        (A r s * quaternionMatrix r i j) • matrixAction s (blockCoordinates T quaternionMatrix) := by
  rw [curvatureEndomorphism_blockTensor]
  simp only [tensorSlotAction_smul_matrix, tensorSlotAction_sum_matrix]
  change blockCoordinatesLinear quaternionMatrix _ = _
  simp only [map_smul, map_sum]
  change (1 / 2 : ℝ) • (∑ r, ∑ s, (A r s * quaternionMatrix r i j) •
    blockCoordinates (tensorSlotAction (quaternionMatrix s) T) quaternionMatrix) = _
  simp_rw [blockCoordinates_quaternion_action]
  simp only [smul_neg, Finset.sum_neg_distrib, neg_smul]

theorem blockCoordinates_blockTensor_opposite_action (A : Mat3)
    (T : CovariantCoordinates 4) (i j : Fin 4) :
    blockCoordinates (tensorSlotAction
      (curvatureEndomorphism (Angular.blockTensor A Angular.oppositeMatrix) i j) T)
      quaternionMatrix = 0 := by
  rw [curvatureEndomorphism_blockTensor]
  simp only [tensorSlotAction_smul_matrix, tensorSlotAction_sum_matrix]
  change blockCoordinatesLinear quaternionMatrix _ = _
  simp only [map_smul, map_sum]
  change (1 / 2 : ℝ) • (∑ r, ∑ s, (A r s * Angular.oppositeMatrix r i j) •
    blockCoordinates (tensorSlotAction (Angular.oppositeMatrix s) T) quaternionMatrix) = _
  simp only [blockCoordinates_opposite_action, smul_zero, Finset.sum_const_zero]

theorem blockCoordinates_einstein_curvature_action (A U : Mat3)
    (T : CovariantCoordinates 4) (i j : Fin 4) :
    blockCoordinates (-tensorSlotAction
      (curvatureEndomorphism (Angular.einsteinCurvatureTensor A U) i j) T)
      quaternionMatrix = bundleCurvatureAction A i j (blockCoordinates T quaternionMatrix) := by
  have hc : curvatureEndomorphism (Angular.einsteinCurvatureTensor A U) i j =
      curvatureEndomorphism (Angular.blockTensor (1 + A) quaternionMatrix) i j +
        curvatureEndomorphism (Angular.blockTensor (1 + U) Angular.oppositeMatrix) i j := rfl
  rw [hc, tensorSlotAction_add_matrix]
  change blockCoordinatesLinear quaternionMatrix (-(_ + _)) = _
  rw [map_neg, map_add]
  change -(blockCoordinates (tensorSlotAction
    (curvatureEndomorphism (Angular.blockTensor (1 + A) quaternionMatrix) i j) T)
      quaternionMatrix + blockCoordinates (tensorSlotAction
    (curvatureEndomorphism (Angular.blockTensor (1 + U) Angular.oppositeMatrix) i j) T)
      quaternionMatrix) = _
  rw [blockCoordinates_blockTensor_plus_action, blockCoordinates_blockTensor_opposite_action,
    add_zero, neg_smul, neg_neg]
  ext a b
  simp only [bundleCurvatureAction, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, Matrix.add_apply, Matrix.one_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  simp only [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transport the zero Ricci contraction of the actual curvature Hessian
to any orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frame_curvature_hessian_trace_zero (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (d a j k : Fin 4) :
    (∑ r, frameTensor e.matrix
      (covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c))
        (chartAt FourSpace c c)) ![d, a, r, j, k, r]) = 0 := by
  let H := covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c))
    (chartAt FourSpace c c)
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  have htrace (u v b f : Fin 4) :
      (∑ r, ∑ s, (chartMetric g c)⁻¹ r s * H ![u, v, r, b, f, s]) = 0 :=
    curvatureHessian_contraction_zero g hRic c (chartAt FourSpace c c) hz u v b f
  have hslice (u v : Fin 4) :
      (∑ r, frameTensor e.matrix (fun b => H (Fin.cons u (Fin.cons v b)))
        ![r, j, k, r]) = 0 := by
    rw [frameTensor_trace_inverse]
    have ht (b f : Fin 4) :
        (∑ r, ∑ s, (chartMetric g c)⁻¹ r s *
          H (Fin.cons u (Fin.cons v ![r, b, f, s]))) = 0 := htrace u v b f
    simp only [ht, mul_zero, Finset.sum_const_zero]
  change (∑ r, frameTensor e.matrix H (Fin.cons d (Fin.cons a ![r, j, k, r]))) = 0
  simp only [frameTensor_cons (n := 5), frameTensor_cons (n := 4), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro u _
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hslice, mul_zero, Finset.sum_const_zero]

theorem frame_normalizedWeyl_hessian_trace_zero (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (d a j k : Fin 4) :
    (∑ r, frameTensor e.matrix
      (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
        (chartAt FourSpace c c)) ![d, a, r, j, k, r]) = 0 := by
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  rw [covariantHessian_normalizedWeyl g c (chartAt FourSpace c c) hz]
  exact frame_curvature_hessian_trace_zero e hRic d a j k

end
end PositiveEinsteinFour.Geometry
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

/-- The only reflection input on the oriented measure is the ordinary
parallel-transport relation, valid independently of the measure. -/
def ParallelReflection (d : MetricGreenData g μ) : Prop :=
  ∀ i t e, frameReflection ((d.flow i).map t e) =
    (d.flow i).map (orientationSign i * t) (frameReflection e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Algebraic first Bianchi survives a second covariant derivative.
Only an identity on the open chart is differentiated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantHessian_firstBianchi (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 5) (z : FourSpace)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z)
    (hB : ∀ᶠ w in 𝓝 z, ∀ a i j k l,
      T w ![a, i, j, k, l] + T w ![a, j, k, i, l] + T w ![a, k, i, j, l] = 0)
    (d a : Fin 4) :
    AlgebraicCurvature.FirstBianchi
      (curvatureHessianArray (covariantDerivative g c T z) d a) := by
  let P : FourSpace → CovariantCoordinates 5 := fun w b => T w (b ∘ secondCurvatureCycle)
  let V : FourSpace → CovariantCoordinates 5 :=
    fun w b => T w (b ∘ (secondCurvatureCycle.trans secondCurvatureCycle))
  have hP : ∀ b, DifferentiableAt ℝ (fun w => P w b) z := fun b => hT _
  have hV : ∀ b, DifferentiableAt ℝ (fun w => V w b) z := fun b => hT _
  have hfield : (fun w => T w + P w + V w) =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [hB] with w hw
    funext b
    have hb : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have hp : b ∘ secondCurvatureCycle = ![b 0, b 2, b 3, b 1, b 4] := by
      funext i
      fin_cases i <;> rfl
    have hv : b ∘ (secondCurvatureCycle.trans secondCurvatureCycle) =
        ![b 0, b 3, b 1, b 2, b 4] := by
      funext i
      fin_cases i <;> rfl
    change T w b + T w (b ∘ secondCurvatureCycle) +
      T w (b ∘ (secondCurvatureCycle.trans secondCurvatureCycle)) = 0
    rw [hp, hv, hb]
    exact hw _ _ _ _ _
  have hd : covariantDerivative g c T z + covariantDerivative g c P z +
      covariantDerivative g c V z = 0 := by
    rw [← covariantDerivative_add g c T P z hT hP,
      ← covariantDerivative_add g c (fun w => T w + P w) V z
        (fun b => (hT b).add (hP b)) hV,
      covariantDerivative_congr g c hfield]
    funext b
    simp [covariantDerivative, partialDeriv]
  intro i j k l
  have h := congrFun hd (Fin.cons d ![a, i, j, k, l])
  change covariantDerivative g c T z (Fin.cons d ![a, i, j, k, l]) +
    covariantDerivative g c (fun w b => T w (b ∘ secondCurvatureCycle)) z
      (Fin.cons d ![a, i, j, k, l]) +
    covariantDerivative g c
      (fun w b => T w (b ∘ (secondCurvatureCycle.trans secondCurvatureCycle))) z
      (Fin.cons d ![a, i, j, k, l]) = 0 at h
  rw [covariantDerivative_permute, covariantDerivative_permute] at h
  have hp : ![a, i, j, k, l] ∘ secondCurvatureCycle = ![a, j, k, i, l] := by
    funext b
    fin_cases b <;> rfl
  have hv : ![a, i, j, k, l] ∘ (secondCurvatureCycle.trans secondCurvatureCycle) =
      ![a, k, i, j, l] := by
    funext b
    fin_cases b <;> rfl
  rw [hp, hv] at h
  exact h

theorem curvatureHessian_firstBianchi (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (d a : Fin 4) :
    AlgebraicCurvature.FirstBianchi (curvatureHessianArray
      (covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c)) z) d a) := by
  have hdet := (metricInChart_posDef g c z hz).det_pos.ne'
  apply covariantHessian_firstBianchi
  · intro b
    exact (covariantDerivative_contDiffAt g c z hz hdet (curvatureCoordinates g c)
      (curvatureCoordinates_contDiffAt g c z hz hdet) b).differentiableAt (by first | simp | exact_mod_cast le_top)
  · filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    intro a i j k l
    exact curvatureDerivative_firstBianchi g c w hw
      (metricInChart_posDef g c w hw).det_pos.ne' a i j k l

theorem frame_normalizedWeyl_hessian_firstBianchi (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (d a : Fin 4) :
    AlgebraicCurvature.FirstBianchi (curvatureHessianArray (frameTensor e.matrix
      (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
        (chartAt FourSpace c c))) d a) := by
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  rw [covariantHessian_normalizedWeyl g c (chartAt FourSpace c c) hz]
  exact frameHessian_firstBianchi e.matrix
    (covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c))
      (chartAt FourSpace c c)) (curvatureHessian_firstBianchi g c (chartAt FourSpace c c) hz) d a

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two actual Weyl Hessian blocks are trace-free because the
Einstein curvature Hessian has zero Ricci contraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem actual_weylHessian_traceFree (e : OrthonormalFrame g c) (hRic : RicciThree g)
    (i j : Fin 4) :
    TraceHessian.traceFree (plusWeylHessian g c e i j) ∧
      TraceHessian.traceFree (minusWeylHessian g c e i j) := by
  let T := frameTensor e.matrix
    (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
      (chartAt FourSpace c c))
  have hs := frame_normalizedWeyl_hessian_symmetries g c e i j
  have hb := frame_normalizedWeyl_hessian_firstBianchi g c e i j
  have hR (k : Fin 4) : (∑ r, T ![i, j, r, k, k, r]) = 0 :=
    frame_normalizedWeyl_hessian_trace_zero e hRic i j k k
  exact AlgebraicCurvature.ricci_zero_blocks_traceFree
    (curvatureHessianArray T i j) hs.1 hs.2.1 hb hR

theorem actual_weylHessian_constraints (e : OrthonormalFrame g c) (hRic : RicciThree g)
    (i j : Fin 4) :
    (TraceHessian.symmetric (plusWeylHessian g c e i j) ∧
      TraceHessian.traceFree (plusWeylHessian g c e i j)) ∧
    (TraceHessian.symmetric (minusWeylHessian g c e i j) ∧
      TraceHessian.traceFree (minusWeylHessian g c e i j)) :=
  ⟨⟨(actual_weylHessian_symmetric e i j).1, (actual_weylHessian_traceFree e hRic i j).1⟩,
   ⟨(actual_weylHessian_symmetric e i j).2, (actual_weylHessian_traceFree e hRic i j).2⟩⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rank-four curvature commutator on the positive Weyl block. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem blockCoordinates_unitFrameTensor :
    blockCoordinates unitFrameTensor quaternionMatrix = 1 := by
  ext a b
  rw [blockCoordinates_pairing,
    unitFrameTensor_pairing _ _ (Angular.quaternionMatrix_transpose b),
    CurvatureContraction.plus_twoForm_pairing]
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num

theorem frameWeyl_blockCoordinates (e : OrthonormalFrame g c) :
    blockCoordinates (frameTensor e.matrix
      (normalizedWeylCoordinates g c (chartAt FourSpace c c))) quaternionMatrix =
        plusWeyl g c e := by
  have hT : frameTensor e.matrix (normalizedWeylCoordinates g c (chartAt FourSpace c c)) =
      frameTensor e.matrix (curvatureCoordinates g c (chartAt FourSpace c c)) - unitFrameTensor := by
    funext a
    change frameTensor e.matrix (_ - _) a = _
    rw [frameTensor_sub, frameTensor_unitCurvature]
    rfl
  rw [hT]
  change blockCoordinatesLinear quaternionMatrix (_ - _) = _
  rw [map_sub]
  change blockCoordinates (frameTensor e.matrix
    (curvatureCoordinates g c (chartAt FourSpace c c))) quaternionMatrix -
      blockCoordinates unitFrameTensor quaternionMatrix = _
  rw [blockCoordinates_unitFrameTensor]
  change blockCoordinates (frameTensor e.matrix
    (curvatureCoordinates g c (chartAt FourSpace c c))) quaternionMatrix - 1 =
      curvatureBlock (curvaturePairing g c e) quaternionMatrix - 1
  congr 1
  ext a b
  simp only [blockCoordinates, curvatureBlock, frameTensor_curvatureCoordinates,
    curvaturePairing]

/-- The last pointwise commutator input of the Weyl equation is a consequence
of the actual Levi-Civita commutator and Einstein curvature decomposition. -/
theorem actual_plusWeylHessian_commutator (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (i j : Fin 4) (a b : Fin 3) :
    plusWeylHessian g c e i j a b - plusWeylHessian g c e j i a b =
      bundleCurvatureAction (plusWeyl g c e) i j (plusWeyl g c e) a b := by
  let z : FourSpace := chartAt FourSpace c c
  let T : CovariantCoordinates 4 := normalizedWeylCoordinates g c z
  let X : CovariantCoordinates 6 := covariantDerivative g c
    (covariantDerivative g c (normalizedWeylCoordinates g c)) z
  let C : Fin 4 → Fin 4 → Mat4 := fun p q => coordinateCurvatureMatrix g c p q z
  have hz : z ∈ (chartAt FourSpace c).target := (chartAt FourSpace c).map_source
    (mem_chart_source FourSpace c)
  have hdet : (metricInChart g c z).det ≠ 0 :=
    (metricInChart_posDef g c z hz).det_pos.ne'
  have hX (p q : Fin 4) (v : Fin 4 → Fin 4) :
      X (Fin.cons p (Fin.cons q v)) - X (Fin.cons q (Fin.cons p v)) =
        -tensorSlotAction (C p q) T v :=
    normalizedWeyl_commutator g c z hz hdet p q v
  have hc : e.matrix⁻¹ * pulledCurvatureEndomorphism e.matrix C i j * e.matrix =
      curvatureEndomorphism (Angular.einsteinCurvatureTensor
        (plusWeyl g c e) (minusWeyl g c e)) i j := by
    rw [frame_curvatureEndomorphism, actual_einstein_decomposition e hRic]
  have he : (fun v => frameTensor e.matrix X (Fin.cons i (Fin.cons j v))) -
      (fun v => frameTensor e.matrix X (Fin.cons j (Fin.cons i v))) =
        -tensorSlotAction (curvatureEndomorphism (Angular.einsteinCurvatureTensor
          (plusWeyl g c e) (minusWeyl g c e)) i j) (frameTensor e.matrix T) := by
    funext v
    have hh := framed_tensor_commutator e.matrix (isUnit_iff_ne_zero.mpr e.det_ne_zero)
      C T X hX i j v
    rw [hc] at hh
    exact hh
  have hb := congrArg (blockCoordinatesLinear quaternionMatrix) he
  rw [map_sub] at hb
  change blockCoordinates (fun v => frameTensor e.matrix X (Fin.cons i (Fin.cons j v)))
      quaternionMatrix -
    blockCoordinates (fun v => frameTensor e.matrix X (Fin.cons j (Fin.cons i v)))
      quaternionMatrix =
    blockCoordinates (-tensorSlotAction (curvatureEndomorphism
      (Angular.einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e)) i j)
      (frameTensor e.matrix T)) quaternionMatrix at hb
  rw [blockCoordinates_einstein_curvature_action, frameWeyl_blockCoordinates] at hb
  exact congrArg (fun B : Mat3 => B a b) hb

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiating the actual cyclic second Bianchi identity preserves
its derivative and curvature slots, before passage to an orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem covariantHessian_differentialBianchi (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 5) (z : FourSpace)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) z)
    (hB : ∀ᶠ w in 𝓝 z, ∀ a i j k l,
      T w ![a, i, j, k, l] + T w ![i, j, a, k, l] + T w ![j, a, i, k, l] = 0)
    (d : Fin 4) :
    AlgebraicCurvature.DifferentialBianchi
      (curvatureDerivativeArray (fun b => covariantDerivative g c T z (Fin.cons d b))) := by
  let P : FourSpace → CovariantCoordinates 5 := fun w b => T w (b ∘ differentiatedBianchiCycle)
  let V : FourSpace → CovariantCoordinates 5 :=
    fun w b => T w (b ∘ (differentiatedBianchiCycle.trans differentiatedBianchiCycle))
  have hP : ∀ b, DifferentiableAt ℝ (fun w => P w b) z := fun b => hT _
  have hV : ∀ b, DifferentiableAt ℝ (fun w => V w b) z := fun b => hT _
  have hfield : (fun w => T w + P w + V w) =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [hB] with w hw
    funext b
    have hb : b = ![b 0, b 1, b 2, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have hp : b ∘ differentiatedBianchiCycle = ![b 1, b 2, b 0, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    have hv : b ∘ (differentiatedBianchiCycle.trans differentiatedBianchiCycle) =
        ![b 2, b 0, b 1, b 3, b 4] := by
      funext i
      fin_cases i <;> rfl
    change T w b + T w (b ∘ differentiatedBianchiCycle) +
      T w (b ∘ (differentiatedBianchiCycle.trans differentiatedBianchiCycle)) = 0
    rw [hp, hv, hb]
    exact hw _ _ _ _ _
  have hd : covariantDerivative g c T z + covariantDerivative g c P z +
      covariantDerivative g c V z = 0 := by
    rw [← covariantDerivative_add g c T P z hT hP,
      ← covariantDerivative_add g c (fun w => T w + P w) V z
        (fun b => (hT b).add (hP b)) hV,
      covariantDerivative_congr g c hfield]
    funext b
    simp [covariantDerivative, partialDeriv]
  intro a i j k l
  have h := congrFun hd (Fin.cons d ![a, i, j, k, l])
  change covariantDerivative g c T z (Fin.cons d ![a, i, j, k, l]) +
    covariantDerivative g c (fun w b => T w (b ∘ differentiatedBianchiCycle)) z
      (Fin.cons d ![a, i, j, k, l]) +
    covariantDerivative g c
      (fun w b => T w (b ∘ (differentiatedBianchiCycle.trans differentiatedBianchiCycle))) z
      (Fin.cons d ![a, i, j, k, l]) = 0 at h
  rw [covariantDerivative_permute, covariantDerivative_permute] at h
  have hp : ![a, i, j, k, l] ∘ differentiatedBianchiCycle = ![i, j, a, k, l] := by
    funext b
    fin_cases b <;> rfl
  have hv : ![a, i, j, k, l] ∘ (differentiatedBianchiCycle.trans differentiatedBianchiCycle) =
      ![j, a, i, k, l] := by
    funext b
    fin_cases b <;> rfl
  rw [hp, hv] at h
  exact h


theorem curvatureHessian_differentialBianchi (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (d : Fin 4) :
    AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray
      (fun b => covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c))
        z (Fin.cons d b))) := by
  have hdet := (metricInChart_posDef g c z hz).det_pos.ne'
  apply covariantHessian_differentialBianchi
  · intro b
    exact (covariantDerivative_contDiffAt g c z hz hdet (curvatureCoordinates g c)
      (curvatureCoordinates_contDiffAt g c z hz hdet) b).differentiableAt (by first | simp | exact_mod_cast le_top)
  · filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    exact curvatureCoordinates_second_bianchi g c w hw
      (metricInChart_posDef g c w hw).det_pos.ne'

theorem frame_normalizedWeyl_hessian_differentialBianchi (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (d : Fin 4) :
    AlgebraicCurvature.DifferentialBianchi (curvatureDerivativeArray
      (fun b => frameTensor e.matrix
        (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
          (chartAt FourSpace c c)) (Fin.cons d b))) := by
  have hz := (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  rw [covariantHessian_normalizedWeyl g c (chartAt FourSpace c c) hz]
  exact frameHessian_differentialBianchi e.matrix
    (covariantDerivative g c (covariantDerivative g c (curvatureCoordinates g c))
      (chartAt FourSpace c c))
    (curvatureHessian_differentialBianchi g c (chartAt FourSpace c c) hz) d

end
end PositiveEinsteinFour.Geometry
end


section

/-! The differentiated Bianchi constraint for the actual Weyl Hessian
follows from the tensor identity and its zero Ricci contraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem actual_plusWeylHessian_bianchi_components (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (d : Fin 4) (r : Fin 3) (i : Fin 4) :
    gradientDivergence (plusWeylHessian g c e d) r i = 0 := by
  let H := frameTensor e.matrix
    (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))
      (chartAt FourSpace c c))
  let T : CovariantCoordinates 5 := fun b => H (Fin.cons d b)
  have hs := frame_normalizedWeyl_hessian_symmetries g c e d
  have hR (a j k : Fin 4) : (∑ l, T ![a, l, j, k, l]) = 0 :=
    frame_normalizedWeyl_hessian_trace_zero e hRic d a j k
  exact gradientBlock_divergence_of_ricci_parallel T
    (fun a => (hs a).1) (fun a => (hs a).2.1) (fun a => (hs a).2.2)
    (frame_normalizedWeyl_hessian_differentialBianchi g c e d) hR r i

theorem actual_plusWeylHessian_bianchi (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (d : Fin 4) (r : Fin 3) :
    HighestHessian.divergence (plusWeylHessian g c e) d r = 0 := by
  ext i
  have h := actual_plusWeylHessian_bianchi_components e hRic d r i
  change (∑ s, Bianchi.quaternion s
    (WithLp.toLp 2 (fun j => plusWeylHessian g c e d j s r))) i = 0
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [← TraceHessian.quaternionMatrix_apply]
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rank-five commutator includes the curvature action on the
leading covector slot of the Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

/-- The outer Ricci commutation formula is derived from the actual
Levi-Civita action on all five slots, including the gradient covector. -/
theorem actual_plusWeylThird_outerCommutator (e : OrthonormalFrame g c)
    (hRic : RicciThree g) (i k j : Fin 4) :
    plusWeylThirdDerivative g c e i k j - plusWeylThirdDerivative g c e k i j =
      bundleCurvatureAction (plusWeyl g c e) i k (plusWeylGradient g c e j) +
        ∑ a, frameCurvature g c e i k a j • plusWeylGradient g c e a := by
  let z : FourSpace := chartAt FourSpace c c
  let T : CovariantCoordinates 5 := covariantDerivative g c (normalizedWeylCoordinates g c) z
  let X : CovariantCoordinates 7 := covariantDerivative g c
    (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c))) z
  let C : Fin 4 → Fin 4 → Mat4 := fun p q => coordinateCurvatureMatrix g c p q z
  have hz : z ∈ (chartAt FourSpace c).target := (chartAt FourSpace c).map_source
    (mem_chart_source FourSpace c)
  have hdet : (metricInChart g c z).det ≠ 0 :=
    (metricInChart_posDef g c z hz).det_pos.ne'
  have hX (p q : Fin 4) (v : Fin 5 → Fin 4) :
      X (Fin.cons p (Fin.cons q v)) - X (Fin.cons q (Fin.cons p v)) =
        -tensorSlotAction (C p q) T v :=
    normalizedWeyl_gradient_commutator g c z hz hdet p q v
  have hc : e.matrix⁻¹ * pulledCurvatureEndomorphism e.matrix C i k * e.matrix =
      curvatureEndomorphism (Angular.einsteinCurvatureTensor
        (plusWeyl g c e) (minusWeyl g c e)) i k := by
    rw [frame_curvatureEndomorphism, actual_einstein_decomposition e hRic]
  have he : (fun v => frameTensor e.matrix X (Fin.cons i (Fin.cons k v))) -
      (fun v => frameTensor e.matrix X (Fin.cons k (Fin.cons i v))) =
        -tensorSlotAction (curvatureEndomorphism (Angular.einsteinCurvatureTensor
          (plusWeyl g c e) (minusWeyl g c e)) i k) (frameTensor e.matrix T) := by
    funext v
    have hh := framed_tensor_commutator e.matrix (isUnit_iff_ne_zero.mpr e.det_ne_zero)
      C T X hX i k v
    rw [hc] at hh
    exact hh
  have hb := congrArg (fun S : CovariantCoordinates 5 =>
    blockCoordinatesLinear quaternionMatrix (fun a => S (Fin.cons j a))) he
  change blockCoordinatesLinear quaternionMatrix
    ((fun a => frameTensor e.matrix X (Fin.cons i (Fin.cons k (Fin.cons j a)))) -
      (fun a => frameTensor e.matrix X (Fin.cons k (Fin.cons i (Fin.cons j a))))) =
    gradientBlock (-tensorSlotAction (curvatureEndomorphism (Angular.einsteinCurvatureTensor
      (plusWeyl g c e) (minusWeyl g c e)) i k) (frameTensor e.matrix T)) quaternionMatrix j at hb
  rw [map_sub, gradientBlock_negative_slotAction,
    blockCoordinates_einstein_curvature_action] at hb
  have hr (r : Fin 4) :
      curvatureEndomorphism (Angular.einsteinCurvatureTensor
        (plusWeyl g c e) (minusWeyl g c e)) i k r j =
        -frameCurvature g c e i k r j := by
    change Angular.einsteinCurvatureTensor (plusWeyl g c e) (minusWeyl g c e) i k j r = _
    rw [← actual_einstein_decomposition e hRic]
    exact frameCurvature_last_skew e i k j r
  simp only [hr, neg_smul, Finset.sum_neg_distrib, sub_neg_eq_add] at hb
  exact hb

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiate the proved Weyl Hessian commutator along parallel frames.
Only the ordinary derivative identities already present in the flow data are used. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.parallelInnerNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.parallelInnerNormedSpace
local instance parallelInnerNormedAlgebra_r57b6aa_1 : NormedAlgebra ℝ Mat := Matrix.frobeniusNormedAlgebra
/-- Product differentiation in the matrix bundle, without an eigenframe. -/
theorem hasDerivAt_bundleCurvatureSelf {T : ℝ → Mat} {Z : Mat} {t : ℝ}
    (hT : HasDerivAt T Z t) (i j : Fin 4) :
    HasDerivAt (fun r => bundleCurvatureAction (T r) i j (T r))
      (bundleCurvatureDerivative Z i j (T t) + bundleCurvatureAction (T t) i j Z) t := by
  have hs (r s : Fin 3) := (parallel_hasDerivAt_entry hT r s).smul
    (hasDerivAt_matrixAction hT s)
  have hr (r : Fin 3) := ((hasDerivAt_matrixAction hT r).add
    (HasDerivAt.fun_sum (u := Finset.univ) (fun s _ => hs r s))).const_smul (quaternionMatrix r i j)
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun r _ => hr r)).const_smul (1 / 2 : ℝ)
  let D : Mat := (1 / 2 : ℝ) • ∑ r, quaternionMatrix r i j •
    (matrixAction r Z + ∑ s, (T t r s • matrixAction s Z + Z r s • matrixAction s (T t)))
  change HasDerivAt (fun r => bundleCurvatureAction (T r) i j (T r)) D t at hd
  have hD : D = bundleCurvatureDerivative Z i j (T t) +
      bundleCurvatureAction (T t) i j Z := by
    ext a b
    simp only [D, bundleCurvatureDerivative, bundleCurvatureAction, Matrix.smul_apply,
      Matrix.sum_apply, Matrix.add_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    ring
  rwa [hD] at hd

/-- A pointwise Hessian commutator can be differentiated using only its
parallel derivative fields. -/
theorem inner_commutator_of_derivatives
    (T : ℝ → Mat) (X : ℝ → Hessian) (Z : Mat) (V : Fin 4 → Fin 4 → Mat)
    (t : ℝ) (k j : Fin 4)
    (hcomm : ∀ r, X r k j - X r j k = bundleCurvatureAction (T r) k j (T r))
    (hT : HasDerivAt T Z t)
    (hXkj : HasDerivAt (fun r => X r k j) (V k j) t)
    (hXjk : HasDerivAt (fun r => X r j k) (V j k) t) :
    V k j - V j k =
      bundleCurvatureDerivative Z k j (T t) + bundleCurvatureAction (T t) k j Z := by
  have he : (fun r => X r k j - X r j k) =
      fun r => bundleCurvatureAction (T r) k j (T r) := funext hcomm
  have hd := hXkj.sub hXjk
  change HasDerivAt (fun r => X r k j - X r j k) (V k j - V j k) t at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_bundleCurvatureSelf hT k j)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The inner commutator in the Green formula is forced by the actual
Hessian identity and the existing ordinary parallel-frame derivatives. -/
theorem actual_plusWeylThird_innerCommutator
    (g : SmoothMetric M) (hRic : RicciThree g) {μ : Measure (FrameBundle g)}
    (φ : Fin 4 → FrameFlow g μ)
    (hT : ∀ i t e, HasDerivAt
      (fun r => plusWeyl g ((φ i).map r e).base ((φ i).map r e).frame)
      (plusWeylGradient g ((φ i).map t e).base ((φ i).map t e).frame i) t)
    (hX : ∀ i k j t e, HasDerivAt
      (fun r => plusWeylHessian g ((φ i).map r e).base ((φ i).map r e).frame k j)
      (plusWeylThirdDerivative g ((φ i).map t e).base ((φ i).map t e).frame i k j) t)
    (e : FrameBundle g) (i k j : Fin 4) :
    plusWeylThirdDerivative g e.base e.frame i k j -
        plusWeylThirdDerivative g e.base e.frame i j k =
      bundleCurvatureDerivative (plusWeylGradient g e.base e.frame i) k j
        (plusWeyl g e.base e.frame) +
      bundleCurvatureAction (plusWeyl g e.base e.frame) k j
        (plusWeylGradient g e.base e.frame i) := by
  obtain ⟨e₀, he⟩ := ((φ i).map 0).surjective e
  change (φ i).map 0 e₀ = e at he
  have hc (r : ℝ) :
      plusWeylHessian g ((φ i).map r e₀).base ((φ i).map r e₀).frame k j -
        plusWeylHessian g ((φ i).map r e₀).base ((φ i).map r e₀).frame j k =
      bundleCurvatureAction (plusWeyl g ((φ i).map r e₀).base ((φ i).map r e₀).frame)
        k j (plusWeyl g ((φ i).map r e₀).base ((φ i).map r e₀).frame) := by
    ext a b
    exact actual_plusWeylHessian_commutator _ hRic k j a b
  have hh := inner_commutator_of_derivatives
    (fun r => plusWeyl g ((φ i).map r e₀).base ((φ i).map r e₀).frame)
    (fun r => plusWeylHessian g ((φ i).map r e₀).base ((φ i).map r e₀).frame)
    (plusWeylGradient g ((φ i).map 0 e₀).base ((φ i).map 0 e₀).frame i)
    (fun k j => plusWeylThirdDerivative g ((φ i).map 0 e₀).base ((φ i).map 0 e₀).frame i k j)
    0 k j hc (hT i 0 e₀) (hX i k j 0 e₀) (hX i j k 0 e₀)
  rw [he] at hh
  exact hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normalized Einstein metric supplies all local tensor identities
needed for the Weyl equation. The equation itself is then derived by the
finite Hessian trace calculation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem actual_weylCovariantIdentities (g : SmoothMetric M) (hRic : RicciThree g) :
    WeylCovariantIdentities g where
  symmetric e := (actual_weyl_symmetric e.frame).1
  traceFree e := (actual_weyl_traceFree e.frame hRic).1
  hessianMatrix e i j := (actual_weylHessian_constraints e.frame hRic i j).1
  hessianBianchi e i r := actual_plusWeylHessian_bianchi e.frame hRic i r
  hessianCommutator e i j a b := actual_plusWeylHessian_commutator e.frame hRic i j a b

end
end PositiveEinsteinFour.Geometry
end


section

/-! Orientation distinguishes the two explicit quaternionic two-form spaces. -/

namespace PositiveEinsteinFour.QuaternionFrame

open Matrix TraceHessian PositiveEinsteinFour.Geometry
open Angular (oppositeMatrix)
open scoped BigOperators

noncomputable section

theorem pfaffian_quaternion_zero (P : Mat4) :
    pfaffianFour (P * quaternionMatrix 0 * Pᵀ) = P.det := by
  rw [Matrix.det_succ_row_zero P]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp only [pfaffianFour, sandwich_apply]
  simp [quaternionMatrix, Fin.sum_univ_four, Fin.succAbove, Fin.lt_def]
  ring

theorem pfaffian_quaternion_one (P : Mat4) :
    pfaffianFour (P * quaternionMatrix 1 * Pᵀ) = P.det := by
  rw [Matrix.det_succ_row_zero P]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp only [pfaffianFour, sandwich_apply]
  simp [quaternionMatrix, Fin.sum_univ_four, Fin.succAbove, Fin.lt_def]
  ring

theorem pfaffian_quaternion_two (P : Mat4) :
    pfaffianFour (P * quaternionMatrix 2 * Pᵀ) = P.det := by
  rw [Matrix.det_succ_row_zero P]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
  simp only [pfaffianFour, sandwich_apply]
  simp [quaternionMatrix, Fin.sum_univ_four, Fin.succAbove, Fin.lt_def]
  ring

theorem pfaffian_quaternion (P : Mat4) (s : Fin 3) :
    pfaffianFour (P * quaternionMatrix s * Pᵀ) = P.det := by
  fin_cases s
  · exact pfaffian_quaternion_zero P
  · exact pfaffian_quaternion_one P
  · exact pfaffian_quaternion_two P

theorem selfDual_of_pfaffian (A : Mat4)
    (hupper : upperSquareFour A = 2) (hpf : pfaffianFour A = 1) :
    A 2 3 = A 0 1 ∧ A 1 3 = -A 0 2 ∧ A 1 2 = A 0 3 := by
  have hsq : (A 0 1 - A 2 3) ^ 2 + (A 0 2 + A 1 3) ^ 2 +
      (A 0 3 - A 1 2) ^ 2 = 0 := by
    dsimp [upperSquareFour] at hupper
    dsimp [pfaffianFour] at hpf
    nlinarith
  have h1 : (A 0 1 - A 2 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (A 0 2 + A 1 3), sq_nonneg (A 0 3 - A 1 2)]
  have h2 : (A 0 2 + A 1 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (A 0 1 - A 2 3), sq_nonneg (A 0 3 - A 1 2)]
  have h3 : (A 0 3 - A 1 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (A 0 1 - A 2 3), sq_nonneg (A 0 2 + A 1 3)]
  have := sq_eq_zero_iff.mp h1
  have := sq_eq_zero_iff.mp h2
  have := sq_eq_zero_iff.mp h3
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem selfDual_span (A : Mat4)
    (hsk : ∀ i j, A i j = -A j i)
    (hp : A 2 3 = A 0 1 ∧ A 1 3 = -A 0 2 ∧ A 1 2 = A 0 3) :
    A = imaginaryCombination quaternionMatrix (fun r => A r.succ 0) := by
  have hd := skew_diagonal_zero A hsk
  ext i j
  simp only [imaginaryCombination_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [quaternionMatrix]
  all_goals first | exact hd _ | linarith [hsk 0 1, hsk 0 2, hsk 0 3, hsk 1 2, hsk 1 3, hsk 2 3, hp.1, hp.2.1, hp.2.2]

/-- Positive-orientation orthogonal changes preserve the first quaternionic space. -/
theorem oriented_quaternion_span (P : Mat4) (hP : Pᵀ * P = 1) (hdet : P.det = 1)
    (s : Fin 3) :
    P * quaternionMatrix s * Pᵀ = imaginaryCombination quaternionMatrix
      (fun r => (P * quaternionMatrix s * Pᵀ) r.succ 0) := by
  apply selfDual_span
  · exact conjugate_skew P _ (Angular.quaternionMatrix_transpose s)
  · apply selfDual_of_pfaffian
    · exact upperSquareFour_eq_two _ (conjugate_skew P _ (Angular.quaternionMatrix_transpose s))
        (conjugate_orthogonal P _ hP (quaternion_orthogonal s))
    · rw [pfaffian_quaternion, hdet]

/-- The opposite quaternionic space is preserved by the same frame changes. -/
theorem oriented_opposite_span (P : Mat4) (hP : Pᵀ * P = 1) (hdet : P.det = 1)
    (s : Fin 3) :
    P * oppositeMatrix s * Pᵀ = imaginaryCombination oppositeMatrix
      (fun r => -(P * oppositeMatrix s * Pᵀ) r.succ 0) := by
  apply antiSelfDual_span
  · exact conjugate_skew P _ (oppositeMatrix_transpose s)
  · apply antiSelfDual_of_pfaffian
    · exact upperSquareFour_eq_two _ (conjugate_skew P _ (oppositeMatrix_transpose s))
        (conjugate_orthogonal P _ hP (opposite_orthogonal s))
    · rw [pfaffian_opposite, hdet]

end
end PositiveEinsteinFour.QuaternionFrame
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

/-- Hodge star in the first alternating pair of a covariant four-tensor. -/
def hodgeFirstTensor : CovariantCoordinates 4 →ₗ[ℝ] CovariantCoordinates 4 where
  toFun R a := hodgeStarFour (fun i j => R ![i, j, a 2, a 3]) (a 0) (a 1)
  map_add' R S := by
    funext a
    let P : Mat4 := fun i j => R ![i, j, a 2, a 3]
    let Q : Mat4 := fun i j => S ![i, j, a 2, a 3]
    exact congrArg (fun A : Mat4 => A (a 0) (a 1)) (hodgeStarFour.map_add P Q)
  map_smul' r R := by
    funext a
    let P : Mat4 := fun i j => R ![i, j, a 2, a 3]
    exact congrArg (fun A : Mat4 => A (a 0) (a 1)) (hodgeStarFour.map_smul r P)

/-- The first Pontryagin density; its third is the signature density. -/
def curvaturePontryaginDensity (R : CovariantCoordinates 4) : ℝ :=
  frameTensorPairing R (hodgeFirstTensor R) / (16 * Real.pi ^ 2)

def curvatureSignatureDensity (R : CovariantCoordinates 4) : ℝ :=
  curvaturePontryaginDensity R / 3

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six-dimensional two-form fiber and its actual Hodge involution.
The coordinate order is 01, 02, 03, 12, 13, 23. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormMatrix_hodge (a : TwoFormFour) :
    twoFormMatrix (twoFormHodge a) = hodgeStarFour (twoFormMatrix a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoFormMatrix, twoFormHodge, twoFormHodgeLinear,
    hodgeStarFour]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Lowering the actual chart curvature transformation and pulling back
all four covariant slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Actual lowered curvature is a covariant four-tensor on chart overlaps. -/
theorem curvatureCoordinates_transition (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    curvatureCoordinates g c z = frameTensor (chartTransitionMatrix c d z)
      (curvatureCoordinates g d (chartTransition c d z)) := by
  rw [← loweredMatrixTensor_curvature g c z,
    ← loweredMatrixTensor_curvature g d (chartTransition c d z)]
  exact loweredMatrixTensor_transition _ _ _ _ _
    (isUnit_iff_ne_zero.mpr (chartTransitionMatrix_det_ne_zero g c d z hz hx))
    (by simpa only [Matrix.mul_assoc] using metricInChart_transition g c d z hz hx)
    (coordinateCurvatureMatrix_transition g c d z hz hx)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The infinitesimal orthonormal-frame action on two-forms preserves the
Hodge splitting and the fiber inner product. This is the local algebra
needed for the induced Levi-Civita connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormSkewAction_matrix (b a : TwoFormFour) :
    twoFormMatrix (twoFormSkewAction b a) =
      twoFormMatrix b * twoFormMatrix a - twoFormMatrix a * twoFormMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoFormSkewAction, twoFormMatrix] <;> ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two-form Hodge operator is independent of the chosen positively
oriented orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian QuaternionFrame Angular
open scoped BigOperators

noncomputable section

theorem hodgeStarFour_sandwich_quaternion (P : Mat4) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) (s : Fin 3) :
    hodgeStarFour (P * quaternionMatrix s * Pᵀ) = P * quaternionMatrix s * Pᵀ := by
  rw [oriented_quaternion_span P hP hdet s]
  exact hodgeStarFour_quaternion_combination _

theorem hodgeStarFour_sandwich_opposite (P : Mat4) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) (s : Fin 3) :
    hodgeStarFour (P * oppositeMatrix s * Pᵀ) = -(P * oppositeMatrix s * Pᵀ) := by
  rw [oriented_opposite_span P hP hdet s]
  exact hodgeStarFour_opposite_combination _

theorem twoFormMatrix_quaternion_decomposition (a : TwoFormFour) :
    twoFormMatrix a =
      imaginaryCombination quaternionMatrix
        ![-(a 0 + a 5) / 2, -(a 1 - a 4) / 2, -(a 2 + a 3) / 2] +
      imaginaryCombination oppositeMatrix
        ![(a 0 - a 5) / 2, (a 1 + a 4) / 2, (a 2 - a 3) / 2] := by
  ext i j
  simp only [imaginaryCombination_apply, Matrix.add_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    norm_num [twoFormMatrix, quaternionMatrix, oppositeMatrix, oppositeQuaternion] <;> ring

theorem hodgeStarFour_oriented_frame_change (P : Mat4) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) (a : TwoFormFour) :
    hodgeStarFour (P * twoFormMatrix a * Pᵀ) =
      P * hodgeStarFour (twoFormMatrix a) * Pᵀ := by
  have hp (u : Fin 3 → ℝ) :
      hodgeStarFour (P * imaginaryCombination quaternionMatrix u * Pᵀ) =
        P * imaginaryCombination quaternionMatrix u * Pᵀ := by
    rw [sandwich_combination]
    simp only [imaginaryCombination, map_sum, map_smul,
      hodgeStarFour_sandwich_quaternion P hP hdet]
  have hm (u : Fin 3 → ℝ) :
      hodgeStarFour (P * imaginaryCombination oppositeMatrix u * Pᵀ) =
        -(P * imaginaryCombination oppositeMatrix u * Pᵀ) := by
    rw [sandwich_combination]
    simp only [imaginaryCombination, map_sum, map_smul,
      hodgeStarFour_sandwich_opposite P hP hdet, smul_neg, Finset.sum_neg_distrib]
  rw [twoFormMatrix_quaternion_decomposition]
  simp only [Matrix.mul_add, Matrix.add_mul, map_add, hp, hm,
    hodgeStarFour_quaternion_combination, hodgeStarFour_opposite_combination,
    Matrix.mul_neg, Matrix.neg_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A four-column Gram--Schmidt normalizer with entrywise smooth dependence
on the positive metric matrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem metricPair_pos (G : Mat4) (hG : G.PosDef) (u : CoordinateColumn) (hu : u ≠ 0) :
    0 < metricPair G u u := by
  simpa only [metricPair, star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    using hG.dotProduct_mulVec_pos hu

theorem metricPair_symm (G : Mat4) (hG : G.IsHermitian) (u v : CoordinateColumn) :
    metricPair G u v = metricPair G v u := by
  have hs (i j : Fin 4) : G i j = G j i := by
    have h := congrArg (fun A : Mat4 => A j i) hG.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  unfold metricPair
  rw [Finset.sum_comm]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  rw [hs]
  ring

theorem metricPair_scaled (G : Mat4) (u v : CoordinateColumn) (a b : ℝ) :
    metricPair G (fun i => a * u i) (fun i => b * v i) = a * b * metricPair G u v := by
  simp only [metricPair, Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

/-- Smoothness of the finite bilinear pairing with varying coefficients. -/
theorem metricPair_contDiffAt {G : FourSpace → Mat4} {u v : FourSpace → CoordinateColumn}
    {z : FourSpace} (hG : ∀ i j, ContDiffAt ℝ ∞ (fun w => G w i j) z)
    (hu : ∀ i, ContDiffAt ℝ ∞ (fun w => u w i) z)
    (hv : ∀ i, ContDiffAt ℝ ∞ (fun w => v w i) z) :
    ContDiffAt ℝ ∞ (fun w => metricPair (G w) (u w) (v w)) z := by
  unfold metricPair
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((hu i).mul (hG i j)).mul (hv j)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Christoffel transformation transports the covariant derivative
of every finite covariant tensor.  This is used only at ranks four to seven. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Naturality of the coordinate Levi-Civita derivative. The tensor equality
is local; no choice of a global frame is involved. -/
theorem covariantDerivative_chart_transition (g : SmoothMetric M) (c d : M)
    {n : ℕ} (S T : FourSpace → CovariantCoordinates n) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) (chartTransition c d z))
    (hS : S =ᶠ[𝓝 z] fun w => frameTensor (chartTransitionMatrix c d w)
      (T (chartTransition c d w))) :
    covariantDerivative g c S z = frameTensor (chartTransitionMatrix c d z)
      (covariantDerivative g d T (chartTransition c d z)) := by
  rw [covariantDerivative_congr g c hS]
  funext a
  obtain ⟨i, v, rfl⟩ := Fin.exists_cons a
  rw [covariantDerivative_direction]
  rw [covariantDirection_pullback (chartTransition c d) (chartTransitionMatrix c d)
    (connectionMatrix g c) (connectionMatrix g d) T z
    ((chartTransition_contDiffAt c d z hz hx).differentiableAt (by first | simp | exact_mod_cast le_top))
    (fun a b => (chartTransitionMatrix_contDiffAt c d z hz hx a b).differentiableAt
      (by first | simp | exact_mod_cast le_top)) hT rfl i (chart_connection_intertwining g c d z hz hx i)]
  rw [frameTensor_cons, frameTensor_weighted_sum]
  apply Finset.sum_congr rfl
  intro r _
  congr 1

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual local orthonormal frames obtained from smooth coordinate vectors
by the explicit four-column normalizer. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]


theorem chartTransitionMatrix_to_center (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    chartTransitionMatrix c ((chartAt FourSpace c).symm z) z = chartInverseMatrix c z := by
  let x := (chartAt FourSpace c).symm z
  let D : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace x) x
  have hid : D = ContinuousLinearMap.id ℝ FourSpace := by
    ext v i
    have h := congrArg (fun K : TangentSpace I4 x →L[ℝ]
        TangentSpace I4 (extChartAt I4 x x) => K (show TangentSpace I4 x from v))
      (mfderiv_extChartAt_self (I := I4) (x := x))
    have hv : D v = v := by
      simp only [I4, extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] at h
      change D v = v at h
      exact h
    exact congrArg (fun w : FourSpace => w i) hv
  let L : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (chartAt FourSpace c).symm z
  have hf : fderiv ℝ (chartTransition c x) z = D.comp L :=
    chartTransition_fderiv c x z hz (mem_chart_source FourSpace x)
  rw [hid, ContinuousLinearMap.id_comp] at hf
  ext i j
  exact congrArg (fun K : FourSpace →L[ℝ] FourSpace => K (coordinateVector j) i) hf

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual changes of orthonormal frame on the six two-form coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix

noncomputable section

theorem twoFormFrameAction_one (a : TwoFormFour) : twoFormFrameAction 1 a = a := by
  simp only [twoFormFrameAction, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
    twoFormExtract_matrix]

theorem twoFormFrameAction_hodge (P : Mat4) (hP : Pᵀ * P = 1) (hdet : P.det = 1)
    (a : TwoFormFour) :
    twoFormFrameAction P (twoFormHodge a) = twoFormHodge (twoFormFrameAction P a) := by
  apply twoFormMatrix_injective
  rw [twoFormMatrix_frameAction, twoFormMatrix_hodge, twoFormMatrix_hodge,
    twoFormMatrix_frameAction]
  have hPt : Pᵀᵀ * Pᵀ = 1 := by
    rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.mp hP
  simpa only [Matrix.transpose_transpose, Matrix.det_transpose] using
    (hodgeStarFour_oriented_frame_change Pᵀ hPt (by simpa using hdet) a).symm

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FourHeatGaussianApproximation
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian dilation and its actual approximate-identity limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped _root_.Topology

noncomputable section

theorem fourHeatGaussian_rescaled_bound (f : FourSpace → ℝ)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) (x : FourSpace) (t : ℝ) (z : FourSpace) :
    ‖fourHeatGaussian 1 z * f (x - Real.sqrt t • z)‖ ≤ fourHeatGaussian 1 z * C := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (fourHeatGaussian_pos 1 zero_lt_one z)]
  exact mul_le_mul_of_nonneg_left (hC _) (fourHeatGaussian_pos 1 zero_lt_one z).le

theorem fourHeatGaussian_rescaled_limit (f : FourSpace → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) (x : FourSpace) :
    Tendsto (fun t : ℝ => ∫ z : FourSpace,
      fourHeatGaussian 1 z * f (x - Real.sqrt t • z)) (𝓝 0) (𝓝 (f x)) := by
  have hd := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure FourSpace)) (l := 𝓝 (0 : ℝ))
    (F := fun t z => fourHeatGaussian 1 z * f (x - Real.sqrt t • z))
    (f := fun z => fourHeatGaussian 1 z * f x)
    (fun z : FourSpace => fourHeatGaussian 1 z * C)
    (Eventually.of_forall (fourHeatGaussian_rescaled_measurable f hf x))
    (Eventually.of_forall fun t => Eventually.of_forall
      (fourHeatGaussian_rescaled_bound f C hC x t))
    ((fourHeatGaussian_integrable 1 zero_lt_one).mul_const C)
    (Eventually.of_forall (fourHeatGaussian_rescaled_pointwise f hf x))
  simpa only [integral_mul_const, fourHeatGaussian_mass 1 zero_lt_one, one_mul] using hd

theorem fourHeatGaussian_approximate_identity (f : FourSpace → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) (x : FourSpace) :
    Tendsto (fun t : ℝ => ∫ z : FourSpace, fourHeatGaussian t z * f (x - z))
      (𝓝[Set.Ioi 0] 0) (𝓝 (f x)) := by
  apply ((fourHeatGaussian_rescaled_limit f hf C hC x).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (fourHeatGaussian_integral_dilate t ht f x).symm

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_FrameOrientationContinuity
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous frame curves stay in the same orientation component. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

/-- A continuous frame flow initialized at the identity preserves each
orientation component, independently of measure preservation. -/
theorem FrameFlow.orientation_preserving {μ : Measure (FrameBundle g)}
    (φ : FrameFlow g μ) (hzero : ∀ e, φ.map 0 e = e) (o : FrameOrientation g)
    (t : ℝ) (e : FrameBundle g) :
    φ.map t e ∈ o.positive ↔ e ∈ o.positive := by
  have hγ : Continuous (fun s : ℝ => φ.map s e) :=
    φ.continuous.comp (continuous_id.prodMk continuous_const)
  simpa only [hzero] using o.mem_iff_of_continuous_curve (fun s => φ.map s e) hγ t 0

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicJacobiAlgebra
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instCompactSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instSecondCountableTopologyOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite algebra relating the linearized coordinate geodesic
equation to the curvature convention used by the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem actual_jacobiConnection_comm (g : SmoothMetric M) (c : M) (z : FourSpace)
    (v w : JacobiCoordinateVector) :
    jacobiConnection (fun i => connectionMatrix g c i z) v *ᵥ w =
      jacobiConnection (fun i => connectionMatrix g c i z) w *ᵥ v :=
  jacobiConnection_mulVec_comm _ (fun a i j => christoffel_comm g c z a i j) v w

theorem actual_jacobiCurvature_eq (g : SmoothMetric M) (c : M) (z : FourSpace)
    (v w : JacobiCoordinateVector) :
    jacobiCurvature (fun i => connectionMatrix g c i z)
        (fun i j => matrixPartial (connectionMatrix g c j) i z) v w =
      ∑ i, ∑ j, (v i * w j) • coordinateCurvatureMatrix g c i j z := rfl

theorem actual_linearized_geodesic_curvature_identity
    (g : SmoothMetric M) (c : M) (z : FourSpace)
    (v a y w b : JacobiCoordinateVector)
    (ha : a = -(jacobiConnection (fun i => connectionMatrix g c i z) v *ᵥ v))
    (hb : b = -(jacobiConnectionDerivative
        (fun i j => matrixPartial (connectionMatrix g c j) i z) y v *ᵥ v) -
      jacobiConnection (fun i => connectionMatrix g c i z) w *ᵥ v -
      jacobiConnection (fun i => connectionMatrix g c i z) v *ᵥ w) :
    b + jacobiConnectionDerivative
        (fun i j => matrixPartial (connectionMatrix g c j) i z) v v *ᵥ y +
      jacobiConnection (fun i => connectionMatrix g c i z) a *ᵥ y +
      (2 : ℝ) • (jacobiConnection (fun i => connectionMatrix g c i z) v *ᵥ w) +
      jacobiConnection (fun i => connectionMatrix g c i z) v *ᵥ
        (jacobiConnection (fun i => connectionMatrix g c i z) v *ᵥ y) +
      (∑ i, ∑ j, (y i * v j) • coordinateCurvatureMatrix g c i j z) *ᵥ v = 0 := by
  have hD (r a i j : Fin 4) :
      matrixPartial (connectionMatrix g c i) r z a j =
        matrixPartial (connectionMatrix g c j) r z a i := by
    change partialDeriv (fun p => christoffel g c p a i j) r z =
      partialDeriv (fun p => christoffel g c p a j i) r z
    exact congrArg (fun f : FourSpace → ℝ => partialDeriv f r z)
      (funext fun p => christoffel_comm g c p a i j)
  exact linearized_geodesic_curvature_identity _ _
    (fun a i j => christoffel_comm g c z a i j) hD v a y w b ha hb

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricChartDistance
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A bounded inverse-chart differential controls the actual Riemannian
distance on a convex chart region. This is the local estimate needed for
finiteness of the metric's Hausdorff volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metricEDistance_chart_symm_le (g : SmoothMetric M) (c : M)
    (s : Set FourSpace) (hs : Convex ℝ s) (hst : s ⊆ (chartAt FourSpace c).target)
    (K : ℝ≥0)
    (hK : ∀ z ∈ s, ∀ v : FourSpace,
      metricTangentENorm g ((chartAt FourSpace c).symm z)
        (mfderiv I4 I4 (chartAt FourSpace c).symm z v) ≤ K * ‖v‖ₑ)
    (x y : FourSpace) (hx : x ∈ s) (hy : y ∈ s) :
    metricEDistance g ((chartAt FourSpace c).symm x) ((chartAt FourSpace c).symm y) ≤
      K * edist x y := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let η : ℝ →ᴬ[ℝ] FourSpace := ContinuousAffineMap.lineMap x y
  let γ : ℝ → M := (chartAt FourSpace c).symm ∘ η
  have hη : MapsTo η (Icc 0 1) s := by
    rw [mapsTo_iff_image_subset, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap]
    exact hs.segment_subset hx hy
  have hηsmooth : ContMDiff 𝓘(ℝ, ℝ) I4 1 η := by
    rw [contMDiff_iff_contDiff]
    exact η.contDiff
  have hchart : ContMDiffOn I4 I4 1 (chartAt FourSpace c).symm
      (chartAt FourSpace c).target := contMDiffOn_chart_symm
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc 0 1) :=
    hchart.comp hηsmooth.contMDiffOn (fun t ht => hst (hη ht))
  have hstart : γ 0 = (chartAt FourSpace c).symm x := by
    simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  have hend : γ 1 = (chartAt FourSpace c).symm y := by
    simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc 0 1) t 1‖ₑ ≤ K * ‖y - x‖ₑ := by
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc 0 1) t := by
      rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
    have hc : MDifferentiableAt I4 I4 (chartAt FourSpace c).symm (η t) :=
      (contMDiffAt_symm_of_mem_maximalAtlas
        (n := ∞) (IsManifold.chart_mem_maximalAtlas c) (hst (hη ht))).mdifferentiableAt (by simp)
    have hd : mfderivWithin 𝓘(ℝ, ℝ) I4 η (Icc 0 1) t 1 = y - x := by
      have hd' : (fderivWithin ℝ (fun s : ℝ => η s) (Icc 0 1) t) 1 = y - x := by
        rw [fderivWithin_derivWithin]
        exact (AffineMap.hasDerivWithinAt_lineMap (a := x) (b := y)).derivWithin
          (uniqueDiffOn_Icc zero_lt_one t ht)
      simpa only [mfderivWithin_eq_fderivWithin] using! hd'
    have he := mfderiv_comp_mfderivWithin t hc
      (hηsmooth.mdifferentiable (by simp) t).mdifferentiableWithinAt hu
    change ‖mfderivWithin 𝓘(ℝ, ℝ) I4
      ((chartAt FourSpace c).symm ∘ η) (Icc 0 1) t 1‖ₑ ≤ _
    rw [he, ContinuousLinearMap.comp_apply, hd]
    exact hK (η t) (hη ht) (y - x)
  change Manifold.riemannianEDist I4 _ _ ≤ _
  calc
    _ ≤ Manifold.pathELength I4 γ 0 1 :=
      Manifold.riemannianEDist_le_pathELength hγ hstart hend zero_le_one
    _ = ∫⁻ t in Icc (0 : ℝ) 1,
        ‖mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc 0 1) t 1‖ₑ :=
      Manifold.pathELength_eq_lintegral_mfderivWithin_Icc
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, (K : ℝ≥0∞) * ‖y - x‖ₑ :=
      setLIntegral_mono' measurableSet_Icc hspeed
    _ = K * edist x y := by
      simp only [lintegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
        Measure.restrict_apply_univ, mul_one, edist_eq_enorm_sub, enorm_sub_rev]

theorem exists_metric_chart_bound (g : SmoothMetric M) (c : M) :
    ∃ r > (0 : ℝ), ∃ K : ℝ≥0,
      Metric.closedBall (chartAt FourSpace c c) r ⊆ (chartAt FourSpace c).target ∧
      ∀ x ∈ Metric.closedBall (chartAt FourSpace c c) r,
      ∀ y ∈ Metric.closedBall (chartAt FourSpace c c) r,
        metricEDistance g ((chartAt FourSpace c).symm x) ((chartAt FourSpace c).symm y) ≤
          K * edist x y := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  obtain ⟨K, _hKpos, hK⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt I4 c
  have hK' : ∀ᶠ z in 𝓝 (chartAt FourSpace c c),
      (let L : FourSpace →L[ℝ] TangentSpace I4 ((chartAt FourSpace c).symm z) :=
        mfderiv I4 I4 (chartAt FourSpace c).symm z
       ‖L‖ₑ) < K := by
    simpa only [I4, extChartAt_coe, extChartAt_coe_symm, mfderivWithin_univ,
      ModelWithCorners.range_eq_univ, nhdsWithin_univ, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
      Set.range_id] using! hK
  have hc : chartAt FourSpace c c ∈ (chartAt FourSpace c).target :=
    (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem ((chartAt FourSpace c).open_target.mem_nhds hc) hK')
  have hsmall : Metric.closedBall (chartAt FourSpace c c) (r / 2) ⊆
      Metric.ball (chartAt FourSpace c c) r :=
    Metric.closedBall_subset_ball (by linarith)
  have htarget : Metric.closedBall (chartAt FourSpace c c) (r / 2) ⊆
      (chartAt FourSpace c).target := fun z hz => (hball (hsmall hz)).1
  refine ⟨r / 2, by positivity, K, htarget, ?_⟩
  intro x hx y hy
  apply metricEDistance_chart_symm_le g c _ (convex_closedBall _ _) htarget K _ x y hx hy
  intro z hz v
  let L : FourSpace →L[ℝ] TangentSpace I4 ((chartAt FourSpace c).symm z) :=
    mfderiv I4 I4 (chartAt FourSpace c).symm z
  change ‖L v‖ₑ ≤ K * ‖v‖ₑ
  apply (ContinuousLinearMap.le_opENorm L v).trans
  gcongr
  exact (hball (hsmall hz)).2.le

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricChartPath
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A chart differential bound converts the length of an actual smooth
path into a Euclidean endpoint bound. This is the reverse estimate needed
to establish positive local Hausdorff mass. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chart_edist_le_pathELength (g : SmoothMetric M) (c : M)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I4 1 γ)
    (hsource : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (chartAt FourSpace c).source)
    (K : ℝ≥0)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace I4 (γ t),
      ‖mfderiv I4 I4 (chartAt FourSpace c) (γ t) v‖ₑ ≤
        K * metricTangentENorm g (γ t) v) :
    edist (chartAt FourSpace c (γ 0)) (chartAt FourSpace c (γ 1)) ≤
      K * (let : RiemannianBundle (TangentSpace I4 : M → Type _) :=
        ⟨g.toRiemannianMetric⟩; Manifold.pathELength I4 γ 0 1) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let η : ℝ → FourSpace := chartAt FourSpace c ∘ γ
  have hη : ContDiffOn ℝ 1 η (Icc 0 1) :=
    ((contMDiffOn_chart (I := I4) (n := 1) (x := c)).comp hγ.contMDiffOn hsource).contDiffOn
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖derivWithin η (Icc 0 1) t‖ₑ ≤
        K * ‖mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc 0 1) t 1‖ₑ := by
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc 0 1) t := by
      rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
    have hc : MDifferentiableAt I4 I4 (chartAt FourSpace c) (γ t) :=
      (contMDiffAt_of_mem_maximalAtlas (n := 1)
        (IsManifold.chart_mem_maximalAtlas c) (hsource t ht)).mdifferentiableAt one_ne_zero
    have he := mfderiv_comp_mfderivWithin t hc
      (hγ.mdifferentiable one_ne_zero t).mdifferentiableWithinAt hu
    rw [← fderivWithin_derivWithin, ← mfderivWithin_eq_fderivWithin]
    change ‖mfderivWithin 𝓘(ℝ, ℝ) I4 (chartAt FourSpace c ∘ γ) (Icc 0 1) t 1‖ₑ ≤ _
    rw [he, ContinuousLinearMap.comp_apply]
    exact hK t ht _
  calc
    _ = ‖η 1 - η 0‖ₑ := by rw [edist_eq_enorm_sub, enorm_sub_rev]; rfl
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖derivWithin η (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hη zero_le_one
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
        (K : ℝ≥0∞) * ‖mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc 0 1) t 1‖ₑ :=
      setLIntegral_mono' measurableSet_Icc hderiv
    _ = K * Manifold.pathELength I4 γ 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricChartLipschitz
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chart map is Lipschitz on a sufficiently small Riemannian ball.
Short paths between points of the smaller ball stay in the neighborhood
where the chart differential is bounded. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M]

theorem exists_metric_chart_lipschitz (g : SmoothMetric M) (c : M) :
    ∃ s ∈ 𝓝 c, s ⊆ (chartAt FourSpace c).source ∧
      ∃ K : ℝ≥0, ∀ x ∈ s, ∀ y ∈ s,
        edist (chartAt FourSpace c x) (chartAt FourSpace c y) ≤
          K * metricEDistance g x y := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  obtain ⟨K, hKpos, hK⟩ := eventually_enorm_mfderiv_extChartAt_lt I4 c
  have hK' : ∀ᶠ x in 𝓝 c,
      (let L : TangentSpace I4 x →L[ℝ] FourSpace :=
        mfderiv I4 I4 (chartAt FourSpace c) x
       ‖L‖ₑ) < K := by
    simpa only [I4, extChartAt_coe, modelWithCornersSelf_coe,
      Function.id_comp] using! hK
  let U : Set M := (chartAt FourSpace c).source ∩
    {x | (let L : TangentSpace I4 x →L[ℝ] FourSpace :=
      mfderiv I4 I4 (chartAt FourSpace c) x; ‖L‖ₑ) < K}
  have hU : U ∈ 𝓝 c := Filter.inter_mem (chart_source_mem_nhds FourSpace c) hK'
  obtain ⟨ε, hε, hεU⟩ := setOfPred_riemannianEDist_lt_subset_nhds I4 hU
  let δ : ℝ≥0 := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsum : (δ : ℝ≥0∞) + δ + δ + δ = ε := by
    exact_mod_cast (show δ + δ + δ + δ = ε by dsimp [δ]; ring)
  let s : Set M := {x | edist c x < (δ : ℝ≥0∞)}
  have hs : s ∈ 𝓝 c := by
    have hopen : IsOpen s := isOpen_lt (continuous_const.edist continuous_id) continuous_const
    exact hopen.mem_nhds (by simpa [s] using hδ)
  have hsU : s ⊆ U := by
    intro x hx
    apply hεU
    change edist c x < (ε : ℝ≥0∞)
    exact hx.trans_le (by
      calc
        (δ : ℝ≥0∞) ≤ δ + δ + δ + δ := by
          simp only [add_assoc]
          exact le_self_add
        _ = ε := hsum)
  refine ⟨s, hs, fun x hx => (hsU hx).1, K, ?_⟩
  intro x hx y hy
  have hxy : edist x y < (δ : ℝ≥0∞) + δ + δ := by
    calc
      edist x y ≤ edist c x + edist c y := edist_triangle_left _ _ _
      _ < δ + δ := ENNReal.add_lt_add hx hy
      _ ≤ δ + δ + δ := le_add_right le_rfl
  have hbound (r : {r : ℝ≥0∞ // edist x y < r ∧ r < (δ : ℝ≥0∞) + δ + δ}) :
      edist (chartAt FourSpace c x) (chartAt FourSpace c y) ≤ K * (r : ℝ≥0∞) := by
    obtain ⟨γ, hγx, hγy, hγ, hlen, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt r.property.1 zero_lt_one
    have hγU (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ U := by
      apply hεU
      change edist c (γ t) < (ε : ℝ≥0∞)
      calc
        edist c (γ t) ≤ edist c x + edist x (γ t) := edist_triangle _ _ _
        _ ≤ edist c x + Manifold.pathELength I4 γ 0 t := by
          gcongr
          exact Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn hγx rfl ht.1
        _ ≤ edist c x + Manifold.pathELength I4 γ 0 1 := by
          gcongr
          exact ht.2
        _ < δ + (r : ℝ≥0∞) := ENNReal.add_lt_add hx hlen
        _ < δ + (δ + δ + δ) := ENNReal.add_lt_add_left ENNReal.coe_ne_top r.property.2
        _ = ε := by simpa only [add_assoc] using hsum
    have hchart := chart_edist_le_pathELength g c γ hγ (fun t ht => (hγU t ht).1) K
      (fun t ht v => by
        let L : TangentSpace I4 (γ t) →L[ℝ] FourSpace :=
          mfderiv I4 I4 (chartAt FourSpace c) (γ t)
        change ‖L v‖ₑ ≤ K * ‖v‖ₑ
        apply (ContinuousLinearMap.le_opENorm L v).trans
        gcongr
        exact (hγU t ht).2.le)
    rw [hγx, hγy] at hchart
    exact hchart.trans (mul_le_mul_right hlen.le _)
  change edist (chartAt FourSpace c x) (chartAt FourSpace c y) ≤ K * edist x y
  rw [← iInf_open_interval_p0 (edist x y) ((δ : ℝ≥0∞) + δ + δ) hxy,
    ENNReal.mul_iInf_of_ne (by exact_mod_cast hKpos.ne') ENNReal.coe_ne_top]
  exact le_iInf hbound

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RiemannianVolumeFinite
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness and bounded inverse-chart differentials imply finiteness
of the actual four-dimensional Riemannian Hausdorff measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem volumeMeasure_lt_top [CompactSpace M] (g : SmoothMetric M) :
    volumeMeasure g Set.univ < ⊤ := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  let μ : Measure M := Measure.hausdorffMeasure 4
  have hlocal (c : M) : μ.FiniteAtFilter (𝓝 c) := by
    obtain ⟨r, hr, K, _htarget, hK⟩ := exists_metric_chart_bound g c
    let B := Metric.closedBall (chartAt FourSpace c c) r
    have hB : (Measure.hausdorffMeasure 4 : Measure FourSpace) B < ⊤ := by
      let _ := fourSpace_hausdorff_haar
      exact (isCompact_closedBall _ _).measure_lt_top
    have hLip : LipschitzOnWith K (chartAt FourSpace c).symm B := by
      intro x hx y hy
      exact hK x hx y hy
    have hfinite : μ ((chartAt FourSpace c).symm '' B) < ⊤ := by
      apply lt_of_le_of_lt (hLip.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 4))
      rw [show (4 : ℝ) = (4 : ℕ) by norm_num, ENNReal.rpow_natCast]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hB
    refine ⟨(chartAt FourSpace c).symm '' B, ?_, hfinite⟩
    have hc : chartAt FourSpace c c ∈ (chartAt FourSpace c).target :=
      (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
    have hn := (chartAt FourSpace c).symm.image_mem_nhds hc
      (Metric.closedBall_mem_nhds (chartAt FourSpace c c) hr)
    simpa only [(chartAt FourSpace c).left_inv (mem_chart_source FourSpace c)] using hn
  let _ : IsLocallyFiniteMeasure μ := ⟨hlocal⟩
  have hfinite : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
  change (ENNReal.ofReal (Real.pi ^ 2 / 32) • μ) Set.univ < ⊤
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RiemannianVolumePositive
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nonempty smooth Riemannian four-manifold has positive Hausdorff
volume. The proof compares a small neighborhood with its Euclidean chart
using the actual Riemannian distance. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem volumeMeasure_pos [Nonempty M] (g : SmoothMetric M) :
    0 < volumeMeasure g Set.univ := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  let μ : Measure M := Measure.hausdorffMeasure 4
  let ν : Measure FourSpace := Measure.hausdorffMeasure 4
  let : Measure.IsAddHaarMeasure ν := by
    simpa [ν, FourSpace] using
      (inferInstance : Measure.IsAddHaarMeasure
        (Measure.hausdorffMeasure (Module.finrank ℝ FourSpace) : Measure FourSpace))
  obtain ⟨c⟩ := ‹Nonempty M›
  obtain ⟨s, hs, _hsource, K, hK⟩ := exists_metric_chart_lipschitz g c
  have hLip : LipschitzOnWith K (chartAt FourSpace c) s := by
    intro x hx y hy
    exact hK x hx y hy
  have himage : (chartAt FourSpace c) '' s ∈ 𝓝 (chartAt FourSpace c c) :=
    (chartAt FourSpace c).image_mem_nhds (mem_chart_source FourSpace c) hs
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp himage
  have himage_pos : 0 < ν ((chartAt FourSpace c) '' s) :=
    lt_of_lt_of_le (Metric.isOpen_ball.measure_pos ν (Metric.nonempty_ball.mpr hr))
      (measure_mono hball)
  have hs_pos : 0 < μ s := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have h := hLip.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 4)
    change ν ((chartAt FourSpace c) '' s) ≤ (K : ℝ≥0∞) ^ (4 : ℝ) * μ s at h
    rw [hz, mul_zero] at h
    exact (not_le_of_gt himage_pos) h
  have hmass : 0 < μ Set.univ := hs_pos.trans_le (measure_mono (subset_univ s))
  change 0 < (ENNReal.ofReal (Real.pi ^ 2 / 32) • μ) Set.univ
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' hmass.ne'

theorem actual_finitePositiveVolume [Nonempty M] [CompactSpace M] (g : SmoothMetric M) :
    FinitePositiveVolume g :=
  ⟨volumeMeasure_pos g, volumeMeasure_lt_top g⟩

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelMeasure
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Angular.coordinateFlip_apply _root_.OAI.PositiveEinsteinFour.Angular.coordinatePermutation_apply _root_.OAI.PositiveEinsteinFour.Angular.pairMix_coordinate _root_.OAI.PositiveEinsteinFour.Angular.planeRotation_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverChart_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_deck _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverDeck_proj _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverLocal_apply _root_.OAI.PositiveEinsteinFour.Geometry.orientationCoverMetric_inner _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_deck_mfderiv _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_projection_mfderiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Riemannian volume has full support.  This follows directly
from the local Lipschitz chart comparison, without an assumed density formula. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem volumeMeasure_open_pos (g : SmoothMetric M) (U : Set M)
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < volumeMeasure g U := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  let μ : Measure M := Measure.hausdorffMeasure 4
  let ν : Measure FourSpace := Measure.hausdorffMeasure 4
  let : Measure.IsAddHaarMeasure ν := by
    simpa [ν, FourSpace] using
      (inferInstance : Measure.IsAddHaarMeasure
        (Measure.hausdorffMeasure (Module.finrank ℝ FourSpace) : Measure FourSpace))
  obtain ⟨c, hc⟩ := hne
  obtain ⟨s, hs, _, K, hK⟩ := exists_metric_chart_lipschitz g c
  have hLip : LipschitzOnWith K (chartAt FourSpace c) (s ∩ U) := by
    intro x hx y hy
    exact hK x hx.1 y hy.1
  have himage : (chartAt FourSpace c) '' (s ∩ U) ∈ 𝓝 (chartAt FourSpace c c) :=
    (chartAt FourSpace c).image_mem_nhds (mem_chart_source FourSpace c)
      (Filter.inter_mem hs (hU.mem_nhds hc))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp himage
  have himage_pos : 0 < ν ((chartAt FourSpace c) '' (s ∩ U)) :=
    lt_of_lt_of_le (Metric.isOpen_ball.measure_pos ν (Metric.nonempty_ball.mpr hr))
      (measure_mono hball)
  have hs_pos : 0 < μ (s ∩ U) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have h := hLip.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 4)
    change ν ((chartAt FourSpace c) '' (s ∩ U)) ≤
      (K : ℝ≥0∞) ^ (4 : ℝ) * μ (s ∩ U) at h
    rw [hz, mul_zero] at h
    exact (not_le_of_gt himage_pos) h
  have hmass : 0 < μ U := hs_pos.trans_le (measure_mono inter_subset_right)
  change 0 < (ENNReal.ofReal (Real.pi ^ 2 / 32) • μ) U
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by positivity)).ne' hmass.ne'

theorem volumeMeasure_isOpenPosMeasure (g : SmoothMetric M) :
    (volumeMeasure g).IsOpenPosMeasure :=
  ⟨fun U hU hne => (volumeMeasure_open_pos g U hU hne).ne'⟩

theorem normalizedVolume_isOpenPosMeasure [Nonempty M] [CompactSpace M]
    (g : SmoothMetric M) : (normalizedVolume g).IsOpenPosMeasure := by
  let := volumeMeasure_isOpenPosMeasure g
  exact Measure.isOpenPosMeasure_smul _
    (ENNReal.inv_ne_zero.mpr (actual_finitePositiveVolume g).finite.ne)

end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricLinearChartPath
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Path-length comparisons after a fixed linear change of chart
coordinates. These retain the sharp constants supplied by a frozen
orthonormal frame, instead of replacing them by a coarse operator norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem linear_chart_edist_le_pathELength (g : SmoothMetric M) (c : M)
    (A : FourSpace →L[ℝ] FourSpace)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I4 1 γ)
    (hsource : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (chartAt FourSpace c).source)
    (K : ℝ≥0)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : TangentSpace I4 (γ t),
      ‖A (mfderiv I4 I4 (chartAt FourSpace c) (γ t) v)‖ₑ ≤
        K * metricTangentENorm g (γ t) v) :
    edist (A (chartAt FourSpace c (γ 0))) (A (chartAt FourSpace c (γ 1))) ≤
      K * (let : RiemannianBundle (TangentSpace I4 : M → Type _) :=
        ⟨g.toRiemannianMetric⟩; Manifold.pathELength I4 γ 0 1) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let η : ℝ → FourSpace := A ∘ chartAt FourSpace c ∘ γ
  have hc : ContDiffOn ℝ 1 (chartAt FourSpace c ∘ γ) (Icc 0 1) :=
    ((contMDiffOn_chart (I := I4) (n := 1) (x := c)).comp
      hγ.contMDiffOn hsource).contDiffOn
  have hη : ContDiffOn ℝ 1 η (Icc 0 1) := A.contDiff.comp_contDiffOn hc
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖derivWithin η (Icc 0 1) t‖ₑ ≤
        K * ‖mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc 0 1) t 1‖ₑ := by
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc 0 1) t := by
      rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
    have hchart : MDifferentiableAt I4 I4 (chartAt FourSpace c) (γ t) :=
      (contMDiffAt_of_mem_maximalAtlas (n := 1)
        (IsManifold.chart_mem_maximalAtlas c) (hsource t ht)).mdifferentiableAt one_ne_zero
    have he := mfderiv_comp_mfderivWithin t hchart
      (hγ.mdifferentiable one_ne_zero t).mdifferentiableWithinAt hu
    have hlin := A.hasFDerivAt.comp_hasFDerivWithinAt t
      ((hc.differentiableOn one_ne_zero t ht).hasFDerivWithinAt)
    have hlin' := hlin.fderivWithin (uniqueDiffOn_Icc zero_lt_one t ht)
    rw [← fderivWithin_derivWithin]
    change ‖(fderivWithin ℝ (A ∘ (chartAt FourSpace c ∘ γ)) (Icc 0 1) t) 1‖ₑ ≤ _
    rw [hlin', ContinuousLinearMap.comp_apply, ← mfderivWithin_eq_fderivWithin, he]
    change ‖A (mfderiv I4 I4 (chartAt FourSpace c) (γ t)
      (mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc 0 1) t 1))‖ₑ ≤ _
    exact hK t ht _
  calc
    _ = ‖η 1 - η 0‖ₑ := by rw [edist_eq_enorm_sub, enorm_sub_rev]; rfl
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖derivWithin η (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hη zero_le_one
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
        (K : ℝ≥0∞) * ‖mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc 0 1) t 1‖ₑ :=
      setLIntegral_mono' measurableSet_Icc hderiv
    _ = K * Manifold.pathELength I4 γ 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]

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

/-! Continuity of the actual chart density gives sharp local comparison
of its weighted measure with the constant density at the chart point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_chartDensity_local_bounds (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (δ : ℝ) (hδ : 0 < δ) :
    ∃ U : Set FourSpace, IsOpen U ∧ z₀.val ∈ U ∧ U ⊆ (chartAt FourSpace c).target ∧
      ∀ A : Set FourSpace, MeasurableSet A → A ⊆ U →
        ENNReal.ofReal ((1 - δ) * chartVolumeDensity g c z₀) * volume A ≤
          (volume.withDensity (fun z => ENNReal.ofReal (chartVolumeDensity g c z))) A ∧
        (volume.withDensity (fun z => ENNReal.ofReal (chartVolumeDensity g c z))) A ≤
          ENNReal.ofReal ((1 + δ) * chartVolumeDensity g c z₀) * volume A := by
  have hρ := chartVolumeDensity_pos g c z₀ z₀.property
  have hc := (chartVolumeDensity_contDiffAt g c z₀ z₀.property).continuousAt
  have ha : ContinuousAt (fun z =>
      |chartVolumeDensity g c z - chartVolumeDensity g c z₀|) z₀.val :=
    (hc.sub continuousAt_const).abs
  have he : ∀ᶠ z in 𝓝 z₀.val,
      |chartVolumeDensity g c z - chartVolumeDensity g c z₀| <
        δ * chartVolumeDensity g c z₀ := by
    apply ha.eventually_lt continuousAt_const
    simp only [sub_self, abs_zero]
    exact mul_pos hδ hρ
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem ((chartAt FourSpace c).open_target.mem_nhds z₀.property) he)
  refine ⟨Metric.ball z₀.val r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    fun z hz => (hsub hz).1, ?_⟩
  intro A hA hAU
  have hb (z : FourSpace) (hz : z ∈ A) :
      (1 - δ) * chartVolumeDensity g c z₀ ≤ chartVolumeDensity g c z ∧
      chartVolumeDensity g c z ≤ (1 + δ) * chartVolumeDensity g c z₀ := by
    have he' : |chartVolumeDensity g c z - chartVolumeDensity g c z₀| <
        δ * chartVolumeDensity g c z₀ := (hsub (hAU hz)).2
    have h := abs_lt.mp he'
    constructor <;> nlinarith [h.1, h.2]
  rw [withDensity_apply _ hA]
  constructor
  · have h := setLIntegral_mono' (μ := (volume : Measure FourSpace)) hA (fun z hz => ENNReal.ofReal_le_ofReal (hb z hz).1)
    simpa only [lintegral_const, Measure.restrict_apply_univ] using h
  · have h := setLIntegral_mono' (μ := (volume : Measure FourSpace)) hA (fun z hz => ENNReal.ofReal_le_ofReal (hb z hz).2)
    simpa only [lintegral_const, Measure.restrict_apply_univ] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The fiber change of coordinates used for kinetic-energy shells.
Lowering a metric-orthonormal frame has determinant equal to the metric
volume density and sends Euclidean radial energy to kinetic energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def coordinateMomentum (g : SmoothMetric M) (c : M) (x : FourSpace)
    (E : Mat4) (v : FourSpace) : FourSpace :=
  WithLp.toLp 2 ((metricInChart g c x * E) *ᵥ WithLp.ofLp v)

theorem coordinateMomentum_det (g : SmoothMetric M) (c : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (E : Mat4) (hE : Eᵀ * metricInChart g c x * E = 1) :
    |(metricInChart g c x * E).det| = chartVolumeDensity g c x := by
  have hp := (metricInChart_posDef g c x hx).det_pos
  have hs : (chartVolumeDensity g c x) ^ 2 = (metricInChart g c x).det :=
    Real.sq_sqrt hp.le
  have he := chartVolumeDensity_mul_frame_det g c x hx E hE
  rw [Matrix.det_mul, abs_mul, abs_of_pos hp, ← hs]
  calc
    _ = chartVolumeDensity g c x * (chartVolumeDensity g c x * |E.det|) := by ring
    _ = _ := by rw [he, mul_one]

/-- At each base point, the lowering map sends Euclidean fiber volume
weighted by the metric density to ordinary cotangent fiber volume. -/
theorem coordinateMomentum_measurePreserving (g : SmoothMetric M) (c : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (E : Mat4) (hE : Eᵀ * metricInChart g c x * E = 1) :
    MeasurePreserving (coordinateMomentum g c x E)
      (ENNReal.ofReal (chartVolumeDensity g c x) • (volume : Measure FourSpace)) volume := by
  let L : FourSpace →ₗ[ℝ] FourSpace :=
    Matrix.toEuclideanLin (metricInChart g c x * E)
  have hd : |L.det| = chartVolumeDensity g c x := by
    rw [show L.det = (metricInChart g c x * E).det from
      LinearMap.det_toLpLin 2 _]
    exact coordinateMomentum_det g c x hx E hE
  have hp := chartVolumeDensity_pos g c x hx
  have hn : L.det ≠ 0 := abs_ne_zero.mp (hd.symm ▸ hp.ne')
  have hL : Continuous L := L.continuous_of_finiteDimensional
  refine ⟨hL.measurable, ?_⟩
  change Measure.map L (ENNReal.ofReal (chartVolumeDensity g c x) • volume) = volume
  rw [Measure.map_smul,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hn, smul_smul]
  have hs : ENNReal.ofReal (chartVolumeDensity g c x) * ENNReal.ofReal |L.det⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul, abs_inv, hd, mul_inv_cancel₀ hp.ne', ENNReal.ofReal_one]
    exact hp.le
  rw [hs, one_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual normalized Weyl tensors and their first three covariant derivatives
have the same chart transition law in every slot. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

theorem unitMatrixTensor_pullback (J H : Mat4) :
    unitMatrixTensor (Jᵀ * H * J) = frameTensor J (unitMatrixTensor H) := by
  funext a
  have ha : a = ![a 0, a 1, a 2, a 3] := by
    funext k
    fin_cases k <;> rfl
  rw [ha, frameTensor_four]
  have h₁ : (∑ p, ∑ q, ∑ r, ∑ s,
      J p (a 0) * J q (a 1) * J r (a 2) * J s (a 3) *
        (H q r * H p s)) =
      (Jᵀ * H * J) (a 1) (a 2) * (Jᵀ * H * J) (a 0) (a 3) := by
    calc
      _ = ∑ p, ∑ q, ∑ r, ∑ s,
          (J p (a 0) * H p s * J s (a 3)) *
            (J q (a 1) * H q r * J r (a 2)) := by
        repeat' (apply Finset.sum_congr rfl; intro _ _)
        ring
      _ = _ := by
        rw [sum_cross_pairs, ← matrix_pairing_expansion,
          ← matrix_pairing_expansion]
        ring
  have h₂ : (∑ p, ∑ q, ∑ r, ∑ s,
      J p (a 0) * J q (a 1) * J r (a 2) * J s (a 3) *
        (H p r * H q s)) =
      (Jᵀ * H * J) (a 0) (a 2) * (Jᵀ * H * J) (a 1) (a 3) := by
    calc
      _ = ∑ p, ∑ q, ∑ r, ∑ s,
          (J p (a 0) * H p r * J r (a 2)) *
            (J q (a 1) * H q s * J s (a 3)) := by
        repeat' (apply Finset.sum_congr rfl; intro _ _)
        ring
      _ = _ := by
        rw [sum_parallel_pairs, ← matrix_pairing_expansion,
          ← matrix_pairing_expansion]
  change _ = ∑ p, ∑ q, ∑ r, ∑ s,
    J p (a 0) * J q (a 1) * J r (a 2) * J s (a 3) *
      (H q r * H p s - H p r * H q s)
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [h₁, h₂]
  rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem unitCurvatureCoordinates_transition (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    unitCurvatureCoordinates g c z = frameTensor (chartTransitionMatrix c d z)
      (unitCurvatureCoordinates g d (chartTransition c d z)) := by
  change unitMatrixTensor _ = frameTensor _ (unitMatrixTensor _)
  rw [metricInChart_transition g c d z hz hx]
  simpa only [Matrix.mul_assoc] using
    unitMatrixTensor_pullback (chartTransitionMatrix c d z)
      (metricInChart g d (chartTransition c d z))

theorem normalizedWeylCoordinates_transition (g : SmoothMetric M) (c d : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    normalizedWeylCoordinates g c z = frameTensor (chartTransitionMatrix c d z)
      (normalizedWeylCoordinates g d (chartTransition c d z)) := by
  funext a
  change curvatureCoordinates g c z a - unitCurvatureCoordinates g c z a =
    frameTensor (chartTransitionMatrix c d z)
      (curvatureCoordinates g d (chartTransition c d z) -
        unitCurvatureCoordinates g d (chartTransition c d z)) a
  rw [frameTensor_sub, curvatureCoordinates_transition g c d z hz hx,
    unitCurvatureCoordinates_transition g c d z hz hx]

/-- Only three derivatives are used below, but retaining the natural number
index makes the local covariance proof a single rank induction. -/
def iteratedWeylDerivative (g : SmoothMetric M) (c : M) :
    (k : ℕ) → FourSpace → CovariantCoordinates (4 + k)
  | 0 => normalizedWeylCoordinates g c
  | k + 1 => covariantDerivative g c (iteratedWeylDerivative g c k)

theorem iteratedWeylDerivative_contDiffAt (g : SmoothMetric M) (c : M)
    (k : ℕ) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (a : Fin (4 + k) → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => iteratedWeylDerivative g c k w a) z := by
  induction k with
  | zero =>
    exact normalizedWeylCoordinates_contDiffAt g c z hz
      (metricInChart_posDef g c z hz).det_pos.ne' a
  | succ k ih =>
    exact covariantDerivative_contDiffAt g c z hz
      (metricInChart_posDef g c z hz).det_pos.ne' _ ih a

theorem iteratedWeylDerivative_transition (g : SmoothMetric M) (c d : M)
    (k : ℕ) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    iteratedWeylDerivative g c k z = frameTensor (chartTransitionMatrix c d z)
      (iteratedWeylDerivative g d k (chartTransition c d z)) := by
  induction k generalizing z with
  | zero => exact normalizedWeylCoordinates_transition g c d z hz hx
  | succ k ih =>
    apply covariantDerivative_chart_transition g c d
      (iteratedWeylDerivative g c k) (iteratedWeylDerivative g d k) z hz hx
    · intro a
      exact (iteratedWeylDerivative_contDiffAt g d k (chartTransition c d z)
        ((chartAt FourSpace d).map_source hx) a).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    · exact (chart_overlap_eventually c d z hz hx).mono
        (fun w hw => ih w hw.1 hw.2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six two-form coefficients carry the actual tensor norm, with the
usual factor of two for repeated alternating pairs. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoFormFrameIsometry (P : Mat4) (hP : Pᵀ * P = 1) : TwoFormFour →ₗᵢ[ℝ] TwoFormFour where
  toLinearMap := twoFormFrameActionLinear P
  norm_map' := twoFormFrameAction_norm P hP

end
end PositiveEinsteinFour.Geometry
end


section

/-! Differentiating a tensor along a coordinate curve and a parallel frame.
The premises are the ordinary velocity and Levi-Civita parallel ODE, rather
than a specialized derivative identity for curvature or scalar fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem hasDerivAt_coordinate_comp {x : ℝ → FourSpace} {v : FourSpace}
    {f : FourSpace → ℝ} {t : ℝ} (hx : HasDerivAt x v t)
    (hf : DifferentiableAt ℝ f (x t)) :
    HasDerivAt (fun s => f (x s)) (∑ r, v r * partialDeriv f r (x t)) t := by
  have h := hf.hasFDerivAt.comp_hasDerivAt t hx
  have hv : v = ∑ r, v r • coordinateVector r :=
    (sum_coordinateVector (fun r => v r)).symm
  have hd : fderiv ℝ f (x t) v = ∑ r, v r * partialDeriv f r (x t) := by
    calc
      _ = fderiv ℝ f (x t) (∑ r, v r • coordinateVector r) :=
        congrArg (fderiv ℝ f (x t)) hv
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, partialDeriv]
  rwa [hd] at h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- A tensor evaluated on a parallel moving frame differentiates to its
covariant derivative in the velocity frame direction. -/
theorem hasDerivAt_parallel_frameTensor {n : ℕ} (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (E : ℝ → Mat4) (T : FourSpace → CovariantCoordinates n)
    (t : ℝ) (k : Fin 4)
    (hx : HasDerivAt x (WithLp.toLp 2 (fun r => E t r k)) t)
    (hE : ∀ i j, HasDerivAt (fun s => E s i j)
      (-((∑ r, E t r k • connectionMatrix g c r (x t)) * E t) i j) t)
    (hT : ∀ a, DifferentiableAt ℝ (fun z => T z a) (x t))
    (a : Fin n → Fin 4) :
    HasDerivAt (fun s => frameTensor (E s) (T (x s)) a)
      (frameTensor (E t) (covariantDerivative g c T (x t)) (Fin.cons k a)) t := by
  let U : Mat4 := ∑ r, E t r k • connectionMatrix g c r (x t)
  let D : CovariantCoordinates n := fun b => ∑ r, E t r k * tensorPartial T r (x t) b
  have htime (b : Fin n → Fin 4) : HasDerivAt (fun s => T (x s) b) (D b) t := by
    exact hasDerivAt_coordinate_comp hx (hT b)
  have hd := hasDerivAt_frameTensor E (fun s => T (x s)) (-(U * E t)) D t hE htime a
  have hconn : E t * (0 : Mat4) = -(U * E t) + U * E t := by simp
  have hv := frameVariation_connection (E t) (-(U * E t)) U 0 hconn (T (x t))
  have hz : tensorSlotAction (0 : Mat4) (frameTensor (E t) (T (x t))) = 0 := by
    funext b
    simp [tensorSlotAction, covariantSlotAction]
  rw [hz] at hv
  have hU : tensorSlotAction U (T (x t)) =
      fun b => ∑ r, E t r k * tensorSlotAction (connectionMatrix g c r (x t)) (T (x t)) b := by
    funext b
    simp only [U, tensorSlotAction_sum_matrix, tensorSlotAction_smul_matrix,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hDU : D - tensorSlotAction U (T (x t)) =
      fun b => ∑ r, E t r k * tensorCovariantDirection (connectionMatrix g c) T r (x t) b := by
    funext b
    simp only [Pi.sub_apply, D, hU, tensorCovariantDirection, mul_sub,
      Finset.sum_sub_distrib]
  have heq : frameVariation (E t) (-(U * E t)) (T (x t)) a + frameTensor (E t) D a =
      frameTensor (E t) (covariantDerivative g c T (x t)) (Fin.cons k a) := by
    have hv' := congrFun hv a
    simp only [Pi.add_apply, Pi.zero_apply] at hv'
    calc
      _ = frameTensor (E t) D a - frameTensor (E t) (tensorSlotAction U (T (x t))) a := by
        linarith only [hv']
      _ = frameTensor (E t) (D - tensorSlotAction U (T (x t))) a :=
        (frameTensor_sub _ _ _ _).symm
      _ = frameTensor (E t) (fun b =>
          ∑ r, E t r k * tensorCovariantDirection (connectionMatrix g c) T r (x t) b) a := by
        rw [hDU]
      _ = ∑ r, E t r k * frameTensor (E t)
          (tensorCovariantDirection (connectionMatrix g c) T r (x t)) a := by
        rw [frameTensor_sum]
        simp only [frameTensor_const_mul]
      _ = _ := by
        rw [frameTensor_cons]
        apply Finset.sum_congr rfl
        intro r _
        congr 1
  rwa [heq] at hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! Jointly continuous orthonormal-frame charts with compact orthogonal
fiber. These charts will give compactness over a compact base. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frame_eq_of_matrix_eq_p2 {g : SmoothMetric M} {x : M}
    (a b : OrthonormalFrame g x) (h : a.matrix = b.matrix) : a = b := by
  cases a with
  | mk A hA =>
    cases b with
    | mk B hB =>
      dsimp only at h
      subst B
      rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Sharp endpoint estimates in coordinates given by a fixed linear
isomorphism. Only the path argument changes; the metric is the actual
Riemannian path metric throughout. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metricEDistance_chart_symm_linear_le (g : SmoothMetric M) (c : M)
    (A : FourSpace →L[ℝ] FourSpace)
    (s : Set FourSpace) (hs : Convex ℝ s) (hst : s ⊆ (chartAt FourSpace c).target)
    (K : ℝ≥0)
    (hK : ∀ z ∈ s, ∀ v : FourSpace,
      metricTangentENorm g ((chartAt FourSpace c).symm z)
        (mfderiv I4 I4 (chartAt FourSpace c).symm z (A v)) ≤ K * ‖v‖ₑ)
    (x y : FourSpace) (hx : A x ∈ s) (hy : A y ∈ s) :
    metricEDistance g ((chartAt FourSpace c).symm (A x)) ((chartAt FourSpace c).symm (A y)) ≤
      K * edist x y := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let η : ℝ →ᴬ[ℝ] FourSpace := ContinuousAffineMap.lineMap (A x) (A y)
  let γ : ℝ → M := (chartAt FourSpace c).symm ∘ η
  have hη : MapsTo η (Icc 0 1) s := by
    rw [mapsTo_iff_image_subset, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap]
    exact hs.segment_subset hx hy
  have hηsmooth : ContMDiff 𝓘(ℝ, ℝ) I4 1 η := by
    rw [contMDiff_iff_contDiff]
    exact η.contDiff
  have hchart : ContMDiffOn I4 I4 1 (chartAt FourSpace c).symm
      (chartAt FourSpace c).target := contMDiffOn_chart_symm
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc 0 1) :=
    hchart.comp hηsmooth.contMDiffOn (fun t ht => hst (hη ht))
  have hstart : γ 0 = (chartAt FourSpace c).symm (A x) := by
    simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  have hend : γ 1 = (chartAt FourSpace c).symm (A y) := by
    simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc 0 1) t 1‖ₑ ≤ K * ‖y - x‖ₑ := by
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc 0 1) t := by
      rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
    have hc : MDifferentiableAt I4 I4 (chartAt FourSpace c).symm (η t) :=
      (contMDiffAt_symm_of_mem_maximalAtlas
        (n := ∞) (IsManifold.chart_mem_maximalAtlas c) (hst (hη ht))).mdifferentiableAt (by simp)
    have hd : mfderivWithin 𝓘(ℝ, ℝ) I4 η (Icc 0 1) t 1 = A (y - x) := by
      have hd' : (fderivWithin ℝ (fun s : ℝ => η s) (Icc 0 1) t) 1 = A (y - x) := by
        rw [fderivWithin_derivWithin]
        simpa only [η, ContinuousAffineMap.coe_lineMap_eq, map_sub] using
          (AffineMap.hasDerivWithinAt_lineMap (a := A x) (b := A y)).derivWithin
            (uniqueDiffOn_Icc zero_lt_one t ht)
      simpa only [mfderivWithin_eq_fderivWithin] using! hd'
    have he := mfderiv_comp_mfderivWithin t hc
      (hηsmooth.mdifferentiable (by simp) t).mdifferentiableWithinAt hu
    change ‖mfderivWithin 𝓘(ℝ, ℝ) I4
      ((chartAt FourSpace c).symm ∘ η) (Icc 0 1) t 1‖ₑ ≤ _
    rw [he, ContinuousLinearMap.comp_apply, hd]
    exact hK (η t) (hη ht) (y - x)
  change Manifold.riemannianEDist I4 _ _ ≤ _
  calc
    _ ≤ Manifold.pathELength I4 γ 0 1 :=
      Manifold.riemannianEDist_le_pathELength hγ hstart hend zero_le_one
    _ = ∫⁻ t in Icc (0 : ℝ) 1,
        ‖mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc 0 1) t 1‖ₑ :=
      Manifold.pathELength_eq_lintegral_mfderivWithin_Icc
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, (K : ℝ≥0∞) * ‖y - x‖ₑ :=
      setLIntegral_mono' measurableSet_Icc hspeed
    _ = K * edist x y := by
      simp only [lintegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
        Measure.restrict_apply_univ, mul_one, edist_eq_enorm_sub, enorm_sub_rev]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual invariant probability on the oriented orthogonal matrix
fiber. This is the compact fiber measure for the frame-bundle construction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory

noncomputable section

theorem isCompact_orientedOrthogonalFour :
    IsCompact (Matrix.specialOrthogonalGroup (Fin 4) ℝ : Set Mat4) := by
  have he : (Matrix.specialOrthogonalGroup (Fin 4) ℝ : Set Mat4) =
      {S : Mat4 | Sᵀ * S = 1} ∩ {S : Mat4 | S.det = 1} := by
    ext S
    change S ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ ↔ Sᵀ * S = 1 ∧ S.det = 1
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  rw [he]
  exact isCompact_orthogonalFour.inter_right (isClosed_eq (by fun_prop) continuous_const)

instance instCompactSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFour : CompactSpace OrientedOrthogonalFour :=
  isCompact_iff_compactSpace.mp isCompact_orientedOrthogonalFour

def orientedFrameHaar : Measure OrientedOrthogonalFour := Measure.haarMeasure ⊤

instance instIsProbabilityMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFourOrientedFrameHaar : IsProbabilityMeasure orientedFrameHaar := by
  constructor
  exact Measure.haarMeasure_self (K₀ := ⊤)

instance instIsHaarMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFourOrientedFrameHaar : Measure.IsHaarMeasure orientedFrameHaar :=
  Measure.isHaarMeasure_haarMeasure ⊤

theorem orientedFrameHaar_left (Q : OrientedOrthogonalFour) :
    MeasurePreserving (fun S => Q * S) orientedFrameHaar orientedFrameHaar :=
  measurePreserving_mul_left orientedFrameHaar Q

theorem orientedFrameHaar_right (Q : OrientedOrthogonalFour) :
    MeasurePreserving (fun S => S * Q) orientedFrameHaar orientedFrameHaar := by
  refine ⟨by fun_prop, ?_⟩
  haveI : IsProbabilityMeasure (Measure.map (fun S => S * Q) orientedFrameHaar) :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable fun S => S * Q).aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure
    (Measure.map (fun S => S * Q) orientedFrameHaar) orientedFrameHaar

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

structure OrientedNormRegularity (o : FrameOrientation g) : Prop where
  plusSquareSmooth : ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun c => plusNorm o c ^ 2)
  minusSquareSmooth : ContMDiff I4 𝓘(ℝ, ℝ) ∞ (fun c => minusNorm o c ^ 2)

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

theorem OrthonormalFrame.changeMatrix_self {c : M} (e : OrthonormalFrame g c) :
    e.changeMatrix e = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr e.det_ne_zero)

theorem OrthonormalFrame.changeMatrix_comp {c : M} (e f k : OrthonormalFrame g c) :
    e.changeMatrix f * f.changeMatrix k = e.changeMatrix k := by
  unfold OrthonormalFrame.changeMatrix
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc f.matrix,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr f.det_ne_zero), Matrix.one_mul]

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

def twoFormDerivativeRows (B : Fin 4 → TwoFormFour) : CovariantCoordinates 3 :=
  fun v => twoFormTensor (B (v 0)) (fun i => v i.succ)

theorem twoFormDerivativeRows_cons (B : Fin 4 → TwoFormFour)
    (i : Fin 4) (v : Fin 2 → Fin 4) :
    twoFormDerivativeRows B (Fin.cons i v) = twoFormTensor (B i) v := rfl

theorem twoFormDerivativeRows_norm (B : Fin 4 → TwoFormFour) :
    frameTensorSquareNorm (twoFormDerivativeRows B) = 2 * ∑ i, ‖B i‖ ^ 2 := by
  unfold frameTensorSquareNorm frameTensorPairing
  rw [sum_tensor_indices_cons]
  simp only [twoFormDerivativeRows_cons]
  change (∑ i, frameTensorSquareNorm (twoFormTensor (B i))) = _
  simp_rw [twoFormTensor_norm]
  exact (Finset.mul_sum _ _ _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual continuous right action of orthogonal matrices on frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frame_ext_matrix {g : SmoothMetric M} {x : M}
    (e f : OrthonormalFrame g x) (h : e.matrix = f.matrix) : e = f := by
  cases e with
  | mk A hA =>
    cases f with
    | mk B hB =>
      dsimp only at h
      subst B
      rfl

def OrthonormalFrame.rotate {g : SmoothMetric M} {x : M}
    (e : OrthonormalFrame g x) (Q : OrthogonalFour) : OrthonormalFrame g x where
  matrix := e.matrix * Q.val
  orthonormal := by
    calc
      (e.matrix * Q.val)ᵀ * chartMetric g x * (e.matrix * Q.val) =
          Q.valᵀ * (e.matrixᵀ * chartMetric g x * e.matrix) * Q.val := by
        rw [Matrix.transpose_mul]
        noncomm_ring
      _ = 1 := by rw [e.orthonormal, mul_one, Q.property]

def FrameBundle.rotate {g : SmoothMetric M} (e : FrameBundle g)
    (Q : OrthogonalFour) : FrameBundle g := ⟨e.base, e.frame.rotate Q⟩

theorem OrthonormalFrame.rotate_vector {g : SmoothMetric M} {x : M}
    (e : OrthonormalFrame g x) (Q : OrthogonalFour) (j : Fin 4) :
    (e.rotate Q).vector j = ∑ k, Q.val k j • e.vector k := by
  ext i
  simp only [OrthonormalFrame.vector, OrthonormalFrame.rotate, Matrix.mul_apply,
    WithLp.ofLp_sum, PiLp.smul_apply, smul_eq_mul, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem continuous_orientedToOrthogonal : Continuous orientedToOrthogonal :=
  continuous_subtype_val.subtype_mk _

theorem trivialization_sum_vectors
    (V : Trivialization FourSpace (Bundle.TotalSpace.proj : TangentBundle I4 M → M))
    [V.IsLinear ℝ] (x : M) (hx : x ∈ V.baseSet) (a : Fin 4 → ℝ)
    (v : Fin 4 → TangentSpace I4 x) :
    (V (⟨x, ∑ k, a k • v k⟩ : TangentBundle I4 M)).2 =
      ∑ k, a k • (V (⟨x, v k⟩ : TangentBundle I4 M)).2 := by
  let L : TangentSpace I4 x →ₗ[ℝ] FourSpace := V.linearMapAt ℝ x
  have h := map_sum L (fun k : Fin 4 => a k • v k) Finset.univ
  simpa only [map_smul, L, V.coe_linearMapAt_of_mem (R := ℝ) hx] using h

theorem continuous_frameRotate (g : SmoothMetric M) :
    Continuous (fun p : FrameBundle g × OrthogonalFour => p.1.rotate p.2) := by
  apply continuous_induced_rng.mpr
  apply continuous_iff_continuousAt.mpr
  intro p
  let V := trivializationAt FourSpace (TangentSpace I4 : M → Type _) p.1.base
  have hbase : Continuous (fun q : FrameBundle g × OrthogonalFour => q.1.base) :=
    (continuous_frameBase g).comp continuous_fst
  have hn : ∀ᶠ q : FrameBundle g × OrthogonalFour in 𝓝 p, q.1.base ∈ V.baseSet :=
    hbase.continuousAt.eventually (V.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt FourSpace (TangentSpace I4) p.1.base))
  have hv (k : Fin 4) : ContinuousAt
      (fun q : FrameBundle g × OrthogonalFour =>
        (V (⟨q.1.base, q.1.frame.vector k⟩ : TangentBundle I4 M)).2) p := by
    have hvec : Continuous (fun q : FrameBundle g × OrthogonalFour =>
        (⟨q.1.base, q.1.frame.vector k⟩ : TangentBundle I4 M)) :=
      ((continuous_apply k).comp (continuous_snd.comp (continuous_frameRealization g))).comp
        continuous_fst
    exact continuous_snd.continuousAt.comp
      ((V.toOpenPartialHomeomorph.continuousAt (V.mem_source.mpr
        (mem_baseSet_trivializationAt FourSpace (TangentSpace I4) p.1.base))).comp
          hvec.continuousAt)
  have hout (j : Fin 4) : ContinuousAt
      (fun q : FrameBundle g × OrthogonalFour =>
        (⟨q.1.base, (q.1.frame.rotate q.2).vector j⟩ : TangentBundle I4 M)) p := by
    apply (V.toOpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_left
      (by exact hn)).mpr
    have hsum : ContinuousAt (fun q : FrameBundle g × OrthogonalFour =>
        ∑ k, q.2.val k j •
          (V (⟨q.1.base, q.1.frame.vector k⟩ : TangentBundle I4 M)).2) p := by
      apply tendsto_finsetSum
      intro k _
      exact (((continuous_apply j).comp (continuous_apply k)).comp
        (continuous_subtype_val.comp continuous_snd)).continuousAt.smul (hv k)
    apply (hbase.continuousAt.prodMk hsum).congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    apply Prod.ext
    · exact V.coe_fst' (x := (⟨q.1.base, (q.1.frame.rotate q.2).vector j⟩ :
        TangentBundle I4 M)) hq
    · change (V (⟨q.1.base, (q.1.frame.rotate q.2).vector j⟩ :
        TangentBundle I4 M)).2 = _
      rw [OrthonormalFrame.rotate_vector]
      exact trivialization_sum_vectors V q.1.base hq
        (fun k => q.2.val k j) (fun k => q.1.frame.vector k)

  exact hbase.continuousAt.prodMk (continuousAt_pi.mpr hout)

theorem frameRotate_oriented_positive {g : SmoothMetric M} (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (Q : OrientedOrthogonalFour) :
    e.rotate (orientedToOrthogonal Q) ∈ o.positive := by
  apply (o.compatible e.base e.frame _ he).mpr
  change 0 < e.frame.matrix.det * (e.frame.matrix * Q.val).det
  rw [Matrix.det_mul, (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).2, mul_one]
  exact mul_self_pos.mpr e.frame.det_ne_zero

theorem frameRotate_one {g : SmoothMetric M} (e : FrameBundle g) :
    e.rotate (orientedToOrthogonal 1) = e := by
  cases e with
  | mk x f =>
    apply congrArg (FrameBundle.mk x)
    apply frame_ext_matrix
    exact Matrix.mul_one _

theorem frameRotate_mul {g : SmoothMetric M} (e : FrameBundle g)
    (P Q : OrientedOrthogonalFour) :
    (e.rotate (orientedToOrthogonal P)).rotate (orientedToOrthogonal Q) =
      e.rotate (orientedToOrthogonal (P * Q)) := by
  cases e with
  | mk x f =>
    apply congrArg (FrameBundle.mk x)
    apply frame_ext_matrix
    exact Matrix.mul_assoc _ _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Sharp endpoint estimates in coordinates given by a fixed linear
isomorphism. Only the path argument changes; the metric is the actual
Riemannian path metric throughout. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M]

theorem exists_linear_chart_lipschitz_of_bound (g : SmoothMetric M) (c x₀ : M)
    (A : FourSpace →L[ℝ] FourSpace) (U : Set M) (hU : U ∈ 𝓝 x₀)
    (hsource : U ⊆ (chartAt FourSpace c).source) (K : ℝ≥0) (hKpos : 0 < K)
    (hK : ∀ x ∈ U, ∀ v : TangentSpace I4 x,
      ‖A (mfderiv I4 I4 (chartAt FourSpace c) x v)‖ₑ ≤
        K * metricTangentENorm g x v) :
    ∃ s ∈ 𝓝 x₀, s ⊆ U ∧ ∀ x ∈ s, ∀ y ∈ s,
      edist (A (chartAt FourSpace c x)) (A (chartAt FourSpace c y)) ≤
        K * metricEDistance g x y := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  obtain ⟨ε, hε, hεU⟩ := setOfPred_riemannianEDist_lt_subset_nhds I4 hU
  let δ : ℝ≥0 := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsum : (δ : ℝ≥0∞) + δ + δ + δ = ε := by
    exact_mod_cast (show δ + δ + δ + δ = ε by dsimp [δ]; ring)
  let s : Set M := {x | edist x₀ x < (δ : ℝ≥0∞)}
  have hs : s ∈ 𝓝 x₀ := by
    have hopen : IsOpen s := isOpen_lt (continuous_const.edist continuous_id) continuous_const
    exact hopen.mem_nhds (by simpa [s] using hδ)
  have hsU : s ⊆ U := by
    intro x hx
    apply hεU
    change edist x₀ x < (ε : ℝ≥0∞)
    exact hx.trans_le (by
      calc
        (δ : ℝ≥0∞) ≤ δ + δ + δ + δ := by
          simp only [add_assoc]
          exact le_self_add
        _ = ε := hsum)
  refine ⟨s, hs, hsU, ?_⟩
  intro x hx y hy
  have hxy : edist x y < (δ : ℝ≥0∞) + δ + δ := by
    calc
      edist x y ≤ edist x₀ x + edist x₀ y := edist_triangle_left _ _ _
      _ < δ + δ := ENNReal.add_lt_add hx hy
      _ ≤ δ + δ + δ := le_add_right le_rfl
  have hbound (r : {r : ℝ≥0∞ // edist x y < r ∧ r < (δ : ℝ≥0∞) + δ + δ}) :
      edist (A (chartAt FourSpace c x)) (A (chartAt FourSpace c y)) ≤ K * (r : ℝ≥0∞) := by
    obtain ⟨γ, hγx, hγy, hγ, hlen, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt r.property.1 zero_lt_one
    have hγU (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ U := by
      apply hεU
      change edist x₀ (γ t) < (ε : ℝ≥0∞)
      calc
        edist x₀ (γ t) ≤ edist x₀ x + edist x (γ t) := edist_triangle _ _ _
        _ ≤ edist x₀ x + Manifold.pathELength I4 γ 0 t := by
          gcongr
          exact Manifold.riemannianEDist_le_pathELength hγ.contMDiffOn hγx rfl ht.1
        _ ≤ edist x₀ x + Manifold.pathELength I4 γ 0 1 := by
          gcongr
          exact ht.2
        _ < δ + (r : ℝ≥0∞) := ENNReal.add_lt_add hx hlen
        _ < δ + (δ + δ + δ) := ENNReal.add_lt_add_left ENNReal.coe_ne_top r.property.2
        _ = ε := by simpa only [add_assoc] using hsum
    have hchart := linear_chart_edist_le_pathELength g c A γ hγ
      (fun t ht => hsource (hγU t ht)) K (fun t ht v => hK _ (hγU t ht) v)
    rw [hγx, hγy] at hchart
    exact hchart.trans (mul_le_mul_right hlen.le _)
  change edist (A (chartAt FourSpace c x)) (A (chartAt FourSpace c y)) ≤ K * edist x y
  rw [← iInf_open_interval_p1 (edist x y) ((δ : ℝ≥0∞) + δ + δ) hxy,
    ENNReal.mul_iInf_of_ne (by exact_mod_cast hKpos.ne') ENNReal.coe_ne_top]
  exact le_iInf hbound

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth scalar functions and their first three actual covariant derivatives
are continuous on the intrinsic orthonormal-frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_field_contDiffAt {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (v : Fin 0 → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => scalarCoordinates a c w v) z := by
  exact (ha.contMDiffAt.comp z
    (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) hz)).contDiffAt

omit [IsManifold I4 ∞ M] in
theorem scalarCoordinates_transition (a : M → ℝ) (c d : M) (z : FourSpace)
    (_hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    scalarCoordinates a c z = frameTensor (chartTransitionMatrix c d z)
      (scalarCoordinates a d (chartTransition c d z)) := by
  funext v
  rw [frameTensor_zero]
  change a ((chartAt FourSpace c).symm z) =
    a ((chartAt FourSpace d).symm (chartAt FourSpace d ((chartAt FourSpace c).symm z)))
  rw [(chartAt FourSpace d).left_inv hx]

def iteratedScalarDerivative (g : SmoothMetric M) (a : M → ℝ) (c : M) :
    (k : ℕ) → FourSpace → CovariantCoordinates k
  | 0 => scalarCoordinates a c
  | k + 1 => covariantDerivative g c (iteratedScalarDerivative g a c k)

theorem iteratedScalarDerivative_contDiffAt (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (c : M) (k : ℕ) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (v : Fin k → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => iteratedScalarDerivative g a c k w v) z := by
  induction k with
  | zero => exact scalar_field_contDiffAt ha c z hz v
  | succ k ih =>
    exact covariantDerivative_contDiffAt g c z hz
      (metricInChart_posDef g c z hz).det_pos.ne' _ ih v

theorem iteratedScalarDerivative_transition (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) (c d : M) (k : ℕ) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    iteratedScalarDerivative g a c k z = frameTensor (chartTransitionMatrix c d z)
      (iteratedScalarDerivative g a d k (chartTransition c d z)) := by
  induction k generalizing z with
  | zero => exact scalarCoordinates_transition a c d z hz hx
  | succ k ih =>
    apply covariantDerivative_chart_transition g c d
      (iteratedScalarDerivative g a c k) (iteratedScalarDerivative g a d k) z hz hx
    · intro v
      exact (iteratedScalarDerivative_contDiffAt g ha d k (chartTransition c d z)
        ((chartAt FourSpace d).map_source hx) v).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    · exact (chart_overlap_eventually c d z hz hx).mono
        (fun w hw => ih w hw.1 hw.2)

theorem actual_scalarValue_continuous (g : SmoothMetric M) {a : M → ℝ}
    (ha : ContMDiff I4 𝓘(ℝ, ℝ) ∞ a) :
    Continuous (fun e : FrameBundle g => a e.base) :=
  ha.continuous.comp (continuous_frameBase g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The concrete oriented orthogonal action on the unit directions, and a
continuous oriented orthogonal completion of every direction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular
open scoped BigOperators

noncomputable section

theorem orthogonalEuclidean_norm (P : Mat4) (hP : Pᵀ * P = 1)
    (x : FourSpace) : ‖Matrix.toEuclideanLin P x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have h : (P *ᵥ WithLp.ofLp x) ⬝ᵥ (P *ᵥ WithLp.ofLp x) =
      WithLp.ofLp x ⬝ᵥ WithLp.ofLp x := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, pow_two] using h

def orthogonalEuclideanIsometry (P : Mat4) (hP : Pᵀ * P = 1) :
    FourSpace ≃ₗᵢ[ℝ] FourSpace where
  toLinearEquiv :=
    { Matrix.toEuclideanLin P with
      invFun := Matrix.toEuclideanLin Pᵀ
      left_inv := by
        intro x
        change (Matrix.toLpLin 2 2 Pᵀ) ((Matrix.toLpLin 2 2 P) x) = x
        rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hP, Matrix.toLpLin_one]
        rfl
      right_inv := by
        intro x
        change (Matrix.toLpLin 2 2 P) ((Matrix.toLpLin 2 2 Pᵀ) x) = x
        rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
          mul_eq_one_comm.mp hP, Matrix.toLpLin_one]
        rfl }
  norm_map' := orthogonalEuclidean_norm P hP

def orthogonalDirection (P : Mat4) (hP : Pᵀ * P = 1) : Directions ≃ᵢ Directions :=
  directionIsometry (orthogonalEuclideanIsometry P hP)

def orientedDirection (P : OrientedOrthogonalFour) : Directions ≃ᵢ Directions :=
  orthogonalDirection P.val (by
    have h := (Matrix.mem_specialOrthogonalGroup_iff.mp P.property).1
    rwa [Matrix.mem_orthogonalGroup_iff'] at h)

theorem directionFrameMatrix_det (q : Directions) : (directionFrameMatrix q).det = 1 := by
  have h : (directionFrameMatrix q).det = (∑ k : Fin 4, q.val k ^ 2) ^ 2 := by
    rw [Matrix.det_succ_row_zero]
    simp only [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply]
    simp [directionFrameMatrix, Fin.succAbove, Fin.lt_def]
    ring
  rw [h, direction_sum_sq, one_pow]

def directionOrientedMatrix (q : Directions) : OrientedOrthogonalFour :=
  ⟨directionFrameMatrix q, Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨by rw [Matrix.mem_orthogonalGroup_iff']; exact directionFrameMatrix_orthogonal q,
      directionFrameMatrix_det q⟩⟩

theorem continuous_directionOrientedMatrix : Continuous directionOrientedMatrix := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j
  all_goals
    first
    | change Continuous (fun q : Directions => q.val _)
    | change Continuous (fun q : Directions => -q.val _)
  all_goals fun_prop

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

theorem frame_matrix_ext (e f : OrthonormalFrame g c)
    (h : e.matrix = f.matrix) : e = f := by
  cases e with
  | mk A hA =>
    cases f with
    | mk B hB =>
      dsimp only at h
      subst B
      rfl

def orientedFrameMap (e : OrthonormalFrame g c) (Q : OrientedOrthogonalFour) :
    FrameBundle g := (⟨c, e⟩ : FrameBundle g).rotate (orientedToOrthogonal Q)

theorem continuous_orientedFrameMap (e : OrthonormalFrame g c) :
    Continuous (orientedFrameMap e) :=
  (continuous_frameRotate g).comp (continuous_const.prodMk continuous_orientedToOrthogonal)

def orientedFiberMeasure (e : OrthonormalFrame g c) : Measure (FrameBundle g) :=
  Measure.map (orientedFrameMap e) orientedFrameHaar

def orientedFrameChange (e f : OrthonormalFrame g c)
    (h : 0 < e.matrix.det * f.matrix.det) : OrientedOrthogonalFour :=
  ⟨e.changeMatrix f, Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨by rw [Matrix.mem_orthogonalGroup_iff']; exact e.changeMatrix_orthogonal f,
      e.changeMatrix_det_one f h⟩⟩

theorem orientedFrameMap_change (e f : OrthonormalFrame g c)
    (h : 0 < e.matrix.det * f.matrix.det) :
    orientedFrameMap e (orientedFrameChange e f h) = (⟨c, f⟩ : FrameBundle g) := by
  have he : e.rotate (orientedToOrthogonal (orientedFrameChange e f h)) = f := by
    apply frame_matrix_ext
    exact e.mul_changeMatrix f
  exact congrArg (FrameBundle.mk c) he

theorem orientedFrameMap_mul (e : OrthonormalFrame g c)
    (P Q : OrientedOrthogonalFour) :
    orientedFrameMap e (P * Q) =
      (orientedFrameMap e P).rotate (orientedToOrthogonal Q) :=
  (frameRotate_mul (⟨c, e⟩ : FrameBundle g) P Q).symm

theorem orientedFiberMeasure_eq (e f : OrthonormalFrame g c)
    (h : 0 < e.matrix.det * f.matrix.det) :
    orientedFiberMeasure e = orientedFiberMeasure f := by
  let P := orientedFrameChange e f h
  have he : orientedFrameMap f = orientedFrameMap e ∘ (fun Q => P * Q) := by
    funext Q
    rw [Function.comp_apply, orientedFrameMap_mul, orientedFrameMap_change]
    rfl
  rw [orientedFiberMeasure, orientedFiberMeasure, he,
    ← Measure.map_map (continuous_orientedFrameMap e).measurable (by fun_prop),
    (orientedFrameHaar_left P).map_eq]

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

local instance normalizedVolumeProbability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual Weyl and scalar parallel differentiation from the coordinate
velocity and Levi-Civita frame ODE. No curvature derivative is an input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix TraceHessian
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.parallelFlowNormedRing
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.parallelFlowNormedSpace
local instance parallelFlowNormedAlgebra_r57b6aa_1 : NormedAlgebra ℝ Mat3 := Matrix.frobeniusNormedAlgebra
theorem hasDerivAt_blockCoordinates {T : ℝ → CovariantCoordinates 4}
    {D : CovariantCoordinates 4} {t : ℝ}
    (h : ∀ a, HasDerivAt (fun s => T s a) (D a) t) (Q : Fin 3 → Mat4) :
    HasDerivAt (fun s => blockCoordinates (T s) Q) (blockCoordinates D Q) t := by
  exact ((blockCoordinatesLinear Q).toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_pi.mpr h)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local horizontal frame vector field is smooth and preserves the
metric Gram matrix. The defining equations are ordinary finite-dimensional
ODEs in one coordinate chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem parallelFrame_metric_rate (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (v : Fin 4 → ℝ) :
    (∑ r, v r • matrixPartial (metricInChart g c) r z) =
      (∑ r, v r • connectionMatrix g c r z)ᵀ * metricInChart g c z +
        metricInChart g c z * (∑ r, v r • connectionMatrix g c r z) := by
  have hdet : IsUnit (metricInChart g c z).det :=
    isUnit_iff_ne_zero.mpr (metricInChart_posDef g c z hz).det_pos.ne'
  simp_rw [matrixPartial_metric g c z hdet]
  simp only [smul_add, Finset.sum_add_distrib, Matrix.transpose_sum,
    Matrix.transpose_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm]

/-- The horizontal ODE preserves all inner products of frame columns. -/
theorem hasDerivAt_parallelGram_zero (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (E : ℝ → Mat4) (t : ℝ) (k : Fin 4)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x (WithLp.toLp 2 (fun r => E t r k)) t)
    (hE : ∀ i j, HasDerivAt (fun s => E s i j)
      (-((∑ r, E t r k • connectionMatrix g c r (x t)) * E t) i j) t) :
    HasDerivAt (fun s => (E s)ᵀ * metricInChart g c (x s) * E s) 0 t := by
  let G (s : ℝ) : Mat4 := metricInChart g c (x s)
  let U : Mat4 := ∑ r, E t r k • connectionMatrix g c r (x t)
  let P : Mat4 := -(U * E t)
  let D : Mat4 := Uᵀ * G t + G t * U
  have hG (i j : Fin 4) : HasDerivAt (fun s => G s i j) (D i j) t := by
    have hd := hasDerivAt_coordinate_comp hx
      ((metricInChart_contDiffAt g c (x t) hz i j).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    have hr := congrFun (congrFun (parallelFrame_metric_rate g c (x t) hz
      (fun r => E t r k)) i) j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, matrixPartial] at hr
    change (∑ r, E t r k * partialDeriv (fun z => metricInChart g c z i j) r (x t)) =
      D i j at hr
    rwa [hr] at hd
  have hP (i j : Fin 4) : HasDerivAt (fun s => E s i j) (P i j) t := hE i j
  have hTG (i j : Fin 4) := hasDerivAt_matrix_mul_entry
    (fun s => (E s)ᵀ) G Pᵀ D t (fun a b => hP b a) hG i j
  have hprod (i j : Fin 4) := hasDerivAt_matrix_mul_entry
    (fun s => (E s)ᵀ * G s) E (Pᵀ * G t + (E t)ᵀ * D) P t hTG hP i j
  have hzero : (Pᵀ * G t + (E t)ᵀ * D) * E t + (E t)ᵀ * G t * P = 0 := by
    dsimp only [P, D]
    rw [Matrix.add_mul]
    exact parallelGram_rate_zero (G t) U (E t)
  rw [hzero] at hprod
  exact hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (hprod i))

/-- Along a local solution, one orthonormal initial frame remains
orthonormal throughout its open interval of definition. -/
theorem parallelGram_eq_on_interval (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (E : ℝ → Mat4) (k : Fin 4) (a b s t : ℝ)
    (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b)
    (hz : ∀ r ∈ Set.Ioo a b, x r ∈ (chartAt FourSpace c).target)
    (hx : ∀ r ∈ Set.Ioo a b,
      HasDerivAt x (WithLp.toLp 2 (fun i => E r i k)) r)
    (hE : ∀ r ∈ Set.Ioo a b, ∀ i j, HasDerivAt (fun u => E u i j)
      (-((∑ l, E r l k • connectionMatrix g c l (x r)) * E r) i j) r) :
    (E s)ᵀ * metricInChart g c (x s) * E s =
      (E t)ᵀ * metricInChart g c (x t) * E t := by
  have hd (r : ℝ) (hr : r ∈ Set.Ioo a b) :=
    hasDerivAt_parallelGram_zero g c x E r k (hz r hr) (hx r hr) (hE r hr)
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hd r hr).deriv) hs ht

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

theorem scalarLaplacian_eq_inverse_trace (g : SmoothMetric M) (a : M → ℝ)
    (e : FrameBundle g) :
    scalarLaplacian g a e = ∑ i, ∑ j, (chartMetric g e.base)⁻¹ i j *
      iteratedScalarDerivative g a e.base 2 (chartAt FourSpace e.base e.base) ![i, j] := by
  change (∑ i, frameTensor e.frame.matrix
    (iteratedScalarDerivative g a e.base 2 (chartAt FourSpace e.base e.base)) ![i, i]) = _
  rw [frameTensor_trace_two, e.frame.matrix_mul_transpose]

def scalarLaplacianBase (g : SmoothMetric M) (a : M → ℝ) (x : M) : ℝ :=
  scalarLaplacian g a (frameAt g x)

theorem scalarLaplacian_eq_base (g : SmoothMetric M) (a : M → ℝ)
    (e : FrameBundle g) : scalarLaplacian g a e = scalarLaplacianBase g a e.base := by
  rw [scalarLaplacianBase, scalarLaplacian_eq_inverse_trace,
    scalarLaplacian_eq_inverse_trace]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Haar-to-sphere averaging through the explicit quaternionic completion.
Only integrability on the Haar fiber is required; spherical measurability
is not assumed as a separate input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular MeasureTheory Set
open scoped BigOperators

noncomputable section

local instance instIsProbabilityMeasureDirectionsSphereMeasure : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability

/-- Multiplication by a sphere-dependent orthogonal completion preserves
the Haar marginal. -/
theorem sphereCompletion_haar_preserving :
    MeasurePreserving
      (fun p : Directions × OrientedOrthogonalFour => p.2 * directionOrientedMatrix p.1)
      (sphereMeasure.prod orientedFrameHaar) orientedFrameHaar := by
  have hskew : MeasurePreserving
      (fun p : Directions × OrientedOrthogonalFour =>
        (p.1, p.2 * directionOrientedMatrix p.1))
      (sphereMeasure.prod orientedFrameHaar) (sphereMeasure.prod orientedFrameHaar) := by
    refine (MeasurePreserving.id sphereMeasure).skew_product
      (g := fun q P => P * directionOrientedMatrix q) ?_ ?_
    · exact measurable_snd.mul (continuous_directionOrientedMatrix.measurable.comp measurable_fst)
    · exact Filter.Eventually.of_forall (fun q => (orientedFrameHaar_right
        (directionOrientedMatrix q)).map_eq)
  exact measurePreserving_snd.comp hskew

/-- An integrable Haar-fiber function whose rotated values depend only on
the corresponding unit direction has the spherical average. -/
theorem haar_integral_eq_sphere_of_rotation
    (f : OrientedOrthogonalFour → ℝ) (G : Directions → ℝ)
    (hf : Integrable f orientedFrameHaar)
    (heq : ∀ P q, f (P * directionOrientedMatrix q) =
      G (orientedDirection P q)) :
    (∫ P, f P ∂orientedFrameHaar) = ∫ q, G q ∂sphereMeasure := by
  let R : Directions × OrientedOrthogonalFour → OrientedOrthogonalFour :=
    fun p => p.2 * directionOrientedMatrix p.1
  have hR : MeasurePreserving R (sphereMeasure.prod orientedFrameHaar) orientedFrameHaar :=
    sphereCompletion_haar_preserving
  have hi : Integrable (fun p => f (R p)) (sphereMeasure.prod orientedFrameHaar) :=
    hR.integrable_comp_of_integrable hf
  have hmap : (∫ P, f P ∂orientedFrameHaar) =
      ∫ p, f (R p) ∂(sphereMeasure.prod orientedFrameHaar) := by
    calc
      _ = ∫ P, f P ∂Measure.map R (sphereMeasure.prod orientedFrameHaar) := by
        rw [hR.map_eq]
      _ = _ := integral_map hR.measurable.aemeasurable (by
        simpa only [hR.map_eq] using hf.aestronglyMeasurable)
  rw [hmap, integral_prod_symm _ hi]
  have hinner (P : OrientedOrthogonalFour) :
      (∫ q, f (R (q, P)) ∂sphereMeasure) = ∫ q, G q ∂sphereMeasure := by
    simp_rw [R, heq P]
    exact sphereIntegral_isometry _ G
  simp_rw [hinner]
  simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! In four dimensions, the exterior energy of a two-form jet is the
codifferential energy of its Hodge dual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoForm_rows_exterior_hodge (A : Fin 4 → TwoFormFour) :
    (1 / 6 : ℝ) * (∑ i, ∑ j, ∑ k,
      twoFormExteriorComponent (fun p q r => twoFormMatrix (A p) q r) i j k ^ 2) =
      ∑ k, twoFormCodiffComponent
        (fun p q r => twoFormMatrix (twoFormHodge (A p)) q r) k ^ 2 := by
  simp [twoFormExteriorComponent, twoFormCodiffComponent, Fin.sum_univ_succ,
    twoFormMatrix, twoFormHodge, twoFormHodgeLinear]
  ring

theorem twoForm_rows_deRham_hodge (A : Fin 4 → TwoFormFour) :
    twoFormDeRhamQuadratic (fun p q r => twoFormMatrix (A p) q r) =
      (∑ k, twoFormCodiffComponent (fun p q r => twoFormMatrix (A p) q r) k ^ 2) +
        ∑ k, twoFormCodiffComponent
          (fun p q r => twoFormMatrix (twoFormHodge (A p)) q r) k ^ 2 := by
  unfold twoFormDeRhamQuadratic
  rw [twoForm_rows_exterior_hodge, add_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The connection trace is the logarithmic derivative of the actual
metric volume density. This is the local identity used in the parallel
flow's volume calculation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem hasDerivAt_chartVolumeDensity (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (v : Fin 4 → ℝ) (t : ℝ)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x (WithLp.toLp 2 v) t) :
    HasDerivAt (fun s => chartVolumeDensity g c (x s))
      ((∑ r, v r • connectionMatrix g c r (x t)).trace *
        chartVolumeDensity g c (x t)) t := by
  let G : Mat4 := metricInChart g c (x t)
  let U : Mat4 := ∑ r, v r • connectionMatrix g c r (x t)
  have hG (i j : Fin 4) : HasDerivAt (fun s => metricInChart g c (x s) i j)
      ((Uᵀ * G + G * U) i j) t := by
    have hd := hasDerivAt_coordinate_comp hx
      ((metricInChart_contDiffAt g c (x t) hz i j).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    have hr := congrFun (congrFun (parallelFrame_metric_rate g c (x t) hz v) i) j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, matrixPartial] at hr
    change (∑ r, v r * partialDeriv (fun z => metricInChart g c z i j) r (x t)) =
      (Uᵀ * G + G * U) i j at hr
    change HasDerivAt (fun s => metricInChart g c (x s) i j)
      (∑ r, v r * partialDeriv (fun z => metricInChart g c z i j) r (x t)) t at hd
    rwa [hr] at hd
  have hd := hasDerivAt_det_of_components (fun s => metricInChart g c (x s))
    (Uᵀ * G + G * U) t hG
  change HasDerivAt (fun s => (metricInChart g c (x s)).det)
    (determinantDifferential G (Uᵀ * G + G * U)) t at hd
  rw [determinantDifferential_congruence] at hd
  have hpos : 0 < G.det := (metricInChart_posDef g c (x t) hz).det_pos
  have hs := hd.sqrt hpos.ne'
  have hsqrt : 0 < Real.sqrt G.det := Real.sqrt_pos.mpr hpos
  have hrate : (2 * U.trace * G.det) / (2 * Real.sqrt G.det) =
      U.trace * Real.sqrt G.det := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hsqrt.ne')).mpr
    calc
      2 * U.trace * G.det = 2 * U.trace * (Real.sqrt G.det) ^ 2 := by
        rw [Real.sq_sqrt hpos.le]
      _ = _ := by ring
  rw [hrate] at hs
  exact hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! Ordinary derivatives of a coordinate geodesic variation give its
covariant Jacobi equation, with the actual Christoffel curvature sign. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def geodesicCovariantDerivative (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (v y w : ℝ → JacobiCoordinateVector) (s : ℝ) :
    JacobiCoordinateVector :=
  w s + jacobiConnection (fun i => connectionMatrix g c i (x s)) (v s) *ᵥ y s

theorem hasDerivAt_jacobiConnection (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (v : ℝ → JacobiCoordinateVector) (a : JacobiCoordinateVector)
    (t : ℝ) (hz : x t ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x (WithLp.toLp 2 (v t)) t) (hv : HasDerivAt v a t) :
    HasDerivAt (fun s => jacobiConnection (fun i => connectionMatrix g c i (x s)) (v s))
      (jacobiConnectionDerivative
          (fun i j => matrixPartial (connectionMatrix g c j) i (x t)) (v t) (v t) +
        jacobiConnection (fun i => connectionMatrix g c i (x t)) a) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hΓ (k : Fin 4) : HasDerivAt
      (fun s => connectionMatrix g c k (x s) i j)
      (∑ r, v t r * matrixPartial (connectionMatrix g c k) r (x t) i j) t := by
    exact hasDerivAt_coordinate_comp hx
      ((christoffel_contDiffAt g c (x t) hz (metricInChart_posDef g c (x t) hz).det_pos.ne'
        i k j).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have h := HasDerivAt.fun_sum (fun k (_ : k ∈ Finset.univ) =>
    (hasDerivAt_pi.mp hv k).mul (hΓ k))
  have heq : (∑ k, (a k * connectionMatrix g c k (x t) i j +
      v t k * (∑ r, v t r * matrixPartial (connectionMatrix g c k) r (x t) i j))) =
      (jacobiConnectionDerivative
        (fun r k => matrixPartial (connectionMatrix g c k) r (x t)) (v t) (v t) +
        jacobiConnection (fun k => connectionMatrix g c k (x t)) a) i j := by
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

/-- The derivative of the covariant first derivative is computed from
ordinary first and second variation data. -/
theorem hasDerivAt_geodesicCovariantDerivative (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (v y w : ℝ → JacobiCoordinateVector)
    (a b : JacobiCoordinateVector) (t : ℝ)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x (WithLp.toLp 2 (v t)) t) (hv : HasDerivAt v a t)
    (hy : HasDerivAt y (w t) t) (hw : HasDerivAt w b t) :
    HasDerivAt (geodesicCovariantDerivative g c x v y w)
      (b + (jacobiConnectionDerivative
          (fun i j => matrixPartial (connectionMatrix g c j) i (x t)) (v t) (v t) +
        jacobiConnection (fun i => connectionMatrix g c i (x t)) a) *ᵥ y t +
        jacobiConnection (fun i => connectionMatrix g c i (x t)) (v t) *ᵥ w t) t := by
  have hU := hasDerivAt_jacobiConnection g c x v a t hz hx hv
  simpa only [geodesicCovariantDerivative, Pi.add_apply, add_assoc] using!
    hw.add (hasDerivAt_jacobi_mulVec _ y _ (w t) t
    (fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp hU i) j) hy)

/-- A first variation satisfying the linearized geodesic ODE satisfies
the covariant Jacobi equation, expressed through ordinary coordinate derivatives. -/
theorem coordinate_geodesic_jacobi (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (v y w : ℝ → JacobiCoordinateVector)
    (a b : JacobiCoordinateVector) (t : ℝ)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x (WithLp.toLp 2 (v t)) t) (hv : HasDerivAt v a t)
    (hy : HasDerivAt y (w t) t) (hw : HasDerivAt w b t)
    (ha : a = -(jacobiConnection (fun i => connectionMatrix g c i (x t)) (v t) *ᵥ v t))
    (hb : b = -(jacobiConnectionDerivative
        (fun i j => matrixPartial (connectionMatrix g c j) i (x t)) (y t) (v t) *ᵥ v t) -
      jacobiConnection (fun i => connectionMatrix g c i (x t)) (w t) *ᵥ v t -
      jacobiConnection (fun i => connectionMatrix g c i (x t)) (v t) *ᵥ w t) :
    deriv (geodesicCovariantDerivative g c x v y w) t +
      jacobiConnection (fun i => connectionMatrix g c i (x t)) (v t) *ᵥ
        geodesicCovariantDerivative g c x v y w t +
      (∑ i, ∑ j, (y t i * v t j) • coordinateCurvatureMatrix g c i j (x t)) *ᵥ v t = 0 := by
  rw [(hasDerivAt_geodesicCovariantDerivative g c x v y w a b t hz hx hv hy hw).deriv]
  have h := actual_linearized_geodesic_curvature_identity g c (x t)
    (v t) a (y t) (w t) b ha hb
  simpa only [geodesicCovariantDerivative, Matrix.add_mulVec, Matrix.mulVec_add,
    two_smul, add_assoc] using h

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

def twoTensorProduct (S T : CovariantCoordinates 2) : CovariantCoordinates 4 :=
  fun a => S ![a 0, a 1] * T ![a 2, a 3]

theorem frameTensor_twoProduct (P : Mat4) (S T : CovariantCoordinates 2) :
    frameTensor P (twoTensorProduct S T) =
      twoTensorProduct (frameTensor P S) (frameTensor P T) := by
  funext v
  have hv : v = ![v 0, v 1, v 2, v 3] := by ext i; fin_cases i <;> rfl
  rw [hv, frameTensor_four]
  simp only [twoTensorProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue, frameTensor_two]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

theorem twoTensorContraction_pairing (R : CovariantCoordinates 4)
    (S T : CovariantCoordinates 2) :
    frameTensorPairing (twoTensorContraction R T) S =
      frameTensorPairing R (twoTensorProduct S T) := by
  unfold frameTensorPairing
  rw [sum_two_indices, sum_four_indices_p1]
  simp only [twoTensorContraction, twoTensorProduct, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Fin.isValue, Finset.sum_mul]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

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

theorem jacobiCurvatureCombination_frame (E : Mat4)
    (C : Fin 4 → Fin 4 → Mat4) (v : JacobiCoordinateVector) :
    E⁻¹ * jacobiCurvatureCombination C (E *ᵥ v) (fun a => E a 0) * E =
      ∑ i, v i • (E⁻¹ * pulledCurvatureEndomorphism E C i 0 * E) := by
  have h : jacobiCurvatureCombination C (E *ᵥ v) (fun a => E a 0) =
      ∑ i, v i • pulledCurvatureEndomorphism E C i 0 := by
    change curvatureFirstLinear C (fun a => E a 0) (E *ᵥ v) = _
    rw [jacobi_mulVec_sum, map_sum]
    simp only [map_smul, curvatureFirstLinear, LinearMap.coe_mk, AddHom.coe_mk,
      jacobiCurvatureCombination, pulledCurvatureEndomorphism]
  rw [h]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]

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

def twoFormCurvatureLinear (R : CovariantCoordinates 4) : TwoFormFour →ₗ[ℝ] TwoFormFour :=
  (-1 / 2 : ℝ) • twoFormExtractLinear.comp
    (twoTensorMatrixLinear.comp ((twoTensorContractionLinear R).comp twoFormTensorLinear))

def twoFormCurvatureAction (R : CovariantCoordinates 4) (a : TwoFormFour) : TwoFormFour :=
  twoFormCurvatureLinear R a

theorem twoFormTensor_injective : Function.Injective twoFormTensor := by
  intro a b h
  apply twoFormMatrix_injective
  ext i j
  exact congrFun h ![i,j]

theorem twoFormTensor_curvature (R : CovariantCoordinates 4)
    (hR : ∀ i j k l, R ![j,i,k,l] = -R ![i,j,k,l]) (a : TwoFormFour) :
    twoFormTensor (twoFormCurvatureAction R a) =
      (-1 / 2 : ℝ) • twoTensorContraction R (twoFormTensor a) := by
  let A : Mat4 := twoTensorMatrixLinear (twoTensorContraction R (twoFormTensor a))
  have hA : Aᵀ = -A := by
    ext i j
    change (∑ k, ∑ l, R ![j,i,k,l] * twoFormTensor a ![k,l]) =
      -(∑ k, ∑ l, R ![i,j,k,l] * twoFormTensor a ![k,l])
    calc
      _ = ∑ k, ∑ l, -R ![i,j,k,l] * twoFormTensor a ![k,l] := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        rw [hR i j k l]
      _ = _ := by simp only [neg_mul, Finset.sum_neg_distrib]
  change twoFormTensorLinear ((-1 / 2 : ℝ) • twoFormExtract A) = _
  rw [map_smul]
  congr 1
  funext v
  change twoFormMatrix (twoFormExtract A) (v 0) (v 1) = _
  rw [twoFormMatrix_extract A hA]
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  exact congrArg (twoTensorContraction R (twoFormTensor a)) hv.symm

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

theorem continuous_gradientSquareNorm (Z : X → Angular.Gradient)
    (hZ : ∀ i, Continuous (fun x => Z x i)) :
    Continuous (fun x => gradientSquareNorm (Z x)) := by
  unfold gradientSquareNorm squareNorm
  fun_prop

end
end PositiveEinsteinFour.Geometry
end


section

/-! Inverse parallel-frame coordinates of a variation and its covariant
derivative. The component equations follow by differentiating the inverse matrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem inverseFrameComponents_mul (E : ℝ → Mat4)
    (Y : ℝ → JacobiCoordinateVector) (t : ℝ) (hdet : (E t).det ≠ 0) :
    E t *ᵥ inverseFrameComponents E Y t = Y t := by
  rw [inverseFrameComponents, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

/-- In a parallel frame, ordinary component differentiation is the
inverse-frame image of covariant differentiation. -/
theorem hasDerivAt_inverseFrameComponents (E : ℝ → Mat4)
    (Y : ℝ → JacobiCoordinateVector) (U : Mat4) (Y' : JacobiCoordinateVector)
    (t : ℝ) (hE : ∀ i j, HasDerivAt (fun s => E s i j) (-(U * E t) i j) t)
    (hY : HasDerivAt Y Y' t) (hdet : (E t).det ≠ 0) :
    HasDerivAt (inverseFrameComponents E Y)
      ((E t)⁻¹ *ᵥ (Y' + U *ᵥ Y t)) t := by
  have hEd (i j : Fin 4) := (hE i j).differentiableAt
  have hy : DifferentiableAt ℝ (inverseFrameComponents E Y) t := by
    apply differentiableAt_pi.mpr
    intro i
    change DifferentiableAt ℝ (fun s => ∑ j, (E s)⁻¹ i j * Y s j) t
    exact DifferentiableAt.fun_sum (fun j _ =>
      (jacobi_inverse_differentiableAt E t hEd hdet i j).mul
        (hasDerivAt_pi.mp hY j).differentiableAt)
  have hn : ∀ᶠ s in 𝓝 t, (E s).det ≠ 0 :=
    (jacobi_det_differentiableAt E t hEd).continuousAt.eventually_ne hdet
  have heq : (fun s => E s *ᵥ inverseFrameComponents E Y s) =ᶠ[𝓝 t] Y := by
    filter_upwards [hn] with s hs
    exact inverseFrameComponents_mul E Y s hs
  have hp := (hasDerivAt_parallel_frameVector E (inverseFrameComponents E Y)
    U (deriv (inverseFrameComponents E Y) t) t hE hy.hasDerivAt).congr_of_eventuallyEq
      heq.symm
  have hder : E t *ᵥ deriv (inverseFrameComponents E Y) t = Y' + U *ᵥ Y t := by
    have h := hp.unique hY
    rw [inverseFrameComponents_mul E Y t hdet] at h
    exact (sub_eq_iff_eq_add.mp h)
  have hi := congrArg (fun v => (E t)⁻¹ *ᵥ v) hder
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec] at hi
  rw [← hi]
  exact hy.hasDerivAt

/-- Derivatives of the position and covariant-velocity components. -/
theorem inverseFrameComponents_covariant_pair (E : ℝ → Mat4)
    (Y F : ℝ → JacobiCoordinateVector) (U : Mat4)
    (Y' F' : JacobiCoordinateVector) (t : ℝ)
    (hE : ∀ i j, HasDerivAt (fun s => E s i j) (-(U * E t) i j) t)
    (hY : HasDerivAt Y Y' t) (hF : HasDerivAt F F' t)
    (hFvalue : F t = Y' + U *ᵥ Y t) (hdet : (E t).det ≠ 0) :
    HasDerivAt (inverseFrameComponents E Y) (inverseFrameComponents E F t) t ∧
      HasDerivAt (inverseFrameComponents E F)
        ((E t)⁻¹ *ᵥ (F' + U *ᵥ F t)) t := by
  constructor
  · simpa only [inverseFrameComponents, ← hFvalue] using
      hasDerivAt_inverseFrameComponents E Y U Y' t hE hY hdet
  · exact hasDerivAt_inverseFrameComponents E F U F' t hE hF hdet

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal curvature matrix in any fixed chart. This transports the
actual curvature tensor; it does not require a diagonal or moving chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem framed_lowered_endomorphism (E G : Mat4)
    (C : Fin 4 → Fin 4 → Mat4) (i j a b : Fin 4) :
    frameTensor E (loweredMatrixTensor G C) ![i,j,b,a] =
      (Eᵀ * G * pulledCurvatureEndomorphism E C i j * E) a b := by
  have hsum : (∑ p, ∑ q, (E p i * E q j) • (Eᵀ * (G * C p q) * E)) =
      Eᵀ * G * pulledCurvatureEndomorphism E C i j * E := by
    simp only [pulledCurvatureEndomorphism, Matrix.mul_sum, Matrix.sum_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hh := congrArg (fun A : Mat4 => A a b) hsum
  calc
    _ = ∑ p, ∑ q, (E p i * E q j) * (Eᵀ * (G * C p q) * E) a b :=
      framed_pairMatrix E (fun p q => G * C p q) i j a b
    _ = _ := by
      simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal curvature field and its derivative are linear contractions
of the two actual Weyl blocks along the first parallel frame direction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular
open scoped Manifold ContDiff

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.parallelCurvatureCalculusInstance1
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.parallelCurvatureCalculusInstance2
def normalDeviationLinear (q : Directions) : (Mat3 × Mat3) →ₗ[ℝ] Mat3 where
  toFun p := normalDeviation p.1 p.2 q
  map_add' p r := by
    change (1 / 2 : ℝ) • (p.1 + r.1 + mixingMatrix q * (p.2 + r.2) * (mixingMatrix q)ᵀ) =
      (1 / 2 : ℝ) • (p.1 + mixingMatrix q * p.2 * (mixingMatrix q)ᵀ) +
      (1 / 2 : ℝ) • (r.1 + mixingMatrix q * r.2 * (mixingMatrix q)ᵀ)
    rw [Matrix.mul_add, Matrix.add_mul]
    module
  map_smul' a p := by
    change (1 / 2 : ℝ) • (a • p.1 + mixingMatrix q * (a • p.2) * (mixingMatrix q)ᵀ) =
      a • ((1 / 2 : ℝ) • (p.1 + mixingMatrix q * p.2 * (mixingMatrix q)ᵀ))
    rw [Matrix.mul_smul, Matrix.smul_mul]
    module

def normalDeviationCLM (q : Directions) : (Mat3 × Mat3) →L[ℝ] Mat3 :=
  (normalDeviationLinear q).toContinuousLinearMap

theorem continuous_normalDeviation_comp {X : Type*} [TopologicalSpace X]
    {T U : X → Mat3} (hT : Continuous T) (hU : Continuous U) (q : Directions) :
    Continuous (fun x => normalDeviation (T x) (U x) q) :=
  (normalDeviationCLM q).continuous.comp (hT.prodMk hU)

theorem hasDerivAt_normalDeviation {T U : ℝ → Mat3} {Z V : Mat3} {t : ℝ}
    (hT : HasDerivAt T Z t) (hU : HasDerivAt U V t) (q : Directions) :
    HasDerivAt (fun s => normalDeviation (T s) (U s) q) (normalDeviation Z V q) t :=
  (normalDeviationCLM q).hasFDerivAt.comp_hasDerivAt t (hT.prodMk hU)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six-coordinate matrix and symmetry of the curvature action. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormExtract_apply (A : Mat4) (i : Fin 6) :
    twoFormExtract A i = A (AlgebraicCurvature.pair i).1 (AlgebraicCurvature.pair i).2 := by
  fin_cases i <;> rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuous dependence of the finite-dimensional curvature action on
the actual four-tensor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoFormCurvatureFamily : CovariantCoordinates 4 →ₗ[ℝ]
    (TwoFormFour →ₗ[ℝ] TwoFormFour) where
  toFun := twoFormCurvatureLinear
  map_add' R S := by
    change (-1 / 2 : ℝ) • (twoFormExtractLinear.comp
      (twoTensorMatrixLinear.comp ((twoTensorContractionFamily (R + S)).comp twoFormTensorLinear))) = _
    rw [map_add]
    simp only [LinearMap.add_comp, LinearMap.comp_add, smul_add]
    rfl
  map_smul' r R := by
    change (-1 / 2 : ℝ) • (twoFormExtractLinear.comp
      (twoTensorMatrixLinear.comp ((twoTensorContractionFamily (r • R)).comp twoFormTensorLinear))) = _
    rw [map_smul]
    simp only [RingHom.id_apply, LinearMap.smul_comp, LinearMap.comp_smul]
    rw [smul_comm]
    rfl

def twoFormCurvatureOperator : CovariantCoordinates 4 →L[ℝ]
    (TwoFormFour →L[ℝ] TwoFormFour) :=
  LinearMap.toContinuousLinearMap {
    toFun R := (twoFormCurvatureFamily R).toContinuousLinearMap
    map_add' R S := by
      apply ContinuousLinearMap.ext
      intro a
      exact congrArg (fun L : TwoFormFour →ₗ[ℝ] TwoFormFour => L a)
        (map_add twoFormCurvatureFamily R S)
    map_smul' r R := by
      apply ContinuousLinearMap.ext
      intro a
      exact congrArg (fun L : TwoFormFour →ₗ[ℝ] TwoFormFour => L a)
        (map_smul twoFormCurvatureFamily r R) }

theorem twoFormCurvatureAction_norm_le (R : CovariantCoordinates 4) (a : TwoFormFour) :
    ‖twoFormCurvatureAction R a‖ ≤ ‖twoFormCurvatureOperator‖ * ‖R‖ * ‖a‖ := by
  change ‖twoFormCurvatureOperator R a‖ ≤ _
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))

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

theorem twoFormPotentialMatrix_square_trace (R : CovariantCoordinates 4) :
    (twoFormPotentialMatrix R * twoFormPotentialMatrix R).trace =
      216 - 24 * (twoFormCurvatureMatrix R).trace +
        4 * (twoFormCurvatureMatrix R * twoFormCurvatureMatrix R).trace := by
  simp only [twoFormPotentialMatrix, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Matrix.trace_one,
    Fintype.card_fin]
  ring

theorem twoFormCurvatureMatrix_symmetric (R : CovariantCoordinates 4)
    (hR : ∀ i j k l, R ![k,l,i,j] = R ![i,j,k,l]) :
    (twoFormCurvatureMatrix R)ᵀ = twoFormCurvatureMatrix R := by
  ext i j
  exact congrArg Neg.neg (hR _ _ _ _)

theorem twoFormCurvatureMatrix_square_trace (R : CovariantCoordinates 4)
    (hR : ∀ i j k l, R ![k,l,i,j] = R ![i,j,k,l]) :
    (twoFormCurvatureMatrix R * twoFormCurvatureMatrix R).trace =
      ∑ i, ∑ j, twoFormCurvatureMatrix R i j ^ 2 := by
  have hs := twoFormCurvatureMatrix_symmetric R hR
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij : twoFormCurvatureMatrix R j i = twoFormCurvatureMatrix R i j :=
    congrArg (fun A : TwoFormMatrix => A i j) hs
  rw [hij, pow_two]

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

theorem twoFormSecondTrace_frame (E : Mat4) (T : CovariantCoordinates 4)
    (v : Fin 2 → Fin 4) :
    (∑ i, frameTensor E T (Fin.cons i (Fin.cons i v))) =
      frameTensor E (twoFormSecondTrace (E * Eᵀ) T) v := by
  simp only [frameTensor_cons]
  rw [Finset.sum_comm]
  calc
    (∑ a, ∑ i, E a i * ∑ b, E b i * frameTensor E (fun w => T (Fin.cons a (Fin.cons b w))) v) =
        ∑ a, ∑ b, (∑ i, E a i * E b i) *
          frameTensor E (fun w => T (Fin.cons a (Fin.cons b w))) v := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      symm
      change frameTensor E (fun w => ∑ a, ∑ b, (E * Eᵀ) a b *
        T (Fin.cons a (Fin.cons b w))) v = _
      rw [frameTensor_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [frameTensor_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [frameTensor_const_mul]
      rfl

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

theorem jacobiBlockMatrix_det (a : ℝ) (J : Matrix (Fin 3) (Fin 3) ℝ) :
    (jacobiBlockMatrix a J).det = a * J.det := by
  have hminor : (jacobiBlockMatrix a J).submatrix Fin.succ Fin.succ = J := by
    ext i j
    rfl
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [jacobiBlockMatrix, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero,
    one_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.succAbove_zero]
  change a * ((jacobiBlockMatrix a J).submatrix Fin.succ Fin.succ).det = _
  rw [hminor]

/-- This algebraic identity also holds at zero with Lean's division
convention; the geometric application uses positive `t`. -/
theorem jacobiBlockMatrix_scaled_det (t : ℝ)
    (J : Matrix (Fin 3) (Fin 3) ℝ) :
    (jacobiBlockMatrix 1 (t⁻¹ • J)).det = J.det / t ^ 3 := by
  rw [jacobiBlockMatrix_det, one_mul, Matrix.det_smul, Fintype.card_fin]
  rw [inv_pow, div_eq_mul_inv, mul_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A local minimum of the actual energy forces the second derivative to
be nonnegative.  The finite-piece version cancels the chart boundary
terms before applying this elementary one-variable fact. -/

namespace PositiveEinsteinFour.Geometry

open Set Filter
open scoped _root_.Topology BigOperators

noncomputable section

theorem finite_piece_index_nonneg (n : ℕ) (E : ℕ → ℝ → ℝ) (I L R : ℕ → ℝ)
    (hmin : IsLocalMin (fun s => ∑ i ∈ Finset.range n, E i s) 0)
    (hfd : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i < n, DifferentiableAt ℝ (E i) s)
    (hD : ∀ i < n, HasDerivAt (deriv (E i)) (I i + R i - L i) 0)
    (hjoin : ∀ i < n, R i = L (i + 1)) (hleft : L 0 = 0) (hright : L n = 0) :
    0 ≤ ∑ i ∈ Finset.range n, I i := by
  apply localMin_secondDeriv_nonneg _ _ hmin
  · filter_upwards [hfd] with s hs
    exact DifferentiableAt.fun_sum fun i hi => hs i (Finset.mem_range.mp hi)
  · exact finite_piece_index_secondDeriv n E I L R hfd hD hjoin hleft hright

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarPoissonKernelPotential
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceOrthogonalFour _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth zeroth-order potential does not obstruct the local bootstrap.
Only the principal and first-order perturbations need to be small. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

variable (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
  (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
  (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
  (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
  (hb : ∀ i x, ‖b i x‖ ≤ δ)
  (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
  (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)

include hδ ha ha1 ha2 hb hb1 hsmall

theorem scalar_finite_cutoff_chain_gain_of_potential (c : S) (u : T)
    (n : ℕ) (ψ : ℕ → S)
    (hnest : ∀ k < n, ScalarCutoffNested (ψ k) (ψ (k + 1)))
    (hu : MemSobolev 1 2 (M (ψ n) u))
    (hf : ∀ k ≤ n, MemSobolev (n : ℝ) 2
      (M (ψ k) (scalarPerturbedOperator a b u - u - M c u))) :
    MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M (ψ 0) u) := by
  induction n generalizing ψ with
  | zero => simpa using hu
  | succ n ih =>
      have ht : MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M (ψ 1) u) := by
        apply ih (fun k => ψ (k + 1))
        · intro k hk
          exact hnest (k + 1) (Nat.succ_lt_succ hk)
        · simpa only [Nat.succ_eq_add_one] using hu
        · intro k hk
          exact (hf (k + 1) (Nat.succ_le_succ hk)).mono
            (by exact_mod_cast Nat.le_succ n)
      have hs : MemSobolev (n : ℝ) 2
          (M (ψ 0) (scalarPerturbedOperator a b u - u - M c u)) :=
        (hf 0 (Nat.zero_le _)).mono (by exact_mod_cast Nat.le_succ n)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
          c (ψ 0) (ψ 1) (hnest 0 (Nat.zero_lt_succ n)) n u ht hs

/-- Local H1 and a smooth potential-source remainder give every Sobolev
order on each smaller compactly supported localization. -/
theorem scalar_ball_local_sobolev_of_potential (c : S) (u : T)
    (hH1 : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 → MemSobolev 1 2 (M ψ u))
    (hforce : ∀ n : ℕ, ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
        MemSobolev (n : ℝ) 2 (M ψ (scalarPerturbedOperator a b u - u - M c u)))
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (φ : S)
    (hφc : HasCompactSupport (φ : V → ℂ))
    (hφ : tsupport (φ : V → ℂ) ⊆ closedBall 0 r) :
    ∀ n : ℕ, MemSobolev (n : ℝ) 2 (M φ u) := by
  obtain ⟨ψ, hψ, hnest, hsupp⟩ := exists_scalar_nested_cutoffs r hr0 hr1 φ hφc hφ
  intro n
  have hgain := scalar_finite_cutoff_chain_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
    c u n ψ (fun k _ => hnest k) (hH1 (ψ n) (hsupp n).1 (hsupp n).2)
      (fun k _ => hforce n (ψ k) (hsupp k).1 (hsupp k).2)
  rw [hψ] at hgain
  exact hgain.mono (by exact_mod_cast Nat.le_succ n)

omit hδ ha ha1 ha2 hb hb1 hsmall

include hδ ha ha1 ha2 hb hb1 hsmall

/-- No smallness or prior regularity of the potential term times u is
assumed.  The original L2 solution has a smooth local representative. -/
theorem scalar_small_elliptic_potential_local_representative (c : S) (u : L2)
    (hH1 : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 → MemSobolev 1 2 (M ψ (u : T)))
    (hforce : ∀ n : ℕ, ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 → MemSobolev (n : ℝ) 2
        (M ψ (scalarPerturbedOperator a b (u : T) - (u : T) - M c (u : T)))) :
    ∃ f : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (u : V → ℂ) =ᵐ[volume.restrict (ball 0 (1 / 4))] f := by
  have hc : HasCompactSupport (scalarPotentialInnerCutoff : V → ℂ) := by
    change IsCompact (tsupport (scalarPotentialInnerCutoff : V → ℂ))
    rw [scalarPotentialInnerCutoff_tsupport]
    exact isCompact_closedBall _ _
  have hr : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (M scalarPotentialInnerCutoff (u : T)) :=
    scalar_ball_local_sobolev_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall c (u : T)
      hH1 hforce (1 / 2) (by norm_num) (by norm_num) scalarPotentialInnerCutoff hc
      (by rw [scalarPotentialInnerCutoff_tsupport])
  exact scalar_L2_cutoff_smooth_on u scalarPotentialInnerCutoff (ball 0 (1 / 4))
    isOpen_ball.measurableSet (fun _ hx => scalarPotentialInnerCutoff_one hx) hr

theorem scalar_small_elliptic_potential_local_real_representative (c : S) (u : L2)
    (hH1 : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 → MemSobolev 1 2 (M ψ (u : T)))
    (hforce : ∀ n : ℕ, ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 → MemSobolev (n : ℝ) 2
        (M ψ (scalarPerturbedOperator a b (u : T) - (u : T) - M c (u : T)))) :
    ∃ f : V → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (fun x : V => (u x).re) =ᵐ[volume.restrict (ball 0 (1 / 4))] f := by
  obtain ⟨f, hf, heq⟩ := scalar_small_elliptic_potential_local_representative
    a b δ hδ ha ha1 ha2 hb hb1 hsmall c u hH1 hforce
  refine ⟨Complex.reCLM ∘ f, Complex.reCLM.contDiff.comp hf, ?_⟩
  filter_upwards [heq] with x hx
  change (u x).re = (f x).re
  rw [hx]

end
end PositiveEinsteinFour.Geometry

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

theorem heatSignedGram_add_left (A B C : HeatMat6) :
    heatSignedGram (A + B) C = heatSignedGram A C + heatSignedGram B C := by
  simp [heatSignedGram, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]

theorem heatSignedGram_add_right (A B C : HeatMat6) :
    heatSignedGram A (B + C) = heatSignedGram A B + heatSignedGram A C := by
  simp [heatSignedGram, Matrix.mul_add, Matrix.trace_add]

theorem heatSignedGram_smul_left (a : ℝ) (A B : HeatMat6) :
    heatSignedGram (a • A) B = a * heatSignedGram A B := by
  simp [heatSignedGram, Matrix.transpose_smul,
    Matrix.trace_smul]

theorem heatSignedGram_one_left (A : HeatMat6) :
    heatSignedGram 1 A = (twoFormHodgeMatrix * A).trace := by
  simp [heatSignedGram]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


