-- Prove2me | Definitions.Def_OAIQ091C038
-- name    : OAIQ091C038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T17:46:57.618363+00:00
-- url     : https://prove2.me/theorems/78ea19b3-133f-4480-a53a-985db71a88de
-- title:
--   Definitions bundle OAIQ091C038 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 285 declarations of OpenAI's Lean: 63 definitions, 19 instances and 203 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.KineticLocalFlow.measurableSlice`, `OAI.PositiveEinsteinFour.Geometry.TwoFormL2`, `OAI.PositiveEinsteinFour.Geometry.canonicalUnitTangentMeasure`, `OAI.PositiveEinsteinFour.Geometry.chartBaseDensity`, `OAI.PositiveEinsteinFour.Geometry.chartCoordinateMeasure`, `OAI.PositiveEinsteinFour.Geometry.chartCotangentLowering`, `OAI.PositiveEinsteinFour.Geometry.chartHausdorffMeasure`, `OAI.PositiveEinsteinFour.Geometry.chartPolarLowering`, `OAI.PositiveEinsteinFour.Geometry.coordinateDirection`, `OAI.PositiveEinsteinFour.Geometry.covariantFieldTwoForm`, `OAI.PositiveEinsteinFour.Geometry.euclideanPolarCoordinates`, `OAI.PositiveEinsteinFour.Geometry.euclideanSphereIsometry`, `OAI.PositiveEinsteinFour.Geometry.exhaustingRadialSlab`, `OAI.PositiveEinsteinFour.Geometry.fourHeatBundlePolynomial`, `OAI.PositiveEinsteinFour.Geometry.fourHeatOneCovariantOperator`, `OAI.PositiveEinsteinFour.Geometry.fourHeatOneFirst`, `OAI.PositiveEinsteinFour.Geometry.fourHeatOneOperator`, `OAI.PositiveEinsteinFour.Geometry.fourHeatOneZero`, `OAI.PositiveEinsteinFour.Geometry.fourHeatPolynomial`, `OAI.PositiveEinsteinFour.Geometry.frozenFrameLinearEquiv`, `OAI.PositiveEinsteinFour.Geometry.frozenFrameMetric`, `OAI.PositiveEinsteinFour.Geometry.gramChartUnitTangent`, `OAI.PositiveEinsteinFour.Geometry.gramRadialLift`, `OAI.PositiveEinsteinFour.Geometry.heatNormalBundleParametrix`, `OAI.PositiveEinsteinFour.Geometry.kineticVariationMatrix`, `OAI.PositiveEinsteinFour.Geometry.measurableChart`, `OAI.PositiveEinsteinFour.Geometry.measurableRadialState`, `OAI.PositiveEinsteinFour.Geometry.metricHausdorffMeasure`, `OAI.PositiveEinsteinFour.Geometry.normalFrameAverage`, `OAI.PositiveEinsteinFour.Geometry.normalFrameHaar`, `OAI.PositiveEinsteinFour.Geometry.normalFrameHomeomorph`, `OAI.PositiveEinsteinFour.Geometry.normalIntegralCLM`, `OAI.PositiveEinsteinFour.Geometry.normalIntegralLinear`, `OAI.PositiveEinsteinFour.Geometry.normalizedChartFactor`, `OAI.PositiveEinsteinFour.Geometry.polarAngularMass`, `OAI.PositiveEinsteinFour.Geometry.polarAngularProbability`, `OAI.PositiveEinsteinFour.Geometry.polarDirectionProbability`, `OAI.PositiveEinsteinFour.Geometry.radialCotangentStateExtension`, `OAI.PositiveEinsteinFour.Geometry.smoothCovariantAlternation`, `OAI.PositiveEinsteinFour.Geometry.smoothCovariantDerivative` and 23 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean), [`EinsteinFour_WeylEstimates07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates07.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundle `OAIQ091C037` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C019`, `OAIQ091C020`, `OAIQ091C021`, `OAIQ091C022`, `OAIQ091C057`, `OAIQ091C071` and `OAIQ091C083`; the statements `OAI_PositiveEinsteinFour_Geometry_FrameReflectionData_opposite_kappaTest_integrable`, `OAI_PositiveEinsteinFour_Geometry_MetricGreenData_kappaTest`, `OAI_PositiveEinsteinFour_Geometry_ScalarCovariantData_curvature_identity`, `OAI_PositiveEinsteinFour_Geometry_regularized_H_minus_variance`, `OAI_PositiveEinsteinFour_Geometry_regularized_H_plus_variance`, `OAI_PositiveEinsteinFour_Geometry_regularized_difference_variance`, `OAI_PositiveEinsteinFour_Geometry_regularized_minus_variance`, `OAI_PositiveEinsteinFour_Quadratic_coupling_matrix_nonneg`, `OAI_PositiveEinsteinFour_Quadratic_quadratic_bound_closed` and `OAI_PositiveEinsteinFour_QuaternionFrame_cubic_bound_of_weight_square`; the proofs of `OAI_PositiveEinsteinFour_Bianchi_totalPlus_weightPlusPart_pairing`, `OAI_PositiveEinsteinFour_Geometry_MetricGreenData_minusCurvatureGreen`, `OAI_PositiveEinsteinFour_Geometry_regularized_H_minus_variance`, `OAI_PositiveEinsteinFour_Geometry_regularized_H_plus_variance`, `OAI_PositiveEinsteinFour_Geometry_regularized_difference_variance`, `OAI_PositiveEinsteinFour_Geometry_regularized_minus_variance`, `OAI_PositiveEinsteinFour_MetricDoubleCover_not_projective`, `OAI_PositiveEinsteinFour_Quadratic_quadratic_bound_closed` and `OAI_PositiveEinsteinFour_QuaternionFrame_cubic_bound_of_weight_square`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C037

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.mem_scalarH1MeanZero _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_first _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1SubtractMean_idempotent _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_equiv _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_none _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_some _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradientL2_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradient_subtractMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Freeze a Gram frame at one chart point. Continuity of the actual metric
then gives uniform, arbitrarily sharp quadratic-form bounds nearby. This is
the local comparison needed to identify metric Hausdorff volume with density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frozenFrameMetric (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (z : FourSpace) : Mat4 :=
  (chartGramMatrix g c 1 z₀)ᵀ * metricInChart g c z * chartGramMatrix g c 1 z₀

theorem frozenFrameMetric_self (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c) :
    frozenFrameMetric g c z₀ z₀ = 1 :=
  chartGramMatrix_normalizes g c 1 (by simp) z₀

theorem frozenFrameMetric_continuousAt (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) : ContinuousAt (frozenFrameMetric g c z₀) z₀ := by
  have hG : ContinuousAt (metricInChart g c) z₀ := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact (metricInChart_contDiffAt g c z₀ z₀.property i j).continuousAt
  exact (continuousAt_const.mul hG).mul continuousAt_const

theorem frozenFrameMetric_near_identity (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ z in 𝓝 z₀.val, ∀ v : FourSpace,
      (1 - δ) * ‖v‖ ^ 2 ≤
          WithLp.ofLp v ⬝ᵥ (frozenFrameMetric g c z₀ z *ᵥ WithLp.ofLp v) ∧
        WithLp.ofLp v ⬝ᵥ (frozenFrameMetric g c z₀ z *ᵥ WithLp.ofLp v) ≤
          (1 + δ) * ‖v‖ ^ 2 := by
  have he (i j : Fin 4) : ∀ᶠ z in 𝓝 z₀.val,
      |frozenFrameMetric g c z₀ z i j - (1 : Mat4) i j| < δ / 4 := by
    have hev : Continuous (fun B : Mat4 => B i j) :=
      (continuous_apply j).comp (continuous_apply i)
    have hc : ContinuousAt (fun z => frozenFrameMetric g c z₀ z i j) z₀.val :=
      hev.continuousAt.comp (frozenFrameMetric_continuousAt g c z₀)
    have hh : ContinuousAt (fun z =>
        |frozenFrameMetric g c z₀ z i j - (1 : Mat4) i j|) z₀.val :=
      (hc.sub continuousAt_const).abs
    apply hh.eventually_lt continuousAt_const
    rw [frozenFrameMetric_self, sub_self, abs_zero]
    positivity
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (he i))] with z hz
  intro v
  exact quadraticForm_near_identity _ δ hδ.le (fun i j => (hz i j).le) v

theorem frozenFrameMetric_pairing (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (z : FourSpace) (v : FourSpace) :
    WithLp.ofLp v ⬝ᵥ (frozenFrameMetric g c z₀ z *ᵥ WithLp.ofLp v) =
      (chartGramMatrix g c 1 z₀ *ᵥ WithLp.ofLp v) ⬝ᵥ
        (metricInChart g c z *ᵥ (chartGramMatrix g c 1 z₀ *ᵥ WithLp.ofLp v)) := by
  unfold frozenFrameMetric
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem frozenFrameMetric_tangentNorm (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (z : FourSpace) (v : FourSpace) :
    metricTangentNorm g ((chartAt FourSpace c).symm z)
      (mfderiv I4 I4 (chartAt FourSpace c).symm z
        (WithLp.toLp 2 (chartGramMatrix g c 1 z₀ *ᵥ WithLp.ofLp v))) =
      Real.sqrt (WithLp.ofLp v ⬝ᵥ (frozenFrameMetric g c z₀ z *ᵥ WithLp.ofLp v)) := by
  rw [metricTangentNorm_eq_sqrt, frozenFrameMetric_pairing, metricInChart_pairing]

/-- Arbitrarily sharp bounds on the actual inverse-chart tangent norm,
uniform over all tangent vectors in the frozen orthonormal coordinates. -/
theorem frozenFrameMetric_tangentNorm_near (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) :
    ∀ᶠ z in 𝓝 z₀.val, ∀ v : FourSpace,
      Real.sqrt (1 - δ) * ‖v‖ ≤
        metricTangentNorm g ((chartAt FourSpace c).symm z)
          (mfderiv I4 I4 (chartAt FourSpace c).symm z
            (WithLp.toLp 2 (chartGramMatrix g c 1 z₀ *ᵥ WithLp.ofLp v))) ∧
      metricTangentNorm g ((chartAt FourSpace c).symm z)
          (mfderiv I4 I4 (chartAt FourSpace c).symm z
            (WithLp.toLp 2 (chartGramMatrix g c 1 z₀ *ᵥ WithLp.ofLp v))) ≤
        Real.sqrt (1 + δ) * ‖v‖ := by
  filter_upwards [frozenFrameMetric_near_identity g c z₀ δ hδ] with z hz
  intro v
  have hlo := Real.sqrt_le_sqrt (hz v).1
  have hhi := Real.sqrt_le_sqrt (hz v).2
  rw [Real.sqrt_mul (sub_nonneg.mpr hδone), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg v)] at hlo
  rw [Real.sqrt_mul (by linarith : 0 ≤ 1 + δ), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg v)] at hhi
  constructor
  · simpa only [frozenFrameMetric_tangentNorm] using hlo
  · simpa only [frozenFrameMetric_tangentNorm] using hhi

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

theorem twoFormFrameValue_norm (o : FrameOrientation g) (u : M → TwoFormFour)
    (e : FrameBundle g) : ‖twoFormFrameValue o u e‖ = ‖u e.base‖ :=
  twoFormFrameAction_norm _ ((o.frame e.base).changeMatrix_orthogonal e.frame) _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The fixed linear coordinates determined by the Gram frame at one
point, and the sharp bounds on the coordinate differentials. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chartGramMatrix_isUnit (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c) :
    IsUnit (chartGramMatrix g c 1 z₀) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse
    (chartGramMatrix_normalizes g c 1 (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z₀))

def frozenFrameLinearEquiv (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c) :
    FourSpace ≃L[ℝ] FourSpace :=
  (LinearEquiv.ofBijective (Matrix.toEuclideanLin (chartGramMatrix g c 1 z₀))
    (fourMatrix_bijective _ (chartGramMatrix_isUnit g c z₀))).toContinuousLinearEquiv

theorem frozenFrame_forward_bound (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) :
    ∀ᶠ z in 𝓝 z₀.val, ∀ v : FourSpace,
      metricTangentENorm g ((chartAt FourSpace c).symm z)
        (mfderiv I4 I4 (chartAt FourSpace c).symm z
          (frozenFrameLinearEquiv g c z₀ v)) ≤
        ENNReal.ofReal (Real.sqrt (1 + δ)) * ‖v‖ₑ := by
  filter_upwards [frozenFrameMetric_tangentNorm_near g c z₀ δ hδ hδone] with z hz
  intro v
  rw [metricTangentENorm_eq_ofReal, ← ofReal_norm,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  exact (hz v).2

theorem frozenFrame_inverse_bound (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (δ : ℝ) (hδ : 0 < δ) (hδone : δ < 1) :
    ∀ᶠ z in 𝓝 z₀.val, z ∈ (chartAt FourSpace c).target →
      ∀ v : TangentSpace I4 ((chartAt FourSpace c).symm z),
        ‖(frozenFrameLinearEquiv g c z₀).symm
          (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm z) v)‖ₑ ≤
          ENNReal.ofReal (1 / Real.sqrt (1 - δ)) *
            metricTangentENorm g ((chartAt FourSpace c).symm z) v := by
  filter_upwards [frozenFrameMetric_tangentNorm_near g c z₀ δ hδ hδone.le] with z hz
  intro hzt v
  let E := frozenFrameLinearEquiv g c z₀
  let w := E.symm (mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm z) v)
  have hw : mfderiv I4 I4 (chartAt FourSpace c).symm z (E w) = v := by
    have hEw : E w = mfderiv I4 I4 (chartAt FourSpace c) ((chartAt FourSpace c).symm z) v :=
      E.apply_symm_apply _
    have hid := (mdifferentiable_chart (I := I4) c).symm_comp_deriv
      ((chartAt FourSpace c).map_target hzt)
    rw [(chartAt FourSpace c).right_inv hzt] at hid
    exact (congrArg (fun a : FourSpace =>
      mfderiv I4 I4 (chartAt FourSpace c).symm z a) hEw).trans
        (congrArg (fun L : FourSpace →L[ℝ] FourSpace => L v) hid)
  have hlo := (hz w).1
  change Real.sqrt (1 - δ) * ‖w‖ ≤
    metricTangentNorm g ((chartAt FourSpace c).symm z)
      (mfderiv I4 I4 (chartAt FourSpace c).symm z (E w)) at hlo
  rw [hw] at hlo
  have hroot : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.mpr (sub_pos.mpr hδone)
  have hnorm : ‖w‖ ≤ (1 / Real.sqrt (1 - δ)) *
      metricTangentNorm g ((chartAt FourSpace c).symm z) v := by
    rw [one_div, inv_mul_eq_div]
    exact (le_div_iff₀ hroot).mpr (by simpa only [mul_comm] using hlo)
  change ‖w‖ₑ ≤ _
  rw [metricTangentENorm_eq_ofReal, ← ofReal_norm,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.sqrt (1 - δ))]
  exact ENNReal.ofReal_le_ofReal hnorm

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

theorem measurable_positiveFrameSection (g : SmoothMetric M) (o : FrameOrientation g) :
    Measurable (positiveFrameSection g o) :=
  (exists_measurable_positive_frame g o).choose_spec.1

theorem positiveFrameSection_base (g : SmoothMetric M) (o : FrameOrientation g) (x : M) :
    (positiveFrameSection g o x).base = x :=
  ((exists_measurable_positive_frame g o).choose_spec.2 x).1

theorem positiveFrameSection_positive (g : SmoothMetric M) (o : FrameOrientation g) (x : M) :
    positiveFrameSection g o x ∈ o.positive :=
  ((exists_measurable_positive_frame g o).choose_spec.2 x).2

theorem measurable_orientedFrameParametrization (g : SmoothMetric M)
    (o : FrameOrientation g) : Measurable (orientedFrameParametrization g o) :=
  (continuous_frameRotate g).measurable.comp
    (((measurable_positiveFrameSection g o).comp measurable_fst).prodMk
      (continuous_orientedToOrthogonal.measurable.comp measurable_snd))

theorem orientedFrameParametrization_base (g : SmoothMetric M)
    (o : FrameOrientation g) (p : M × OrientedOrthogonalFour) :
    (orientedFrameParametrization g o p).base = p.1 :=
  positiveFrameSection_base g o p.1

theorem orientedFrameParametrization_positive (g : SmoothMetric M)
    (o : FrameOrientation g) (p : M × OrientedOrthogonalFour) :
    orientedFrameParametrization g o p ∈ o.positive :=
  frameRotate_oriented_positive o _ (positiveFrameSection_positive g o p.1) p.2

variable [T3Space M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normalizedVolumeProbability
instance canonicalFrameMeasure_probability (g : SmoothMetric M) (o : FrameOrientation g) :
    IsProbabilityMeasure (canonicalFrameMeasure g o) := by
  unfold canonicalFrameMeasure
  first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_orientedFrameParametrization <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem canonicalFrameMeasure_supported (g : SmoothMetric M) (o : FrameOrientation g) :
    ∀ᵐ e ∂canonicalFrameMeasure g o, e ∈ o.positive := by
  apply (ae_map_iff (measurable_orientedFrameParametrization g o).aemeasurable
    o.clopen.isClosed.measurableSet).mpr
  exact Filter.Eventually.of_forall (orientedFrameParametrization_positive g o)

theorem canonicalFrameMeasure_base (g : SmoothMetric M) (o : FrameOrientation g) :
    MeasurePreserving FrameBundle.base (canonicalFrameMeasure g o) (normalizedVolume g) := by
  refine ⟨(continuous_frameBase g).measurable, ?_⟩
  rw [canonicalFrameMeasure, Measure.map_map (continuous_frameBase g).measurable
    (measurable_orientedFrameParametrization g o)]
  have he : FrameBundle.base ∘ orientedFrameParametrization g o = Prod.fst := by
    funext p
    exact orientedFrameParametrization_base g o p
  rw [he]
  exact measurePreserving_fst.map_eq


theorem canonicalFrameMeasure_rotate (g : SmoothMetric M) (o : FrameOrientation g)
    (Q : OrientedOrthogonalFour) :
    MeasurePreserving (fun e : FrameBundle g => e.rotate (orientedToOrthogonal Q))
      (canonicalFrameMeasure g o) (canonicalFrameMeasure g o) := by
  let R : M × OrientedOrthogonalFour → M × OrientedOrthogonalFour :=
    fun p => (p.1, p.2 * Q)
  have hR : MeasurePreserving R ((normalizedVolume g).prod orientedFrameHaar)
      ((normalizedVolume g).prod orientedFrameHaar) := by
    exact (MeasurePreserving.id (normalizedVolume g)).prod (orientedFrameHaar_right Q)
  have hrot : Measurable (fun e : FrameBundle g => e.rotate (orientedToOrthogonal Q)) :=
    (continuous_frameRotate g).measurable.comp
      (measurable_id.prodMk measurable_const)
  refine ⟨hrot, ?_⟩
  rw [canonicalFrameMeasure, Measure.map_map hrot
    (measurable_orientedFrameParametrization g o)]
  have he : (fun e : FrameBundle g => e.rotate (orientedToOrthogonal Q)) ∘
      orientedFrameParametrization g o = orientedFrameParametrization g o ∘ R := by
    funext p
    exact frameRotate_mul (positiveFrameSection g o p.1) p.2 Q
  rw [he, ← Measure.map_map (measurable_orientedFrameParametrization g o) hR.measurable,
    hR.map_eq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positively oriented smooth orthonormal charts cover every point. Thus
the local smoothness condition on two-forms tests an actual neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem twoForm_positive_chart (o : FrameOrientation g) (c : M) :
    ∃ (S : Mat4) (hS : Sᵀ * S = 1) (U : Set FourSpace),
      IsOpen U ∧ chartAt FourSpace c c ∈ U ∧
      ∃ hUt : U ⊆ (chartAt FourSpace c).target,
        ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive := by
  obtain ⟨S, hS, hp⟩ := exists_positive_localGramSection g o c
  have hz : chartAt FourSpace c c ∈ (chartAt FourSpace c).target :=
    (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)
  have hc : chartGramSection g c S hS ⟨chartAt FourSpace c c, hz⟩ ∈ o.positive := by
    simpa only [localGramSection, dite_eq_left (mem_chart_source FourSpace c)] using hp.self_of_nhds
  let V : Set (ChartTarget c) := (chartGramSection g c S hS) ⁻¹' o.positive
  have hV : IsOpen V := o.clopen.isOpen.preimage (continuous_chartGramSection g c S hS)
  obtain ⟨W, hW, hWV⟩ := isOpen_induced_iff.mp hV
  have hmem (z : ChartTarget c) : z.val ∈ W ↔ chartGramSection g c S hS z ∈ o.positive := by
    change z ∈ Subtype.val ⁻¹' W ↔ z ∈ V
    rw [hWV]
  refine ⟨S, hS, (chartAt FourSpace c).target ∩ W,
    (chartAt FourSpace c).open_target.inter hW, ⟨hz, (hmem _).mpr hc⟩,
    inter_subset_left, ?_⟩
  intro z hz
  exact (hmem ⟨z, hz.1⟩).mp hz.2

theorem twoFormChartValue_norm (o : FrameOrientation g) (u : M → TwoFormFour)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    ‖twoFormChartValue o u c S hS z‖ = ‖u ((chartAt FourSpace c).symm z)‖ := by
  rw [twoFormChartValue, dite_eq_left hz, twoFormFrameValue_norm]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact Jacobian factor for frozen orthonormal coordinates. This
connects the sharp metric comparison to the actual chart density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix
open scoped Manifold ContDiff ENNReal NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frozenFrameLinearEquiv_det (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c) :
    LinearMap.det (frozenFrameLinearEquiv g c z₀ : FourSpace →ₗ[ℝ] FourSpace) =
      (chartGramMatrix g c 1 z₀).det := by
  change LinearMap.det (Matrix.toEuclideanLin (chartGramMatrix g c 1 z₀)) = _
  exact LinearMap.det_toLpLin 2 _

theorem frozenFrameLinearEquiv_symm_abs_det (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) :
    |LinearMap.det ((frozenFrameLinearEquiv g c z₀).symm : FourSpace →ₗ[ℝ] FourSpace)| =
      chartVolumeDensity g c z₀ := by
  let E := frozenFrameLinearEquiv g c z₀
  have hρ := chartVolumeDensity_mul_frame_det g c z₀ z₀.property
    (chartGramMatrix g c 1 z₀) (chartGramMatrix_normalizes g c 1 (by simp) z₀)
  have hd : |(chartGramMatrix g c 1 z₀).det| ≠ 0 := by
    intro h
    rw [h, mul_zero] at hρ
    exact zero_ne_one hρ
  have hi : |(chartGramMatrix g c 1 z₀).det|⁻¹ = chartVolumeDensity g c z₀ := by
    apply mul_left_cancel₀ hd
    calc
      _ = 1 := mul_inv_cancel₀ hd
      _ = chartVolumeDensity g c z₀ * |(chartGramMatrix g c 1 z₀).det| := hρ.symm
      _ = _ := mul_comm _ _
  change |LinearMap.det (E.toLinearEquiv.symm : FourSpace →ₗ[ℝ] FourSpace)| = _
  rw [LinearEquiv.det_coe_symm, frozenFrameLinearEquiv_det, abs_inv]
  exact hi

theorem volume_frozenFrame_symm_image (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (A : Set FourSpace) :
    volume ((frozenFrameLinearEquiv g c z₀).symm '' A) =
      ENNReal.ofReal (chartVolumeDensity g c z₀) * volume A := by
  rw [Measure.addHaar_image_continuousLinearEquiv,
    frozenFrameLinearEquiv_symm_abs_det]

theorem hausdorff_frozenFrame_symm_image (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (A : Set FourSpace) :
    (Measure.hausdorffMeasure 4 : Measure FourSpace)
        ((frozenFrameLinearEquiv g c z₀).symm '' A) =
      (euclideanHausdorffFactor : ℝ≥0∞) *
        (ENNReal.ofReal (chartVolumeDensity g c z₀) * volume A) := by
  rw [euclideanHausdorff_apply, volume_frozenFrame_symm_image]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A convex coordinate neighborhood with the sharp upper metric bound.
Together with the reverse estimate in MetricFrozenCoordinates, this gives
the local metric comparison used for Hausdorff volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_frozenFrame_symm_lipschitz (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) :
    ∃ r > (0 : ℝ), Metric.closedBall z₀.val r ⊆ (chartAt FourSpace c).target ∧
      ∀ x ∈ Metric.closedBall z₀.val r, ∀ y ∈ Metric.closedBall z₀.val r,
        metricEDistance g ((chartAt FourSpace c).symm x) ((chartAt FourSpace c).symm y) ≤
          ENNReal.ofReal (Real.sqrt (1 + δ)) *
            edist ((frozenFrameLinearEquiv g c z₀).symm x)
              ((frozenFrameLinearEquiv g c z₀).symm y) := by
  let E := frozenFrameLinearEquiv g c z₀
  let K : ℝ≥0 := ⟨Real.sqrt (1 + δ), Real.sqrt_nonneg _⟩
  have hKcoe : (K : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt (1 + δ)) :=
    ENNReal.coe_nnreal_eq K
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem ((chartAt FourSpace c).open_target.mem_nhds z₀.property)
      (frozenFrame_forward_bound g c z₀ δ hδ hδone))
  have hsmall : Metric.closedBall z₀.val (r / 2) ⊆ Metric.ball z₀.val r :=
    Metric.closedBall_subset_ball (by linarith)
  have ht : Metric.closedBall z₀.val (r / 2) ⊆ (chartAt FourSpace c).target :=
    fun z hz => (hball (hsmall hz)).1
  refine ⟨r / 2, by positivity, ht, ?_⟩
  intro x hx y hy
  have h := metricEDistance_chart_symm_linear_le g c E.toContinuousLinearMap
    (Metric.closedBall z₀.val (r / 2)) (convex_closedBall _ _) ht K
    (fun z hz v => by
      simpa only [hKcoe] using! (hball (hsmall hz)).2 v)
    (E.symm x) (E.symm y)
    (by simpa only [ContinuousLinearEquiv.coe_coe, E.apply_symm_apply] using hx)
    (by simpa only [ContinuousLinearEquiv.coe_coe, E.apply_symm_apply] using hy)
  simpa only [ContinuousLinearEquiv.coe_coe, E.apply_symm_apply, hKcoe] using! h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The canonical frame measure can be computed in any measurable positive
frame section. This permits local frame coordinates without changing the
measure used in the geometric estimates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem orientedFiberMeasure_eq_of_positive (o : FrameOrientation g)
    (e f : FrameBundle g) (hbase : e.base = f.base)
    (he : e ∈ o.positive) (hf : f ∈ o.positive) :
    orientedFiberMeasure e.frame = orientedFiberMeasure f.frame := by
  rcases e with ⟨x, e⟩
  rcases f with ⟨y, f⟩
  change x = y at hbase
  subst y
  exact orientedFiberMeasure_eq e f ((o.compatible x e f he).mp hf)

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

/-- Changing the measurable positive reference frame leaves the actual
normalized frame probability unchanged. -/
theorem canonicalFrameMeasure_eq_section (g : SmoothMetric M) (o : FrameOrientation g)
    (s : M → FrameBundle g) (hs : Measurable s)
    (hbase : ∀ x, (s x).base = x) (hpos : ∀ x, s x ∈ o.positive) :
    canonicalFrameMeasure g o =
      Measure.map (fun p : M × OrientedOrthogonalFour =>
        (s p.1).rotate (orientedToOrthogonal p.2))
        ((normalizedVolume g).prod orientedFrameHaar) := by
  have hm : Measurable (fun p : M × OrientedOrthogonalFour =>
      (s p.1).rotate (orientedToOrthogonal p.2)) :=
    (continuous_frameRotate g).measurable.comp
      ((hs.comp measurable_fst).prodMk
        (continuous_orientedToOrthogonal.measurable.comp measurable_snd))
  ext A hA
  rw [canonicalFrameMeasure,
    Measure.map_apply (measurable_orientedFrameParametrization g o) hA,
    Measure.map_apply hm hA,
    Measure.prod_apply ((measurable_orientedFrameParametrization g o) hA),
    Measure.prod_apply (hm hA)]
  apply lintegral_congr
  intro x
  have hb : (positiveFrameSection g o x).base = (s x).base :=
    (positiveFrameSection_base g o x).trans (hbase x).symm
  have he := orientedFiberMeasure_eq_of_positive o (positiveFrameSection g o x)
    (s x) hb (positiveFrameSection_positive g o x) (hpos x)
  have hv := congrArg (fun μ : Measure (FrameBundle g) => μ A) he
  rw [orientedFiberMeasure, orientedFiberMeasure,
    Measure.map_apply (continuous_orientedFrameMap _).measurable hA,
    Measure.map_apply (continuous_orientedFrameMap _).measurable hA] at hv
  exact hv

end
end PositiveEinsteinFour.Geometry
end


section

/-! The norm of an actual smooth two-form is continuous on the base,
despite the arbitrary reference frame used to store its coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem TwoFormSmooth.continuous_norm {u : M → TwoFormFour} (hu : TwoFormSmooth o u) :
    Continuous (fun x => ‖u x‖) := by
  apply continuous_iff_continuousAt.mpr
  intro c
  obtain ⟨S, hS, U, hU, hcU, hUt, hp⟩ := twoForm_positive_chart o c
  have hc : ContinuousAt (chartAt FourSpace c) c :=
    (chartAt FourSpace c).continuousAt (mem_chart_source FourSpace c)
  have hl := (hu c S hS U hU hUt hp).continuousOn.continuousAt (hU.mem_nhds hcU)
  apply (hl.norm.comp hc).congr_of_eventuallyEq
  filter_upwards [hc.eventually (hU.mem_nhds hcU),
    (chartAt FourSpace c).open_source.mem_nhds (mem_chart_source FourSpace c)] with x hx hxs
  change ‖u x‖ = ‖twoFormChartValue o u c S hS (chartAt FourSpace c x)‖
  rw [twoFormChartValue_norm o u c S hS _ (hUt hx), (chartAt FourSpace c).left_inv hxs]

theorem smoothTwoForm_norm_continuous (u : smoothTwoForms o) :
    Continuous (fun x => ‖u.val x‖) := TwoFormSmooth.continuous_norm u.property

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniqueness of the rotation-invariant probability on the actual unit
three-sphere. This identifies the angular measure arising from Euclidean
polar coordinates with the Hausdorff normalization used in the moments. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Matrix
open scoped BigOperators

noncomputable section

theorem orientedDirection_completion (q : Directions) :
    orientedDirection (directionOrientedMatrix q) firstDirection = q := by
  apply Subtype.ext
  ext i
  change (∑ j, directionFrameMatrix q i j * firstDirection.val j) = q.val i
  simp only [firstDirection_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, directionFrameMatrix_zero]

theorem continuous_orientedDirection :
    Continuous (fun p : OrientedOrthogonalFour × Directions => orientedDirection p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : OrientedOrthogonalFour × Directions =>
    WithLp.toLp 2 (fun i => ∑ j, p.1.val i j * p.2.val j))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  apply Continuous.mul
  · have hP : Continuous (fun p : OrientedOrthogonalFour × Directions => p.1.val) :=
      continuous_subtype_val.comp continuous_fst
    have hrow : Continuous (fun p : OrientedOrthogonalFour × Directions => p.1.val i) :=
      (continuous_apply i).comp hP
    exact (continuous_apply j).comp hrow
  · exact (PiLp.continuous_apply 2 _ j).comp (continuous_subtype_val.comp continuous_snd)

/-- Haar averaging of the orbit of any direction gives the fixed spherical
probability, independently of the starting direction. -/
theorem haar_integral_direction (f : Directions → ℝ) (hf : Continuous f) (q : Directions) :
    (∫ P, f (orientedDirection P q) ∂orientedFrameHaar) = ∫ r, f r ∂sphereMeasure := by
  have hc (r : Directions) : Continuous (fun P => f (orientedDirection P r)) := by
    have hp : Continuous (fun P : OrientedOrthogonalFour => (P, r)) :=
      continuous_id.prodMk continuous_const
    have ha : Continuous ((fun p : OrientedOrthogonalFour × Directions =>
        orientedDirection p.1 p.2) ∘ (fun P : OrientedOrthogonalFour => (P, r))) :=
      continuous_orientedDirection.comp hp
    have h := hf.comp ha
    simpa only [Function.comp_def] using h
  have hfirst : (∫ P, f (orientedDirection P firstDirection) ∂orientedFrameHaar) =
      ∫ r, f r ∂sphereMeasure := by
    refine haar_integral_eq_sphere_of_rotation _ f
      ((hc _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ?_
    intro P r
    exact congrArg f ((orientedDirection_mul P (directionOrientedMatrix r) firstDirection).trans
      (congrArg (orientedDirection P) (orientedDirection_completion r)))
  calc
    _ = ∫ P, f (orientedDirection (P * directionOrientedMatrix q) firstDirection)
        ∂orientedFrameHaar := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun P => (congrArg f
        ((orientedDirection_mul P (directionOrientedMatrix q) firstDirection).trans
          (congrArg (orientedDirection P) (orientedDirection_completion q)))).symm)
    _ = ∫ P, f (orientedDirection P firstDirection) ∂orientedFrameHaar :=
      (orientedFrameHaar_right (directionOrientedMatrix q)).integral_comp
        (Homeomorph.mulRight (directionOrientedMatrix q)).measurableEmbedding
          (fun P => f (orientedDirection P firstDirection))
    _ = _ := hfirst

/-- Every probability invariant under the actual SO(4) action agrees with
the normalized Hausdorff measure on the unit three-sphere. -/
theorem sphereMeasure_unique (μ : Measure Directions) [IsProbabilityMeasure μ]
    (hμ : ∀ P, MeasurePreserving (orientedDirection P) μ μ) : μ = sphereMeasure := by
  let : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let F : OrientedOrthogonalFour × Directions → ℝ :=
    fun p => f (orientedDirection p.1 p.2)
  have hc : Continuous F := f.continuous.comp continuous_orientedDirection
  have hi : Integrable F (orientedFrameHaar.prod μ) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hinv (P : OrientedOrthogonalFour) :
      (∫ q, f (orientedDirection P q) ∂μ) = ∫ q, f q ∂μ :=
    (hμ P).integral_comp (orientedDirection P).toHomeomorph.measurableEmbedding f
  calc
    _ = ∫ p, F p ∂(orientedFrameHaar.prod μ) := by
      rw [integral_prod _ hi]
      simp only [F, hinv, integral_const, probReal_univ, one_smul]
    _ = ∫ q, (∫ P, f (orientedDirection P q) ∂orientedFrameHaar) ∂μ :=
      integral_prod_symm _ hi
    _ = ∫ q, f q ∂sphereMeasure := by
      simp_rw [haar_integral_direction _ f.continuous]
      simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual covariant coordinate tensors of the smooth two-form sections.
The chart expression is recovered from any local orthonormal frame by its
metric coframe; no regularity of the chosen global reference frame is used. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem OrthonormalFrame.eq_of_matrix_eq {x : M} (e f : OrthonormalFrame g x)
    (h : e.matrix = f.matrix) : e = f := by
  cases e
  cases f
  cases h
  rfl

def twoFormTensorAt (o : FrameOrientation g) (u : M → TwoFormFour) (x : M) :
    CovariantCoordinates 2 :=
  frameTensor (o.frame x).matrix⁻¹ (twoFormTensor (u x))

def twoFormCoordinates (o : FrameOrientation g) (u : M → TwoFormFour)
    (c : M) (z : FourSpace) : CovariantCoordinates 2 :=
  frameTensor (chartInverseMatrix c z)
    (twoFormTensorAt o u ((chartAt FourSpace c).symm z))

theorem twoFormChartValue_tensor (o : FrameOrientation g) (u : M → TwoFormFour)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    twoFormTensor (twoFormChartValue o u c S hS z) =
      frameTensor (chartGramMatrix g c S z) (twoFormCoordinates o u c z) := by
  simp only [twoFormChartValue, dite_eq_left hz, twoFormFrameValue,
    chartGramSection, OrthonormalFrame.changeMatrix, chartGramFrame,
    twoFormTensor_frameAction, twoFormCoordinates, twoFormTensorAt,
    frameTensor_mul]

theorem twoFormCoordinates_from_chart (o : FrameOrientation g) (u : M → TwoFormFour)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    twoFormCoordinates o u c z =
      frameTensor ((chartGramMatrix g c S z)ᵀ * metricInChart g c z)
        (twoFormTensor (twoFormChartValue o u c S hS z)) := by
  rw [twoFormChartValue_tensor o u c S hS z hz, ← frameTensor_mul]
  have hnorm := chartGramMatrix_normalizes g c S hS ⟨z, hz⟩
  rw [mul_eq_one_comm.mp hnorm, frameTensor_one]

theorem twoForm_positive_chart_at (o : FrameOrientation g) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    ∃ (S : Mat4) (hS : Sᵀ * S = 1) (U : Set FourSpace),
      IsOpen U ∧ z ∈ U ∧ ∃ hUt : U ⊆ (chartAt FourSpace c).target,
        ∀ w (hw : w ∈ U), chartGramSection g c S hS ⟨w, hUt hw⟩ ∈ o.positive := by
  let e := chartGramFrame g c 1 (by simp) ⟨z, hz⟩
  let f := o.frame ((chartAt FourSpace c).symm z)
  let S := e.changeMatrix f
  have hS : Sᵀ * S = 1 := e.changeMatrix_orthogonal f
  have he : chartGramFrame g c S hS ⟨z, hz⟩ = f := by
    apply OrthonormalFrame.eq_of_matrix_eq
    simpa only [e, S, chartGramFrame, chartGramMatrix, Matrix.mul_one,
      Matrix.mul_assoc] using e.mul_changeMatrix f
  have hp : chartGramSection g c S hS ⟨z, hz⟩ ∈ o.positive := by
    change (⟨(chartAt FourSpace c).symm z, chartGramFrame g c S hS ⟨z, hz⟩⟩ :
      FrameBundle g) ∈ o.positive
    rw [he]
    exact o.frame_positive _
  let V : Set (ChartTarget c) := (chartGramSection g c S hS) ⁻¹' o.positive
  have hV : IsOpen V := o.clopen.isOpen.preimage (continuous_chartGramSection g c S hS)
  obtain ⟨W, hW, hWV⟩ := isOpen_induced_iff.mp hV
  have hmem (w : ChartTarget c) : w.val ∈ W ↔ chartGramSection g c S hS w ∈ o.positive := by
    change w ∈ Subtype.val ⁻¹' W ↔ w ∈ V
    rw [hWV]
  refine ⟨S, hS, (chartAt FourSpace c).target ∩ W,
    (chartAt FourSpace c).open_target.inter hW, ⟨hz, (hmem _).mpr hp⟩,
    inter_subset_left, ?_⟩
  intro w hw
  exact (hmem ⟨w, hw.1⟩).mp hw.2

theorem TwoFormSmooth.coordinates_contDiffAt {o : FrameOrientation g} {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (a : Fin 2 → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => twoFormCoordinates o u c w a) z := by
  obtain ⟨S, hS, U, hU, hzU, hUt, hp⟩ := twoForm_positive_chart_at o c z hz
  have hv := (hu c S hS U hU hUt hp).contDiffAt (hU.mem_nhds hzU)
  have hT : ContDiffAt ℝ ∞
      (fun w => twoFormTensor (twoFormChartValue o u c S hS w)) z :=
    twoFormTensorLinear.toContinuousLinearMap.contDiff.comp_contDiffAt z hv
  have hG (i j : Fin 4) : ContDiffAt ℝ ∞
      (fun w => ((chartGramMatrix g c S w)ᵀ * metricInChart g c w) i j) z := by
    change ContDiffAt ℝ ∞ (fun w => ∑ k,
      chartGramMatrix g c S w k i * metricInChart g c w k j) z
    exact ContDiffAt.sum (fun k _ => (chartGramMatrix_contDiffAt g c S z hz k i).mul
      (metricInChart_contDiffAt g c z hz k j))
  have hs : ContDiffAt ℝ ∞ (fun w =>
      frameTensor ((chartGramMatrix g c S w)ᵀ * metricInChart g c w)
        (twoFormTensor (twoFormChartValue o u c S hS w)) a) z := by
    unfold frameTensor
    apply ContDiffAt.sum
    intro b _
    exact (contDiffAt_prod (fun i _ => hG (b i) (a i))).mul
      ((ContinuousLinearMap.proj b : CovariantCoordinates 2 →L[ℝ] ℝ).contDiff.comp_contDiffAt z hT)
  apply hs.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
  exact congrFun (twoFormCoordinates_from_chart o u c S hS w hw) a

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual kinetic Hamiltonian has a local flow whose initial-value
Jacobian is one. Both the variational equation and local injectivity are
proved from the vector field, before applying change of variables. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def kineticVariationMatrix
    (V : CotangentCoordinates →L[ℝ] CotangentCoordinates) : CotangentMatrix :=
  LinearMap.toMatrix cotangentBasis cotangentBasis V.toLinearMap

theorem kineticVariationMatrix_derivative
    (X : CotangentCoordinates → CotangentCoordinates)
    (γ : ℝ → CotangentCoordinates)
    (V : ℝ → CotangentCoordinates →L[ℝ] CotangentCoordinates) (t : ℝ)
    (hX : DifferentiableAt ℝ X (γ t))
    (hV : HasDerivAt V ((fderiv ℝ X (γ t)).comp (V t)) t) (i j : CotangentIndex) :
    HasDerivAt (fun s => kineticVariationMatrix (V s) i j)
      ((cotangentJacobian X (γ t) * kineticVariationMatrix (V t)) i j) t := by
  let π : CotangentCoordinates →L[ℝ] ℝ :=
    (cotangentBasis.coord i).toContinuousLinearMap
  have hd := π.hasFDerivAt.comp_hasDerivAt t
    (hV.clm_apply (hasDerivAt_const t (cotangentBasis j)))
  have hc : ((fderiv ℝ X (γ t)).comp (V t)).toLinearMap =
      (fderiv ℝ X (γ t)).toLinearMap.comp (V t).toLinearMap := rfl
  have hm : kineticVariationMatrix ((fderiv ℝ X (γ t)).comp (V t)) =
      cotangentJacobian X (γ t) * kineticVariationMatrix (V t) := by
    rw [kineticVariationMatrix, hc,
      LinearMap.toMatrix_comp cotangentBasis cotangentBasis cotangentBasis,
      ← cotangentJacobian_eq_toMatrix X (γ t) hX]
    rfl
  have hentry := congrFun (congrFun hm i) j
  have hd' : HasDerivAt (fun s => kineticVariationMatrix (V s) i j)
      (kineticVariationMatrix ((fderiv ℝ X (γ t)).comp (V t)) i j) t := by
    simpa only [kineticVariationMatrix, LinearMap.toMatrix_apply, π, Function.comp_def,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
      map_zero, add_zero, ContinuousLinearMap.coe_coe] using hd
  rwa [hentry] at hd'

namespace KineticLocalFlow

variable {g : SmoothMetric M} {c : M} {p : CotangentCoordinates}

theorem jacobian_det (F : KineticLocalFlow g c p)
    (q : CotangentCoordinates) (hq : q ∈ Metric.ball p F.radius)
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) :
    (cotangentJacobian (fun x => F.map (x, t)) q).det = 1 := by
  let X := cotangentHamiltonianField (kineticHamiltonian g c)
  let α : ℝ → CotangentCoordinates := fun s => F.map (q, s)
  let V : ℝ → CotangentCoordinates →L[ℝ] CotangentCoordinates :=
    fun s => F.variation (q, s)
  let J := fun s => kineticVariationMatrix (V s)
  have hJ (s : ℝ) (hs : s ∈ Ioo (-F.time) F.time) (i j : CotangentIndex) :
      HasDerivAt (fun u => J u i j)
        ((cotangentJacobian X (α s) * J s) i j) s := by
    have hX : DifferentiableAt ℝ X (α s) :=
      (kineticHamiltonianField_contDiffAt g c (α s) (F.inside q hq s hs)).differentiableAt
        (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hV : HasDerivAt V ((fderiv ℝ X (α s)).comp (V s)) s :=
      F.variation_derivative q hq s hs
    exact kineticVariationMatrix_derivative X α V s hX hV i j
  have h0 : J 0 = 1 := by
    dsimp [J, V, kineticVariationMatrix]
    rw [F.initial_variation q hq]
    exact LinearMap.toMatrix_id cotangentBasis
  have hd := cotangentHamiltonian_variational_det_one (kineticHamiltonian g c)
    (fun s => F.map (q, s)) J (-F.time) F.time t
    ⟨by linarith [F.time_pos], F.time_pos⟩ ht
    (fun s hs => kineticHamiltonian_contDiffAt g c _ (F.inside q hq s hs)) hJ h0
  rw [cotangentJacobian_eq_toMatrix _ _ (F.initial_derivative q hq t ht).differentiableAt,
    (F.initial_derivative q hq t ht).fderiv]
  exact hd

theorem injective_slice (F : KineticLocalFlow g c p)
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) :
    InjOn (fun q => F.map (q, t)) (Metric.ball p F.radius) := by
  intro q hq r hr heq
  let f := cotangentHamiltonianField (kineticHamiltonian g c)
  let I := Ioo (-F.time) F.time
  let : PreconnectedSpace I :=
    isPreconnected_iff_preconnectedSpace.mp (convex_Ioo _ _).isPreconnected
  let S : Set I := {s | F.map (q, s.val) = F.map (r, s.val)}
  have hcq : Continuous (fun s : I => F.map (q, s.val)) :=
    (HasDerivAt.continuousOn (fun s hs => F.time_derivative q hq s hs)).domRestrict
  have hcr : Continuous (fun s : I => F.map (r, s.val)) :=
    (HasDerivAt.continuousOn (fun s hs => F.time_derivative r hr s hs)).domRestrict
  have hclosed : IsClosed S := isClosed_eq hcq hcr
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    change F.map (q, s.val) = F.map (r, s.val) at hs
    have hf : ContDiffAt ℝ 1 f (F.map (q, s.val)) :=
      (kineticHamiltonianField_contDiffAt g c _ (F.inside q hq s.val s.property)).of_le
        (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    obtain ⟨K, U, hU, hLip⟩ := hf.exists_lipschitzOnWith
    have hn : ∀ᶠ t in 𝓝 s.val, t ∈ I := isOpen_Ioo.mem_nhds s.property
    have hdq := hn.mono fun t ht => F.time_derivative q hq t ht
    have hdr := hn.mono fun t ht => F.time_derivative r hr t ht
    have hqU := hdq.self_of_nhds.continuousAt.preimage_mem_nhds hU
    have hrU := hdr.self_of_nhds.continuousAt.preimage_mem_nhds
      (by simpa only [← hs] using hU)
    have hu := ODE_solution_unique_of_eventually
      (Filter.Eventually.of_forall fun _ => hLip) (hdq.and hqU) (hdr.and hrU) hs
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds hu
  have hfull : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ
    ⟨⟨t, ht⟩, heq⟩
  have hz : (0 : ℝ) ∈ I := ⟨by linarith [F.time_pos], F.time_pos⟩
  have h : (⟨0, hz⟩ : I) ∈ S := by rw [hfull]; trivial
  exact (F.initial q hq).symm.trans (h.trans (F.initial r hr))

end KineticLocalFlow
end
end PositiveEinsteinFour.Geometry
end


section

/-! The reverse sharp bound at an arbitrary point of a fixed chart.
This permits comparison of the measures on the whole chart domain. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M]

theorem exists_frozenFrame_chart_lipschitz_at (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (δ : ℝ) (hδ : 0 < δ) (hδone : δ < 1) :
    ∃ s ∈ 𝓝 ((chartAt FourSpace c).symm z₀.val),
      s ⊆ (chartAt FourSpace c).source ∧ ∀ x ∈ s, ∀ y ∈ s,
        edist ((frozenFrameLinearEquiv g c z₀).symm (chartAt FourSpace c x))
          ((frozenFrameLinearEquiv g c z₀).symm (chartAt FourSpace c y)) ≤
          ENNReal.ofReal (1 / Real.sqrt (1 - δ)) * metricEDistance g x y := by
  let x₀ := (chartAt FourSpace c).symm z₀.val
  have hx₀ : x₀ ∈ (chartAt FourSpace c).source :=
    (chartAt FourSpace c).map_target z₀.property
  let K : ℝ≥0 := ⟨1 / Real.sqrt (1 - δ), by positivity⟩
  have hKcoe : (K : ℝ≥0∞) = ENNReal.ofReal (1 / Real.sqrt (1 - δ)) :=
    ENNReal.coe_nnreal_eq K
  have hKpos : 0 < K := by
    change 0 < 1 / Real.sqrt (1 - δ)
    exact one_div_pos.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hδone))
  have hc := (chartAt FourSpace c).continuousAt hx₀
  change Tendsto (chartAt FourSpace c) (𝓝 x₀) (𝓝 (chartAt FourSpace c x₀)) at hc
  have hc' : Tendsto (chartAt FourSpace c) (𝓝 x₀) (𝓝 z₀.val) := by
    simpa only [x₀, (chartAt FourSpace c).right_inv z₀.property] using hc
  have hf := hc' (frozenFrame_inverse_bound g c z₀ δ hδ hδone)
  let U : Set M := (chartAt FourSpace c).source ∩ {x | ∀ v : TangentSpace I4 x,
    ‖(frozenFrameLinearEquiv g c z₀).symm
      (mfderiv I4 I4 (chartAt FourSpace c) x v)‖ₑ ≤
      (K : ℝ≥0∞) * metricTangentENorm g x v}
  have hU : U ∈ 𝓝 x₀ := by
    filter_upwards [(chartAt FourSpace c).open_source.mem_nhds hx₀, hf] with x hx hbound
    refine ⟨hx, ?_⟩
    have h := hbound ((chartAt FourSpace c).map_source hx)
    rw [(chartAt FourSpace c).left_inv hx] at h
    simpa only [mem_ofPred_eq, hKcoe] using h
  obtain ⟨s, hs, hsU, hLip⟩ := exists_linear_chart_lipschitz_of_bound g c x₀
    (frozenFrameLinearEquiv g c z₀).symm.toContinuousLinearMap U hU
    (fun _ hx => hx.1) K hKpos (fun _ hx => hx.2)
  refine ⟨s, hs, fun x hx => (hsU hx).1, ?_⟩
  simpa only [hKcoe] using! hLip

end
end PositiveEinsteinFour.Geometry
end


section

/-! The angular measure in the actual four-dimensional Euclidean polar
decomposition, identified with the spherical measure used by the curvature
averages. No surface-area formula is needed for this identification. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory MeasureTheory.Measure Set Metric
open scoped Pointwise

noncomputable section

def euclideanSphereIsometry (e : FourSpace ≃ₗᵢ[ℝ] FourSpace) :
    EuclideanUnitSphere ≃ᵢ EuclideanUnitSphere where
  toFun q := ⟨e q.val, by
    simpa only [mem_sphere, dist_zero_right, e.norm_map] using q.property⟩
  invFun q := ⟨e.symm q.val, by
    simpa only [mem_sphere, dist_zero_right, e.symm.norm_map] using q.property⟩
  left_inv q := Subtype.ext (e.symm_apply_apply q.val)
  right_inv q := Subtype.ext (e.apply_symm_apply q.val)
  isometry_toFun := fun q r => e.isometry q.val r.val

theorem sphere_cone_preimage (e : FourSpace ≃ₗᵢ[ℝ] FourSpace)
    (s : Set EuclideanUnitSphere) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((euclideanSphereIsometry e) ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨r, hr, e q.val, ⟨euclideanSphereIsometry e q, hq, rfl⟩, (e.map_smul r q.val).symm⟩
  · rintro ⟨r, hr, y, ⟨q, hq, rfl⟩, h⟩
    refine ⟨r, hr, e.symm q.val, ⟨(euclideanSphereIsometry e).symm q, ?_, rfl⟩, ?_⟩
    · simpa using hq
    · apply e.injective
      simpa only [map_smul, e.apply_symm_apply] using h

/-- Orthogonal maps preserve the angular measure supplied by the polar
decomposition of Euclidean volume. -/
theorem euclideanSphere_measurePreserving (e : FourSpace ≃ₗᵢ[ℝ] FourSpace) :
    MeasurePreserving (euclideanSphereIsometry e)
      (volume : Measure FourSpace).toSphere (volume : Measure FourSpace).toSphere := by
  refine ⟨(euclideanSphereIsometry e).continuous.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (euclideanSphereIsometry e).continuous.measurable hs,
    Measure.toSphere_apply' _ ((euclideanSphereIsometry e).continuous.measurable hs),
    Measure.toSphere_apply' _ hs, sphere_cone_preimage]
  rw [e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

def polarAngularProbability : Measure EuclideanUnitSphere :=
  ((volume : Measure FourSpace).toSphere univ)⁻¹ • (volume : Measure FourSpace).toSphere

instance polarAngularProbability_probability : IsProbabilityMeasure polarAngularProbability := by
  constructor
  rw [polarAngularProbability, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero volume))
    (measure_ne_top _ _)

def polarDirectionProbability : Measure Directions :=
  Measure.map sphereToDirection polarAngularProbability

instance polarDirectionProbability_probability : IsProbabilityMeasure polarDirectionProbability :=
  (Measure.isProbabilityMeasure_map_iff sphereToDirection.continuous.measurable.aemeasurable).mpr
    (by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))

theorem polarDirectionProbability_eq_sphereMeasure : polarDirectionProbability = sphereMeasure := by
  apply sphereMeasure_unique
  intro P
  let e := orthogonalEuclideanIsometry P.val (by
    have h := (Matrix.mem_specialOrthogonalGroup_iff.mp P.property).1
    rwa [Matrix.mem_orthogonalGroup_iff'] at h)
  have hν : MeasurePreserving (euclideanSphereIsometry e)
      polarAngularProbability polarAngularProbability :=
    (euclideanSphere_measurePreserving e).smul_measure _
  refine ⟨(orientedDirection P).continuous.measurable, ?_⟩
  unfold polarDirectionProbability
  rw [Measure.map_map (orientedDirection P).continuous.measurable
    sphereToDirection.continuous.measurable]
  have he : (orientedDirection P) ∘ sphereToDirection =
      sphereToDirection ∘ (euclideanSphereIsometry e) := rfl
  rw [he, ← Measure.map_map sphereToDirection.continuous.measurable
    (euclideanSphereIsometry e).continuous.measurable, hν.map_eq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual positive L2 pairing on smooth two-form sections. No
measurability of the arbitrarily chosen reference-frame coefficients is
needed: their scalar pairings are intrinsic continuous functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_pairing_continuous (u v : smoothTwoForms o) :
    Continuous (fun x => inner ℝ (u.val x) (v.val x)) := by
  have he : (fun x => inner ℝ (u.val x) (v.val x)) =
      fun x => (‖(u + v).val x‖ ^ 2 - ‖u.val x‖ ^ 2 - ‖v.val x‖ ^ 2) / 2 := by
    funext x
    change inner ℝ (u.val x) (v.val x) =
      (‖u.val x + v.val x‖ ^ 2 - ‖u.val x‖ ^ 2 - ‖v.val x‖ ^ 2) / 2
    have h := norm_add_sq_real (u.val x) (v.val x)
    linarith only [h]
  rw [he]
  exact (((smoothTwoForm_norm_continuous (u + v)).pow 2).sub
    ((smoothTwoForm_norm_continuous u).pow 2) |>.sub
      ((smoothTwoForm_norm_continuous v).pow 2)).div_const 2

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

local instance twoFormL2_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

def smoothTwoFormL2Inner (u v : smoothTwoForms o) : ℝ :=
  ∫ x, inner ℝ (u.val x) (v.val x) ∂normalizedVolume g

theorem smoothTwoForm_pairing_integrable (u v : smoothTwoForms o) :
    Integrable (fun x => inner ℝ (u.val x) (v.val x)) (normalizedVolume g) :=
  (smoothTwoForm_pairing_continuous u v).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [CompactSpace M] [Nonempty M] in
theorem smoothTwoFormL2Inner_comm (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner u v = smoothTwoFormL2Inner v u := by
  unfold smoothTwoFormL2Inner
  apply integral_congr_ae
  filter_upwards [] with x
  exact real_inner_comm _ _

theorem smoothTwoFormL2Inner_add (u v w : smoothTwoForms o) :
    smoothTwoFormL2Inner (u + v) w = smoothTwoFormL2Inner u w + smoothTwoFormL2Inner v w := by
  change (∫ x, inner ℝ (u.val x + v.val x) (w.val x) ∂normalizedVolume g) = _
  simp_rw [inner_add_left]
  exact integral_add (smoothTwoForm_pairing_integrable u w) (smoothTwoForm_pairing_integrable v w)

omit [CompactSpace M] [Nonempty M] in
theorem smoothTwoFormL2Inner_smul (r : ℝ) (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner (r • u) v = r * smoothTwoFormL2Inner u v := by
  change (∫ x, inner ℝ (r • u.val x) (v.val x) ∂normalizedVolume g) = _
  simp_rw [real_inner_smul_left]
  exact integral_const_mul _ _

omit [CompactSpace M] [Nonempty M] in
theorem smoothTwoFormL2Inner_self (u : smoothTwoForms o) :
    smoothTwoFormL2Inner u u = ∫ x, ‖u.val x‖ ^ 2 ∂normalizedVolume g := by
  simp only [smoothTwoFormL2Inner, real_inner_self_eq_norm_sq]

omit [CompactSpace M] [Nonempty M] in
theorem smoothTwoFormL2Inner_nonneg (u : smoothTwoForms o) : 0 ≤ smoothTwoFormL2Inner u u := by
  rw [smoothTwoFormL2Inner_self]
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem smoothTwoFormL2Inner_definite (u : smoothTwoForms o)
    (hu : smoothTwoFormL2Inner u u = 0) : u = 0 := by
  let := normalizedVolume_isOpenPosMeasure g
  have hnorm := (smoothTwoForm_norm_continuous u).pow 2
  have hi := hnorm.integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  rw [smoothTwoFormL2Inner_self] at hu
  have hae : (fun x => ‖u.val x‖ ^ 2) =ᵐ[normalizedVolume g] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp hu
  have hzero : (fun x => ‖u.val x‖ ^ 2) = 0 := Measure.eq_of_ae_eq hae hnorm continuous_const
  apply Subtype.ext
  funext x
  apply norm_eq_zero.mp
  exact sq_eq_zero_iff.mp (congrFun hzero x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Coordinate compatibility of the actual two-form covariant derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem twoFormCoordinates_transition (o : FrameOrientation g) (u : M → TwoFormFour)
    (c d : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    twoFormCoordinates o u c z = frameTensor (chartTransitionMatrix c d z)
      (twoFormCoordinates o u d (chartTransition c d z)) := by
  unfold twoFormCoordinates
  rw [← frameTensor_mul, chartInverseMatrix_transition c d z hz hx]
  have hp : (chartAt FourSpace d).symm (chartTransition c d z) =
      (chartAt FourSpace c).symm z := (chartAt FourSpace d).left_inv hx
  rw [hp]

def twoFormCovariantCoordinates (o : FrameOrientation g) (u : M → TwoFormFour)
    (c : M) (z : FourSpace) : CovariantCoordinates 3 :=
  covariantDerivative g c (twoFormCoordinates o u c) z

theorem TwoFormSmooth.covariant_transition {o : FrameOrientation g} {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    twoFormCovariantCoordinates o u c z = frameTensor (chartTransitionMatrix c d z)
      (twoFormCovariantCoordinates o u d (chartTransition c d z)) := by
  apply covariantDerivative_chart_transition g c d _ _ z hz hx
  · intro a
    exact (hu.coordinates_contDiffAt d _ ((chartAt FourSpace d).map_source hx) a).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact (chart_overlap_eventually c d z hz hx).mono
      (fun w hw => twoFormCoordinates_transition o u c d w hw.1 hw.2)

def twoFormFramedCovariantDerivative (o : FrameOrientation g) (u : M → TwoFormFour)
    (e : FrameBundle g) : CovariantCoordinates 3 :=
  frameTensor e.frame.matrix
    (twoFormCovariantCoordinates o u e.base (chartAt FourSpace e.base e.base))

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

def polarAngularMass : ℝ≥0∞ := (volume : Measure FourSpace).toSphere univ

theorem polarAngularMass_ne_zero : polarAngularMass ≠ 0 :=
  measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero volume)

theorem polarAngularMass_ne_top : polarAngularMass ≠ ⊤ := measure_ne_top _ _

theorem map_euclidean_angular_measure :
    Measure.map sphereToDirection (volume : Measure FourSpace).toSphere =
      polarAngularMass • sphereMeasure := by
  have hraw : (volume : Measure FourSpace).toSphere =
      polarAngularMass • polarAngularProbability := by
    rw [polarAngularProbability, show (volume : Measure FourSpace).toSphere univ =
      polarAngularMass from rfl, smul_smul,
      ENNReal.mul_inv_cancel polarAngularMass_ne_zero polarAngularMass_ne_top, one_smul]
  conv_lhs => rw [hraw]
  rw [Measure.map_smul]
  change polarAngularMass • polarDirectionProbability = _
  rw [polarDirectionProbability_eq_sphereMeasure]

def euclideanPolarCoordinates : ({0}ᶜ : Set FourSpace) →
    Directions × Ioi (0 : ℝ) :=
  Prod.map sphereToDirection id ∘ homeomorphUnitSphereProd FourSpace

/-- Euclidean volume decomposes into spherical probability and the cubic
radial density, with its fixed positive angular factor. -/
theorem euclideanPolarCoordinates_measurePreserving :
    MeasurePreserving euclideanPolarCoordinates
      ((volume : Measure FourSpace).comap Subtype.val)
      ((polarAngularMass • sphereMeasure).prod (Measure.volumeIoiPow 3)) := by
  have h1 := Measure.measurePreserving_homeomorphUnitSphereProd
    (volume : Measure FourSpace)
  have h2 : MeasurePreserving (Prod.map sphereToDirection id)
      ((volume : Measure FourSpace).toSphere.prod (Measure.volumeIoiPow 3))
      ((Measure.map sphereToDirection (volume : Measure FourSpace).toSphere).prod
        (Measure.volumeIoiPow 3)) :=
    (show MeasurePreserving sphereToDirection
      (volume : Measure FourSpace).toSphere
      (Measure.map sphereToDirection (volume : Measure FourSpace).toSphere) from
        ⟨sphereToDirection.continuous.measurable, rfl⟩).prod
      (MeasurePreserving.id (Measure.volumeIoiPow 3))
  have hdim : Module.finrank ℝ FourSpace - 1 = 3 := by
    simp [FourSpace]
  rw [hdim] at h1
  simpa only [euclideanPolarCoordinates, map_euclidean_angular_measure] using h2.comp h1

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual Hausdorff-measure comparisons on arbitrarily small chart
neighborhoods, with constants tending to one in frozen orthonormal
coordinates. No volume-density identity is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

def metricHausdorffMeasure (g : SmoothMetric M) : Measure M := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  exact Measure.hausdorffMeasure 4

theorem volumeMeasure_eq_scaled_hausdorff (g : SmoothMetric M) :
    volumeMeasure g = ENNReal.ofReal (Real.pi ^ 2 / 32) • metricHausdorffMeasure g := rfl

theorem exists_metricHausdorff_chart_bounds (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (δ : ℝ) (hδ : 0 < δ) (hδone : δ < 1) :
    ∃ U : Set FourSpace, IsOpen U ∧ z₀.val ∈ U ∧ U ⊆ (chartAt FourSpace c).target ∧
      ∀ A ⊆ U,
        metricHausdorffMeasure g ((chartAt FourSpace c).symm '' A) ≤
          (ENNReal.ofReal (Real.sqrt (1 + δ))) ^ (4 : ℝ) *
            (Measure.hausdorffMeasure 4 : Measure FourSpace)
              ((frozenFrameLinearEquiv g c z₀).symm '' A) ∧
        (Measure.hausdorffMeasure 4 : Measure FourSpace)
            ((frozenFrameLinearEquiv g c z₀).symm '' A) ≤
          (ENNReal.ofReal (1 / Real.sqrt (1 - δ))) ^ (4 : ℝ) *
            metricHausdorffMeasure g ((chartAt FourSpace c).symm '' A) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  let E := frozenFrameLinearEquiv g c z₀
  let Khi : ℝ≥0 := ⟨Real.sqrt (1 + δ), Real.sqrt_nonneg _⟩
  let Klo : ℝ≥0 := ⟨1 / Real.sqrt (1 - δ), by positivity⟩
  have hp : (Khi : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt (1 + δ)) :=
    ENNReal.coe_nnreal_eq Khi
  have hm : (Klo : ℝ≥0∞) = ENNReal.ofReal (1 / Real.sqrt (1 - δ)) :=
    ENNReal.coe_nnreal_eq Klo
  obtain ⟨r, hr, ht, hupper⟩ := exists_frozenFrame_symm_lipschitz g c z₀ δ hδ hδone.le
  obtain ⟨s, hs, _hs_source, hlower⟩ :=
    exists_frozenFrame_chart_lipschitz_at g c z₀ δ hδ hδone
  have hpre : (chartAt FourSpace c).symm ⁻¹' s ∈ 𝓝 z₀.val :=
    ((chartAt FourSpace c).symm.continuousAt z₀.property).preimage_mem_nhds hs
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (Metric.closedBall_mem_nhds z₀.val hr) hpre)
  refine ⟨Metric.ball z₀.val ε, Metric.isOpen_ball, Metric.mem_ball_self hε,
    fun z hz => ht (hεsub hz).1, ?_⟩
  intro A hA
  have hAt : A ⊆ (chartAt FourSpace c).target := fun z hz => ht (hεsub (hA hz)).1
  have hAs : (chartAt FourSpace c).symm '' A ⊆ s := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hεsub (hA hz)).2
  have hLipHi : LipschitzOnWith Khi ((chartAt FourSpace c).symm ∘ E)
      (E.symm '' A) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change metricEDistance g ((chartAt FourSpace c).symm (E (E.symm x)))
      ((chartAt FourSpace c).symm (E (E.symm y))) ≤ Khi * edist (E.symm x) (E.symm y)
    rw [E.apply_symm_apply, E.apply_symm_apply, hp]
    exact hupper x (hεsub (hA hx)).1 y (hεsub (hA hy)).1
  have hLipLo : LipschitzOnWith Klo (E.symm ∘ chartAt FourSpace c)
      ((chartAt FourSpace c).symm '' A) := by
    intro x hx y hy
    change edist (E.symm (chartAt FourSpace c x)) (E.symm (chartAt FourSpace c y)) ≤
      Klo * metricEDistance g x y
    rw [hm]
    exact hlower x (hAs hx) y (hAs hy)
  have hiHi : ((chartAt FourSpace c).symm ∘ E) '' (E.symm '' A) =
      (chartAt FourSpace c).symm '' A := by
    rw [Set.image_image]
    congr 1
    funext x
    simp only [Function.comp_apply, E.apply_symm_apply]
  have hiLo : (E.symm ∘ chartAt FourSpace c) '' ((chartAt FourSpace c).symm '' A) =
      E.symm '' A := by
    rw [Set.image_image]
    apply Set.image_congr
    intro z hz
    simp only [Function.comp_apply, (chartAt FourSpace c).right_inv (hAt hz)]
  constructor
  · have h := hLipHi.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 4)
    rw [hiHi, hp] at h
    exact h
  · have h := hLipLo.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 4)
    rw [hiLo, hm] at h
    exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smoothness can be verified using the actual covariant coordinate
coefficients. This is the converse needed to assemble regular weak forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormChartValue_extract (u : M → TwoFormFour) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    twoFormChartValue o u c S hS z = twoFormExtract
      (fun i j => frameTensor (chartGramMatrix g c S z) (twoFormCoordinates o u c z) ![i,j]) := by
  have h := twoFormChartValue_tensor o u c S hS z hz
  calc
    _ = twoFormExtract (twoFormMatrix (twoFormChartValue o u c S hS z)) :=
      (twoFormExtract_matrix _).symm
    _ = _ := congrArg (fun T : CovariantCoordinates 2 =>
      twoFormExtract (fun i j => T ![i,j])) h

theorem TwoFormSmooth.of_coordinates {u : M → TwoFormFour}
    (hu : ∀ c z, z ∈ (chartAt FourSpace c).target →
      ∀ a : Fin 2 → Fin 4, ContDiffAt ℝ ∞ (fun w => twoFormCoordinates o u c w a) z) :
    TwoFormSmooth o u := by
  intro c S hS U _hU hUt _hp
  let T : FourSpace → CovariantCoordinates 2 := fun z =>
    frameTensor (chartGramMatrix g c S z) (twoFormCoordinates o u c z)
  have hT : ContDiffOn ℝ ∞ T U := by
    apply contDiffOn_pi.mpr
    intro a z hz
    apply ContDiffAt.contDiffWithinAt
    change ContDiffAt ℝ ∞ (fun w => ∑ b, (∏ k, chartGramMatrix g c S w (b k) (a k)) *
      twoFormCoordinates o u c w b) z
    apply ContDiffAt.sum
    intro b _
    exact (contDiffAt_prod (fun k _ => chartGramMatrix_contDiffAt g c S z (hUt hz) (b k) (a k))).mul
      (hu c z (hUt hz) b)
  let L : CovariantCoordinates 2 →L[ℝ] TwoFormFour :=
    (twoFormExtractLinear.comp twoTensorMatrixLinear).toContinuousLinearMap
  have hL := L.contDiff.comp_contDiffOn hT
  apply hL.congr
  intro z hz
  exact twoFormChartValue_extract u c S hS z (hUt hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The continuous frame-bundle realization of an actual smooth two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormFramedValue (o : FrameOrientation g) (u : M → TwoFormFour)
    (e : FrameBundle g) : CovariantCoordinates 2 :=
  frameTensor e.frame.matrix (twoFormCoordinates o u e.base (chartAt FourSpace e.base e.base))

theorem twoFormFramedValue_eq (o : FrameOrientation g) (u : M → TwoFormFour)
    (e : FrameBundle g) :
    twoFormFramedValue o u e = twoFormTensor (twoFormFrameValue o u e) := by
  unfold twoFormFramedValue twoFormCoordinates
  rw [chartInverseMatrix_center, frameTensor_one,
    (chartAt FourSpace e.base).left_inv (mem_chart_source FourSpace e.base)]
  simp only [twoFormTensorAt, twoFormFrameValue, OrthonormalFrame.changeMatrix,
    twoFormTensor_frameAction, frameTensor_mul]

theorem TwoFormSmooth.continuous_framedValue {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) : Continuous (twoFormFramedValue o u) := by
  apply continuous_framedTensor g (twoFormCoordinates o u)
  · intro c z hz a
    exact (hu.coordinates_contDiffAt c z hz a).continuousAt
  · exact twoFormCoordinates_transition o u

theorem twoFormFramedValue_norm (o : FrameOrientation g) (u : M → TwoFormFour)
    (e : FrameBundle g) :
    frameTensorSquareNorm (twoFormFramedValue o u e) = 2 * ‖u e.base‖ ^ 2 := by
  rw [twoFormFramedValue_eq, twoFormTensor_norm, twoFormFrameValue_norm]

theorem TwoFormSmooth.framedValue_parallel_derivative {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (γ : ℝ → FrameBundle g) (t : ℝ) (i : Fin 4)
    (hγ : ContinuousAt γ t) (hp : ParallelFrameCurveAt g γ i t) (a : Fin 2 → Fin 4) :
    HasDerivAt (fun s => twoFormFramedValue o u (γ s) a)
      (twoFormFramedCovariantDerivative o u (γ t) (Fin.cons i a)) t := by
  apply hasDerivAt_framedTensor g (twoFormCoordinates o u)
  · intro c z hz a
    exact (hu.coordinates_contDiffAt c z hz a).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact twoFormCoordinates_transition o u
  · exact hu.covariant_transition
  · exact hγ
  · exact hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Hilbert completion of actual smooth two-form sections with their
intrinsic L2 pairing. The inclusion of pointwise smooth sections is an
injective linear isometry with dense range. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

/- The L2 topology of the completion differs from the pointwise topology
on the smooth function submodule. -/

instance smoothTwoFormInnerCore : InnerProductSpace.Core ℝ (SmoothL2TwoForm o) where
  inner u v := smoothTwoFormL2Inner (o := o) u v
  conj_inner_symm u v := by
    simpa only [conj_trivial] using smoothTwoFormL2Inner_comm v u
  re_inner_nonneg := smoothTwoFormL2Inner_nonneg
  add_left := smoothTwoFormL2Inner_add
  smul_left u v r := by
    change smoothTwoFormL2Inner (o := o) (r • (u : smoothTwoForms o)) v =
      r * smoothTwoFormL2Inner (o := o) u v
    exact smoothTwoFormL2Inner_smul r u v
  definite := smoothTwoFormL2Inner_definite

instance smoothTwoFormNormedAddCommGroup : NormedAddCommGroup (SmoothL2TwoForm o) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance smoothTwoFormInnerProductSpace : InnerProductSpace ℝ (SmoothL2TwoForm o) :=
  InnerProductSpace.ofCore _

def TwoFormL2 (o : FrameOrientation g) := UniformSpace.Completion (SmoothL2TwoForm o)
  deriving NormedAddCommGroup, NormedSpace ℝ, InnerProductSpace ℝ, CompleteSpace

end
end PositiveEinsteinFour.Geometry
end


section

/-! Express the metric Hausdorff measure on a fixed chart as a measure
on Euclidean coordinates. The totalized chart is used only on its source. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

def measurableChart (c : M) : M → FourSpace := by
  classical
  exact (chartAt FourSpace c).source.piecewise (chartAt FourSpace c) (fun _ => 0)

omit [IsManifold I4 ∞ M] [T3Space M] in
theorem measurable_measurableChart (c : M) : Measurable (measurableChart c) := by
  classical
  exact (chartAt FourSpace c).continuousOn.measurable_piecewise continuousOn_const
    (chartAt FourSpace c).open_source.measurableSet

omit [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M] in
theorem measurableChart_eq (c x : M) (hx : x ∈ (chartAt FourSpace c).source) :
    measurableChart c x = chartAt FourSpace c x := by
  classical
  exact piecewise_eq_of_mem _ _ _ hx

def chartHausdorffMeasure (g : SmoothMetric M) (c : M) : Measure FourSpace :=
  Measure.map (measurableChart c) ((metricHausdorffMeasure g).restrict
    (chartAt FourSpace c).source)

theorem chartHausdorffMeasure_apply (g : SmoothMetric M) (c : M)
    (A : Set FourSpace) (hA : MeasurableSet A) (hAt : A ⊆ (chartAt FourSpace c).target) :
    chartHausdorffMeasure g c A = metricHausdorffMeasure g ((chartAt FourSpace c).symm '' A) := by
  rw [chartHausdorffMeasure, Measure.map_apply (measurable_measurableChart c) hA,
    Measure.restrict_apply ((measurable_measurableChart c) hA)]
  congr 1
  ext x
  constructor
  · rintro ⟨hxA, hxs⟩
    refine ⟨chartAt FourSpace c x, ?_, (chartAt FourSpace c).left_inv hxs⟩
    change measurableChart c x ∈ A at hxA
    rwa [measurableChart_eq c x hxs] at hxA
  · rintro ⟨z, hz, rfl⟩
    have hzs := (chartAt FourSpace c).map_target (hAt hz)
    refine ⟨?_, hzs⟩
    change measurableChart c ((chartAt FourSpace c).symm z) ∈ A
    rw [measurableChart_eq c _ hzs, (chartAt FourSpace c).right_inv (hAt hz)]
    exact hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous flow that fixes the radial coordinate and preserves the
ambient product measure preserves every energy shell. The continuity step
upgrades the usual almost-everywhere conclusion to every positive radius. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory MeasureTheory.Measure Set Filter TopologicalSpace
open scoped ENNReal _root_.Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X] [PseudoMetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

/-- Product measure preservation and continuity imply preservation on
every radial slice, including the unit kinetic-energy shell. -/
theorem measurePreserving_energyShell
    (ν : Measure X) [IsProbabilityMeasure ν]
    (ρ : Measure PositiveRadius) [SigmaFinite ρ] [IsOpenPosMeasure ρ]
    (F : PositiveRadius × X → X) (hF : Continuous F)
    (hambient : MeasurePreserving (fun p : PositiveRadius × X => (p.1, F p))
      (ρ.prod ν) (ρ.prod ν)) (r : PositiveRadius) :
    MeasurePreserving (fun x => F (r, x)) ν ν := by
  have hFr : Continuous (fun x => F (r, x)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  refine ⟨hFr.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let A : PositiveRadius → ℝ := fun t => ∫ x, f (F (t, x)) ∂ν
  let c : ℝ := ∫ x, f x ∂ν
  have hA : Continuous A := by
    apply continuous_of_dominated
    · intro t
      exact (f.continuous.comp (hF.comp
        (continuous_const.prodMk continuous_id))).aestronglyMeasurable
    · intro t
      exact Eventually.of_forall (fun x => f.norm_coe_le_norm (F (t, x)))
    · exact integrable_const ‖f‖
    · exact Eventually.of_forall (fun x =>
        f.continuous.comp (hF.comp (continuous_id.prodMk continuous_const)))
  have hAbound (t : PositiveRadius) : ‖A t‖ ≤ ‖f‖ := by
    simpa only [A, probReal_univ, one_mul, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := ν)
        (Eventually.of_forall (fun x => f.norm_coe_le_norm (F (t, x)))))
  have hfinite (s : Set PositiveRadius) (_hs : MeasurableSet s) (hfin : ρ s < ⊤) :
      IntegrableOn A s ρ := by
    let : IsFiniteMeasure (ρ.restrict s) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
    exact ⟨hA.aestronglyMeasurable, HasFiniteIntegral.of_bounded
      (Eventually.of_forall hAbound)⟩
  have hae : A =ᵐ[ρ] fun _ => c := by
    apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite hfinite
      (fun s _ hfin => integrableOn_const hfin.ne)
    intro s hs hfin
    let : IsFiniteMeasure (ρ.restrict s) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
    have hpre : (fun p : PositiveRadius × X => (p.1, F p)) ⁻¹' (s ×ˢ univ) =
        s ×ˢ univ := by ext p; simp
    have hres : MeasurePreserving (fun p : PositiveRadius × X => (p.1, F p))
        ((ρ.restrict s).prod ν) ((ρ.restrict s).prod ν) := by
      have h := hambient.restrict_preimage (hs.prod MeasurableSet.univ)
      rw [hpre, ← Measure.prod_restrict, Measure.restrict_univ] at h
      exact h
    have hi : Integrable (fun p : PositiveRadius × X => f (F p))
        ((ρ.restrict s).prod ν) :=
      ⟨(f.continuous.comp hF).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (Eventually.of_forall fun p => f.norm_coe_le_norm (F p))⟩
    have hj : Integrable (fun p : PositiveRadius × X => f p.2)
        ((ρ.restrict s).prod ν) :=
      ⟨(f.continuous.comp continuous_snd).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (Eventually.of_forall fun p => f.norm_coe_le_norm p.2)⟩
    have he : (∫ p, f (F p) ∂((ρ.restrict s).prod ν)) =
        ∫ p, f p.2 ∂((ρ.restrict s).prod ν) := by
      have hm := integral_map hres.measurable.aemeasurable
        (show AEStronglyMeasurable (fun p : PositiveRadius × X => f p.2)
          (Measure.map (fun p : PositiveRadius × X => (p.1, F p))
            ((ρ.restrict s).prod ν)) from by rw [hres.map_eq]; exact hj.1)
      rw [hres.map_eq] at hm
      exact hm.symm
    rw [integral_prod _ hi, integral_prod _ hj] at he
    exact he
  have heq : A = fun _ => c := eq_of_ae_eq hae hA continuous_const
  calc
    _ = A r := integral_map hFr.measurable.aemeasurable f.continuous.aestronglyMeasurable
    _ = c := congrFun heq r

theorem measurePreserving_cubicEnergyShell
    (ν : Measure X) [IsProbabilityMeasure ν]
    (F : PositiveRadius × X → X) (hF : Continuous F)
    (hambient : MeasurePreserving (fun p : PositiveRadius × X => (p.1, F p))
      ((Measure.volumeIoiPow 3).prod ν) ((Measure.volumeIoiPow 3).prod ν))
    (r : PositiveRadius) : MeasurePreserving (fun x => F (r, x)) ν ν :=
  measurePreserving_energyShell ν (Measure.volumeIoiPow 3) F hF hambient r

end
end PositiveEinsteinFour.Geometry
end


section

/-! The reconstruction direction of polar volume. It turns the spherical
probability and cubic radial density into actual Euclidean fiber volume,
including the null origin. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

noncomputable section

theorem euclideanPolarReconstruction_measurePreserving :
    MeasurePreserving euclideanPolarReconstruction
      ((polarAngularMass • sphereMeasure).prod (Measure.volumeIoiPow 3)) volume := by
  have hforward : MeasurePreserving euclideanPolarHomeomorph.toMeasurableEquiv
      ((volume : Measure FourSpace).comap Subtype.val)
      ((polarAngularMass • sphereMeasure).prod (Measure.volumeIoiPow 3)) :=
    euclideanPolarCoordinates_measurePreserving
  have hback := hforward.symm euclideanPolarHomeomorph.toMeasurableEquiv
  have hcoe : MeasurePreserving (Subtype.val : ({0}ᶜ : Set FourSpace) → FourSpace)
      ((volume : Measure FourSpace).comap Subtype.val) volume := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe (measurableSet_singleton 0).compl]
    exact Measure.restrict_eq_self_of_ae_mem ((volume : Measure FourSpace).ae_ne 0)
  exact hcoe.comp hback

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth covariant fields in centered coordinates. This supplies the
one-form fields used by the degree-two de Rham complex. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {n : ℕ}

theorem covariantFieldCoordinates_center (T : M → CovariantCoordinates n) (x : M) :
    covariantFieldCoordinates T x (chartAt FourSpace x x) = T x := by
  unfold covariantFieldCoordinates
  rw [chartInverseMatrix_center, frameTensor_one,
    (chartAt FourSpace x).left_inv (mem_chart_source FourSpace x)]

def smoothTwoFormCovariantField {o : FrameOrientation g} (u : smoothTwoForms o) :
    smoothCovariantFields M 2 :=
  ⟨twoFormTensorAt o u.val, fun c z hz a => u.property.coordinates_contDiffAt c z hz a⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reconstruction of actual smooth two-form fields from compatible
alternating coordinate tensors. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormFromCoordinates (o : FrameOrientation g)
    (T : M → FourSpace → CovariantCoordinates 2) : M → TwoFormFour :=
  fun x => twoFormExtract (twoTensorMatrixLinear
    (frameTensor (o.frame x).matrix (T x (chartAt FourSpace x x))))

theorem twoFormFromCoordinates_tensorAt (T : M → FourSpace → CovariantCoordinates 2)
    (hT : ∀ c z, z ∈ (chartAt FourSpace c).target → ∀ i j, T c z ![j,i] = -T c z ![i,j])
    (x : M) : twoFormTensorAt o (twoFormFromCoordinates o T) x = T x (chartAt FourSpace x x) := by
  unfold twoFormTensorAt twoFormFromCoordinates
  rw [twoFormTensor_extract _ (twoTensor_frame_skew _ _
    (hT x _ (mem_chart_target FourSpace x))), ← frameTensor_mul,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (o.frame x).det_ne_zero), frameTensor_one]

theorem twoFormFromCoordinates_coordinates (T : M → FourSpace → CovariantCoordinates 2)
    (hT : ∀ c z, z ∈ (chartAt FourSpace c).target → ∀ i j, T c z ![j,i] = -T c z ![i,j])
    (ht : ∀ c d z, (hz : z ∈ (chartAt FourSpace c).target) →
      (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source →
      T c z = frameTensor (chartTransitionMatrix c d z) (T d (chartTransition c d z)))
    (c : M) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    twoFormCoordinates o (twoFormFromCoordinates o T) c z = T c z := by
  unfold twoFormCoordinates
  rw [twoFormFromCoordinates_tensorAt T hT]
  have h := ht c ((chartAt FourSpace c).symm z) z hz
    (mem_chart_source FourSpace ((chartAt FourSpace c).symm z))
  rw [chartTransitionMatrix_to_center c z hz] at h
  exact h.symm

theorem twoFormFromCoordinates_smooth (T : M → FourSpace → CovariantCoordinates 2)
    (hT : ∀ c z, z ∈ (chartAt FourSpace c).target → ∀ i j, T c z ![j,i] = -T c z ![i,j])
    (ht : ∀ c d z, (hz : z ∈ (chartAt FourSpace c).target) →
      (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source →
      T c z = frameTensor (chartTransitionMatrix c d z) (T d (chartTransition c d z)))
    (hsm : ∀ c z, z ∈ (chartAt FourSpace c).target →
      ∀ a : Fin 2 → Fin 4, ContDiffAt ℝ ∞ (fun w => T c w a) z) :
    TwoFormSmooth o (twoFormFromCoordinates o T) := by
  apply TwoFormSmooth.of_coordinates
  intro c z hz a
  have he : (fun w => twoFormCoordinates o (twoFormFromCoordinates o T) c w a) =ᶠ[𝓝 z]
      fun w => T c w a := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    exact congrFun (twoFormFromCoordinates_coordinates T hT ht c w hw) a
  exact (hsm c z hz a).congr_of_eventuallyEq he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linearity of the actual smooth two-form covariant derivative and energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormCoordinates_add (u v : M → TwoFormFour) (c : M) :
    twoFormCoordinates o (u + v) c =
      fun z => twoFormCoordinates o u c z + twoFormCoordinates o v c z := by
  have ht (a b : TwoFormFour) : twoFormTensor (a + b) = twoFormTensor a + twoFormTensor b :=
    twoFormTensorLinear.map_add a b
  funext z a
  simp only [twoFormCoordinates, twoFormTensorAt, Pi.add_apply, ht, frameTensor,
    Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem twoFormCoordinates_smul (r : ℝ) (u : M → TwoFormFour) (c : M) :
    twoFormCoordinates o (r • u) c = fun z => r • twoFormCoordinates o u c z := by
  have ht (a : TwoFormFour) : twoFormTensor (r • a) = r • twoFormTensor a :=
    twoFormTensorLinear.map_smul r a
  funext z a
  simp only [twoFormCoordinates, twoFormTensorAt, Pi.smul_apply, ht, frameTensor,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem twoFormCovariantCoordinates_add (u v : smoothTwoForms o) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    twoFormCovariantCoordinates o (u + v).val c z =
      twoFormCovariantCoordinates o u.val c z + twoFormCovariantCoordinates o v.val c z := by
  change covariantDerivative g c (twoFormCoordinates o (u.val + v.val) c) z = _
  rw [twoFormCoordinates_add]
  exact covariantDerivative_add g c _ _ z
    (fun a => (u.property.coordinates_contDiffAt c z hz a).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (fun a => (v.property.coordinates_contDiffAt c z hz a).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

theorem twoFormCovariantCoordinates_smul (r : ℝ) (u : M → TwoFormFour)
    (c : M) (z : FourSpace) :
    twoFormCovariantCoordinates o (r • u) c z = r • twoFormCovariantCoordinates o u c z := by
  unfold twoFormCovariantCoordinates
  rw [twoFormCoordinates_smul]
  funext a
  have hd (f : FourSpace → ℝ) (i : Fin 4) :
      partialDeriv (fun w => r * f w) i z = r * partialDeriv f i z := by
    change fderiv ℝ (r • f) z (coordinateVector i) = _
    rw [fderiv_const_smul_field]
    rfl
  simp only [covariantDerivative, Pi.smul_apply, smul_eq_mul, hd, mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem twoFormFramedCovariantDerivative_add (u v : smoothTwoForms o) (e : FrameBundle g) :
    twoFormFramedCovariantDerivative o (u + v).val e =
      twoFormFramedCovariantDerivative o u.val e + twoFormFramedCovariantDerivative o v.val e := by
  unfold twoFormFramedCovariantDerivative
  rw [twoFormCovariantCoordinates_add u v e.base _
    ((chartAt FourSpace e.base).map_source (mem_chart_source FourSpace e.base))]
  funext a
  exact frameTensor_add _ _ _ a

theorem twoFormFramedCovariantDerivative_smul (r : ℝ) (u : M → TwoFormFour)
    (e : FrameBundle g) :
    twoFormFramedCovariantDerivative o (r • u) e =
      r • twoFormFramedCovariantDerivative o u e := by
  unfold twoFormFramedCovariantDerivative
  rw [twoFormCovariantCoordinates_smul]
  funext a
  exact frameTensor_const_mul _ r _ a

end
end PositiveEinsteinFour.Geometry
end


section

/-! The chart-level measure identity for lowering a smooth orthonormal
frame. The base density and Euclidean fiber volume become cotangent
coordinate volume by the already proved fiber Jacobian formula. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory MeasureTheory.Measure
open scoped BigOperators Manifold ContDiff ENNReal

noncomputable section

local instance instIsProbabilityMeasureDirectionsSphereMeasure_1 : IsProbabilityMeasure Angular.sphereMeasure :=
  Angular.actual_sphereMeasure_probability

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartCoordinateMeasure (c : M) : Measure (ChartTarget c) :=
  Measure.comap Subtype.val (volume : Measure FourSpace)

instance chartCoordinateMeasure_sigmaFinite (c : M) :
    SigmaFinite (chartCoordinateMeasure c) := by
  apply SigmaFinite.of_map (chartCoordinateMeasure c) measurable_subtype_coe.aemeasurable
  change SigmaFinite (Measure.map Subtype.val (Measure.comap Subtype.val
    (volume : Measure FourSpace)))
  rw [map_comap_subtype_coe (chartAt FourSpace c).open_target.measurableSet]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def chartCotangentLowering (g : SmoothMetric M) (c : M)
    (p : ChartTarget c × FourSpace) : ChartTarget c × FourSpace :=
  (p.1, coordinateMomentum g c p.1 (chartGramMatrix g c 1 p.1) p.2)

theorem continuous_chartCotangentLowering (g : SmoothMetric M) (c : M) :
    Continuous (chartCotangentLowering g c) := by
  have hG (i j : Fin 4) :
      Continuous (fun x : ChartTarget c => metricInChart g c x i j) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (metricInChart_contDiffAt g c x x.property i j).continuousAt.comp
      continuous_subtype_val.continuousAt
  have hE (i j : Fin 4) :
      Continuous (fun x : ChartTarget c => chartGramMatrix g c 1 x i j) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (chartGramMatrix_contDiffAt g c 1 x x.property i j).continuousAt.comp
      continuous_subtype_val.continuousAt
  apply continuous_fst.prodMk
  change Continuous (fun p : ChartTarget c × FourSpace =>
    WithLp.toLp 2 (fun i => ∑ j,
      (∑ k, metricInChart g c p.1 i k * chartGramMatrix g c 1 p.1 k j) * p.2 j))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  apply Continuous.mul
  · apply continuous_finsetSum
    intro k _
    exact ((hG i k).comp continuous_fst).mul ((hE k j).comp continuous_fst)
  · exact (PiLp.continuous_apply 2 _ j).comp continuous_snd

theorem chartCotangentLowering_measurePreserving (g : SmoothMetric M) (c : M) :
    MeasurePreserving (chartCotangentLowering g c)
      (((chartCoordinateMeasure c).withDensity
        (fun x => ENNReal.ofReal (chartVolumeDensity g c x))).prod volume)
      ((chartCoordinateMeasure c).prod volume) := by
  have hm := (continuous_chartCotangentLowering g c).measurable
  have hd : Measurable (fun x : ChartTarget c =>
      ENNReal.ofReal (chartVolumeDensity g c x)) := by
    apply Continuous.measurable
    apply ENNReal.continuous_ofReal.comp
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (chartVolumeDensity_contDiffAt g c x x.property).continuousAt.comp
      continuous_subtype_val.continuousAt
  refine ⟨hm, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hm hA, Measure.prod_apply (hm hA), Measure.prod_apply hA,
    lintegral_withDensity_eq_lintegral_mul _ hd (measurable_measure_prodMk_left (hm hA))]
  apply lintegral_congr
  intro x
  have hp := coordinateMomentum_measurePreserving g c x x.property
    (chartGramMatrix g c 1 x) (chartGramMatrix_normalizes g c 1 (by simp) x)
  have he := congrArg (fun μ : Measure FourSpace => μ (Prod.mk x ⁻¹' A)) hp.map_eq
  rw [Measure.map_apply hp.measurable (measurable_prodMk_left hA),
    Measure.smul_apply, smul_eq_mul] at he
  exact he

/-- Base point, direction and positive radius as actual cotangent
coordinates, using the smooth Gram frame on the chart. -/
def chartPolarLowering (g : SmoothMetric M) (c : M)
    (p : ChartTarget c × (Angular.Directions × Set.Ioi (0 : ℝ))) :
    ChartTarget c × FourSpace :=
  chartCotangentLowering g c (p.1, euclideanPolarReconstruction p.2)

theorem chartPolarLowering_measurePreserving (g : SmoothMetric M) (c : M) :
    MeasurePreserving (chartPolarLowering g c)
      (((chartCoordinateMeasure c).withDensity
        (fun x => ENNReal.ofReal (chartVolumeDensity g c x))).prod
          ((polarAngularMass • Angular.sphereMeasure).prod (Measure.volumeIoiPow 3)))
      ((chartCoordinateMeasure c).prod volume) :=
  (chartCotangentLowering_measurePreserving g c).comp
    ((MeasurePreserving.id _).prod euclideanPolarReconstruction_measurePreserving)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The existing Levi-Civita coordinate derivative acts on actual smooth
covariant fields; no chart or derivative compatibility is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {n : ℕ}

def smoothCovariantDerivative (g : SmoothMetric M) (T : smoothCovariantFields M n) :
    smoothCovariantFields M (n + 1) :=
  ⟨covariantFieldDerivative g T.val, T.property.derivative⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual orthonormal frame components determine a covariant field. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {n : ℕ}

theorem covariantField_eq_of_framed (T U : M → CovariantCoordinates n)
    (h : ∀ e : FrameBundle g, covariantFieldFramed g T e = covariantFieldFramed g U e) :
    T = U := by
  funext x
  let e := frameAt g x
  have he := h e
  rw [covariantFieldFramed_eq, covariantFieldFramed_eq] at he
  change frameTensor e.frame.matrix (T x) = frameTensor e.frame.matrix (U x) at he
  have hi := congrArg (frameTensor e.frame.matrix⁻¹) he
  rw [← frameTensor_mul, ← frameTensor_mul,
    Matrix.mul_nonsing_inv e.frame.matrix
      (isUnit_iff_ne_zero.mpr e.frame.det_ne_zero), frameTensor_one, frameTensor_one] at hi
  exact hi

theorem covariantFieldFramed_add (T U : M → CovariantCoordinates n) (e : FrameBundle g) :
    covariantFieldFramed g (T + U) e = covariantFieldFramed g T e + covariantFieldFramed g U e := by
  simp only [covariantFieldFramed_eq, Pi.add_apply]
  funext a
  exact frameTensor_add _ _ _ a

theorem covariantFieldFramed_smul (r : ℝ) (T : M → CovariantCoordinates n) (e : FrameBundle g) :
    covariantFieldFramed g (r • T) e = r • covariantFieldFramed g T e := by
  simp only [covariantFieldFramed_eq, Pi.smul_apply]
  funext a
  exact frameTensor_const_mul _ _ _ a

end
end PositiveEinsteinFour.Geometry
end


section

/-! Alternating smooth covariant fields give the existing actual
six-coordinate two-form sections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def covariantFieldTwoForm (T : smoothCovariantFields M 2) (hT : CovariantTwoFormSkew T.val) :
    smoothTwoForms o :=
  ⟨twoFormFromCoordinates o (covariantFieldCoordinates T.val),
    twoFormFromCoordinates_smooth _ (fun c z _ => hT.coordinates c z)
      (covariantFieldCoordinates_transition T.val) T.property⟩

theorem covariantFieldTwoForm_coordinates (T : smoothCovariantFields M 2)
    (hT : CovariantTwoFormSkew T.val) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    twoFormCoordinates o (covariantFieldTwoForm (o := o) T hT).val c z =
      covariantFieldCoordinates T.val c z :=
  twoFormFromCoordinates_coordinates _ (fun c z _ => hT.coordinates c z)
    (covariantFieldCoordinates_transition T.val) c z hz

theorem covariantFieldTwoForm_framed (T : smoothCovariantFields M 2)
    (hT : CovariantTwoFormSkew T.val) (e : FrameBundle g) :
    twoFormFramedValue o (covariantFieldTwoForm (o := o) T hT).val e =
      covariantFieldFramed g T.val e := by
  unfold twoFormFramedValue
  rw [covariantFieldTwoForm_coordinates T hT e.base _ (mem_chart_target FourSpace e.base)]
  rfl

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

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

/-- Base averages for the constructed frame measure are precisely the
normalized Riemannian averages, as used in the Poisson equation. -/
theorem canonicalFrameMeasure_integral_base (g : SmoothMetric M)
    (o : FrameOrientation g) (A : M → ℝ) (hA : Integrable A (normalizedVolume g)) :
    (∫ e : FrameBundle g, A e.base ∂canonicalFrameMeasure g o) =
      ∫ x, A x ∂normalizedVolume g := by
  have hb := canonicalFrameMeasure_base g o
  have ha : AEStronglyMeasurable A
      (Measure.map FrameBundle.base (canonicalFrameMeasure g o)) := by
    rw [hb.map_eq]
    exact hA.aestronglyMeasurable
  have hi := integral_map hb.measurable.aemeasurable ha
  rw [hb.map_eq] at hi
  exact hi.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exterior derivative from smooth one-forms to two-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

theorem twoCovariantAlternation_apply (T : CovariantCoordinates 2) (i j : Fin 4) :
    twoCovariantAlternation T ![i,j] = T ![i,j] - T ![j,i] := by
  have he : ![i,j] ∘ Equiv.swap (0 : Fin 2) 1 = ![j,i] := by
    ext k
    fin_cases k <;> simp
  exact congrArg (T ![i,j] - ·) (congrArg T he)

theorem twoCovariantAlternation_skew (T : CovariantCoordinates 2) (i j : Fin 4) :
    twoCovariantAlternation T ![j,i] = -twoCovariantAlternation T ![i,j] := by
  rw [twoCovariantAlternation_apply, twoCovariantAlternation_apply]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothCovariantAlternation (T : smoothCovariantFields M 2) : smoothCovariantFields M 2 :=
  ⟨fun x => twoCovariantAlternation (T.val x), by
    intro c z hz a
    have h := (T.property c z hz a).sub (T.property c z hz (a ∘ Equiv.swap 0 1))
    apply h.congr_of_eventuallyEq
    filter_upwards [] with w
    exact congrFun (twoCovariantAlternation_frame (chartInverseMatrix c w) (T.val _)) a⟩

def smoothOneFormExterior (u : smoothCovariantFields M 1) : smoothTwoForms o :=
  covariantFieldTwoForm (o := o) (smoothCovariantAlternation (smoothCovariantDerivative g u))
    (fun _x i j => twoCovariantAlternation_skew _ i j)

theorem smoothOneFormExterior_framed (u : smoothCovariantFields M 1)
    (e : FrameBundle g) (i j : Fin 4) :
    twoFormFramedValue o (smoothOneFormExterior (o := o) u).val e ![i,j] =
      covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,j] -
        covariantFieldFramed g (covariantFieldDerivative g u.val) e ![j,i] := by
  apply Eq.trans (congrFun (covariantFieldTwoForm_framed (o := o)
    (smoothCovariantAlternation (smoothCovariantDerivative g u))
      (fun _x p q => twoCovariantAlternation_skew _ p q) e) ![i,j])
  simp only [covariantFieldFramed_eq]
  exact (congrFun (twoCovariantAlternation_frame e.frame.matrix
    (covariantFieldDerivative g u.val e.base)) ![i,j]).trans
      (twoCovariantAlternation_apply _ i j)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linearity of the actual exterior derivative on smooth one-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothOneFormExterior_apply (u : smoothCovariantFields M 1) (x : M) :
    (smoothOneFormExterior (o := o) u).val x =
      twoFormExtract (twoTensorMatrixLinear (frameTensor (o.frame x).matrix
        (twoCovariantAlternation (covariantFieldDerivative g u.val x)))) := by
  change twoFormExtract (twoTensorMatrixLinear (frameTensor (o.frame x).matrix
    (covariantFieldCoordinates
      (smoothCovariantAlternation (smoothCovariantDerivative g u)).val x
        (chartAt FourSpace x x)))) = _
  rw [covariantFieldCoordinates_center]
  rfl

theorem smoothOneFormExterior_add (u v : smoothCovariantFields M 1) :
    smoothOneFormExterior (o := o) (u + v) =
      smoothOneFormExterior u + smoothOneFormExterior v := by
  apply Subtype.ext
  funext x
  simp only [smoothOneFormExterior_apply, Submodule.coe_add, Pi.add_apply]
  have hd : covariantFieldDerivative g (u.val + v.val) x =
      covariantFieldDerivative g u.val x + covariantFieldDerivative g v.val x :=
    congrFun (covariantFieldDerivative_add (g := g) u v) x
  rw [hd]
  change twoFormExtractLinear (twoTensorMatrixLinear (frameTensor _
    (twoCovariantAlternationLinear (_ + _)))) = _
  rw [map_add]
  have he (E : Mat4) (T U : CovariantCoordinates 2) :
      frameTensor E (T + U) = frameTensor E T + frameTensor E U := by
    funext a
    exact frameTensor_add E T U a
  rw [he, map_add, map_add]
  rfl

theorem smoothOneFormExterior_smul (r : ℝ) (u : smoothCovariantFields M 1) :
    smoothOneFormExterior (o := o) (r • u) = r • smoothOneFormExterior u := by
  apply Subtype.ext
  funext x
  simp only [smoothOneFormExterior_apply, Submodule.coe_smul, Pi.smul_apply]
  have hd : covariantFieldDerivative g (r • u.val) x =
      r • covariantFieldDerivative g u.val x :=
    congrFun (covariantFieldDerivative_smul (g := g) r u) x
  rw [hd]
  change twoFormExtractLinear (twoTensorMatrixLinear (frameTensor _
    (twoCovariantAlternationLinear (r • _)))) = _
  rw [map_smul]
  have he (E : Mat4) (T : CovariantCoordinates 2) :
      frameTensor E (r • T) = r • frameTensor E T := by
    funext a
    exact frameTensor_const_mul E r T a
  rw [he, map_smul, map_smul]
  rfl

def smoothOneFormExteriorLinear : smoothCovariantFields M 1 →ₗ[ℝ] smoothTwoForms o where
  toFun := smoothOneFormExterior
  map_add' := smoothOneFormExterior_add
  map_smul' := smoothOneFormExterior_smul

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact group of oriented normal-frame rotations. Its elements
fix the first frame direction, so its action commutes with the actual
first parallel flow. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem isClosed_normalRotationSubgroup :
    IsClosed (normalRotationSubgroup : Set OrientedOrthogonalFour) := by
  change IsClosed {Q : OrientedOrthogonalFour |
    orientedDirection Q firstDirection = firstDirection}
  have hp : Continuous (fun Q : OrientedOrthogonalFour => (Q, firstDirection)) :=
    continuous_id.prodMk continuous_const
  have hf : Continuous ((fun p : OrientedOrthogonalFour × Directions =>
      orientedDirection p.1 p.2) ∘ (fun Q : OrientedOrthogonalFour => (Q, firstDirection))) :=
    continuous_orientedDirection.comp hp
  exact isClosed_eq hf continuous_const

instance instCompactSpaceSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFourSubgroupNormalFrameRotation : CompactSpace NormalFrameRotation :=
  isCompact_iff_compactSpace.mp isClosed_normalRotationSubgroup.isCompact

instance instSecondCountableTopologySubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFourSubgroupNormalFrameRotation : SecondCountableTopology NormalFrameRotation :=
  (show Topology.IsEmbedding (Subtype.val : NormalFrameRotation → OrientedOrthogonalFour)
    from Topology.IsEmbedding.subtypeVal).secondCountableTopology

def normalFrameHaar : Measure NormalFrameRotation := Measure.haarMeasure ⊤

instance instIsProbabilityMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFourSubgroupNormalFrameRotationNormalFrameHaar : IsProbabilityMeasure normalFrameHaar := by
  constructor
  exact Measure.haarMeasure_self (K₀ := ⊤)

instance instIsHaarMeasureSubtypeMatrixFinOfNatNatRealMemSubmonoidOrientedOrthogonalFourSubgroupNormalFrameRotationNormalFrameHaar : Measure.IsHaarMeasure normalFrameHaar :=
  Measure.isHaarMeasure_haarMeasure ⊤

theorem normalFrameHaar_left (Q : NormalFrameRotation) :
    MeasurePreserving (fun P => Q * P) normalFrameHaar normalFrameHaar :=
  measurePreserving_mul_left normalFrameHaar Q

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem continuous_normalFrameRotate (g : SmoothMetric M) :
    Continuous (fun p : FrameBundle g × NormalFrameRotation => normalFrameRotate p.1 p.2) :=
  (continuous_frameRotate g).comp (continuous_fst.prodMk
    (continuous_orientedToOrthogonal.comp (continuous_subtype_val.comp continuous_snd)))

theorem normalFrameRotate_mul {g : SmoothMetric M} (e : FrameBundle g)
    (P Q : NormalFrameRotation) :
    normalFrameRotate (normalFrameRotate e P) Q = normalFrameRotate e (P * Q) :=
  frameRotate_mul e P.val Q.val

theorem normalFrameRotate_one {g : SmoothMetric M} (e : FrameBundle g) :
    normalFrameRotate e 1 = e := frameRotate_one e

def normalFrameHomeomorph (g : SmoothMetric M) (Q : NormalFrameRotation) :
    FrameBundle g ≃ₜ FrameBundle g where
  toFun e := normalFrameRotate e Q
  invFun e := normalFrameRotate e Q⁻¹
  left_inv e := by
    change normalFrameRotate (normalFrameRotate e Q) Q⁻¹ = e
    rw [normalFrameRotate_mul, mul_inv_cancel, normalFrameRotate_one]
  right_inv e := by
    change normalFrameRotate (normalFrameRotate e Q⁻¹) Q = e
    rw [normalFrameRotate_mul, inv_mul_cancel, normalFrameRotate_one]
  continuous_toFun := (continuous_normalFrameRotate g).comp
    (continuous_id.prodMk continuous_const)
  continuous_invFun := (continuous_normalFrameRotate g).comp
    (continuous_id.prodMk continuous_const)

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

theorem canonicalFrameMeasure_normalFrameRotate (g : SmoothMetric M)
    (o : FrameOrientation g) (Q : NormalFrameRotation) :
    MeasurePreserving (fun e : FrameBundle g => normalFrameRotate e Q)
      (canonicalFrameMeasure g o) (canonicalFrameMeasure g o) :=
  canonicalFrameMeasure_rotate g o Q.val

end
end PositiveEinsteinFour.Geometry
end


section

/-! A fixed oriented change of frame conjugates any distinguished
direction to the first. Frame-volume preservation therefore reduces
to the first, geodesic, flow. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem parallelFrameCurveAt_directionChange (g : SmoothMetric M)
    (γ : ℝ → FrameBundle g) (k l : Fin 4) (Q : OrthogonalFour)
    (hQ : ∀ r, Q.val r l = if r = k then 1 else 0) (t : ℝ)
    (h : ParallelFrameCurveAt g γ k t) :
    ParallelFrameCurveAt g (fun s => (γ s).rotate Q) l t := by
  let c := (γ t).base
  let E (s : ℝ) := frameChartMatrix g c (γ s)
  let C : Mat4 := ∑ r, E t r k • connectionMatrix g c r
    (chartAt FourSpace c (γ t).base)
  have hcol (r : Fin 4) : frameChartMatrix g c ((γ t).rotate Q) r l = E t r k := by
    rw [frameChartMatrix_rotate]
    simp only [Matrix.mul_apply, hQ, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, E]
  constructor
  · change HasDerivAt (fun s => chartAt FourSpace c (γ s).base)
      (WithLp.toLp 2 (fun r => frameChartMatrix g c ((γ t).rotate Q) r l)) t
    simp_rw [hcol]
    exact h.velocity
  · intro i j
    have hs := HasDerivAt.fun_sum (fun a (_ : a ∈ Finset.univ) =>
      (h.parallel i a).mul_const (Q.val a j))
    have hp : HasDerivAt (fun s => (E s * Q.val) i j)
        ((-(C * E t) * Q.val) i j) t := by
      simpa only [E, C, Matrix.mul_apply, Matrix.neg_apply] using hs
    have he : (-((∑ r, frameChartMatrix g c ((γ t).rotate Q) r l •
        connectionMatrix g c r (chartAt FourSpace c (γ t).base)) *
          frameChartMatrix g c ((γ t).rotate Q)) i j) =
        (-(C * E t) * Q.val) i j := by
      simp_rw [hcol]
      rw [frameChartMatrix_rotate]
      change (-(C * (E t * Q.val))) i j = (-(C * E t) * Q.val) i j
      rw [Matrix.neg_mul, Matrix.mul_assoc]
    change HasDerivAt (fun s => frameChartMatrix g c ((γ s).rotate Q) i j)
      (-((∑ r, frameChartMatrix g c ((γ t).rotate Q) r l •
        connectionMatrix g c r (chartAt FourSpace c (γ t).base)) *
          frameChartMatrix g c ((γ t).rotate Q)) i j) t
    rw [he]
    have hf : (fun s => frameChartMatrix g c ((γ s).rotate Q) i j) =
        fun s => (E s * Q.val) i j := by
      funext s
      exact congrFun (congrFun (frameChartMatrix_rotate g c (γ s) Q) i) j
    rw [hf]
    exact hp

theorem parallelFrameFlowMap_directionChange [T2Space M] [CompactSpace M]
    (g : SmoothMetric M) (k l : Fin 4) (Q : OrthogonalFour)
    (hQ : ∀ r, Q.val r l = if r = k then 1 else 0) (t : ℝ) (e : FrameBundle g) :
    (parallelFrameFlowMap g k t e).rotate Q =
      parallelFrameFlowMap g l t (e.rotate Q) := by
  let γ : ℝ → FrameBundle g := fun s => (parallelFrameFlowMap g k s e).rotate Q
  let η : ℝ → FrameBundle g := fun s => parallelFrameFlowMap g l s (e.rotate Q)
  have hγc : Continuous γ := (continuous_frameRotate g).comp
    ((parallelFrameFlowMap_curve_continuous g k e).prodMk continuous_const)
  have hηc : Continuous η := parallelFrameFlowMap_curve_continuous g l (e.rotate Q)
  have hγ (s : ℝ) : ParallelFrameCurveAt g γ l s :=
    parallelFrameCurveAt_directionChange g (fun u => parallelFrameFlowMap g k u e)
      k l Q hQ s (parallelFrameFlowMap_primitive g k e s)
  have hη (s : ℝ) : ParallelFrameCurveAt g η l s :=
    parallelFrameFlowMap_primitive g l (e.rotate Q) s
  have h0 : γ 0 = η 0 := by simp only [γ, η, parallelFrameFlowMap_zero]
  exact congrFun (intrinsic_parallelFrame_unique_global g γ η l hγc hηc hγ hη h0) t

def coordinateDirection (k : Fin 4) : Directions :=
  ⟨EuclideanSpace.single k 1, by simp⟩

theorem coordinateDirection_apply (k r : Fin 4) :
    (coordinateDirection k).val r = if r = k then 1 else 0 := by
  simp [coordinateDirection, eq_comm]

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

theorem parallelFrameFlowMap_preserves_of_first (g : SmoothMetric M)
    (o : FrameOrientation g)
    (hfirst : ∀ t, MeasurePreserving (parallelFrameFlowMap g 0 t)
      (canonicalFrameMeasure g o) (canonicalFrameMeasure g o)) (k : Fin 4) (t : ℝ) :
    MeasurePreserving (parallelFrameFlowMap g k t)
      (canonicalFrameMeasure g o) (canonicalFrameMeasure g o) := by
  let Q := directionOrientedMatrix (coordinateDirection k)
  have hQ (r : Fin 4) : (orientedToOrthogonal Q).val r 0 = if r = k then 1 else 0 := by
    exact (directionFrameMatrix_zero (coordinateDirection k) r).trans
      (coordinateDirection_apply k r)
  have h := (canonicalFrameMeasure_rotate g o Q⁻¹).comp
    ((hfirst t).comp (canonicalFrameMeasure_rotate g o Q))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext e
  change parallelFrameFlowMap g k t e =
    (parallelFrameFlowMap g 0 t (e.rotate (orientedToOrthogonal Q))).rotate
      (orientedToOrthogonal Q⁻¹)
  rw [← parallelFrameFlowMap_directionChange g k 0 (orientedToOrthogonal Q) hQ,
    frameRotate_mul, mul_inv_cancel, frameRotate_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Complete horizontal curves give parallel-frame calculus. Preservation of
the specified measure is the Brin--Karcher hypothesis, Section 1, p. 275. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem actualParallelMetricData_zero (g : SmoothMetric M)
    (μ : Measure (FrameBundle g))
    (hpres : ∀ k t, MeasurePreserving (parallelFrameFlowMap g k t) μ μ)
    (hRic : RicciThree g) (k : Fin 4) (e : FrameBundle g) :
    ((actualParallelMetricData g μ hpres hRic).flow k).map 0 e = e :=
  parallelFrameFlowMap_zero g k e

end
end PositiveEinsteinFour.Geometry
end


section

/-! Averaging over the actual normal-frame rotations. This is the
fiber operation needed to lift geodesic measure preservation to the
full oriented-frame measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

def normalIntegralLinear : C(NormalFrameRotation, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ Q, f Q ∂normalFrameHaar
  map_add' f h := integral_add
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  map_smul' a f := integral_const_mul a (fun Q => f Q)

def normalIntegralCLM : C(NormalFrameRotation, ℝ) →L[ℝ] ℝ :=
  normalIntegralLinear.mkContinuous 1 (fun f => by
    change ‖∫ Q, f Q ∂normalFrameHaar‖ ≤ 1 * ‖f‖
    simpa using norm_integral_le_of_norm_le_const (μ := normalFrameHaar)
      (Filter.Eventually.of_forall (fun Q => f.norm_coe_le_norm Q)))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def normalFrameAverage (f : FrameBundle g → ℝ) (e : FrameBundle g) : ℝ :=
  ∫ Q, f (normalFrameRotate e Q) ∂normalFrameHaar

theorem normalFrameAverage_rotate (f : FrameBundle g → ℝ)
    (e : FrameBundle g) (P : NormalFrameRotation) :
    normalFrameAverage f (normalFrameRotate e P) = normalFrameAverage f e := by
  unfold normalFrameAverage
  simp_rw [normalFrameRotate_mul]
  exact (normalFrameHaar_left P).integral_comp
    (Homeomorph.mulLeft P).measurableEmbedding (fun Q => f (normalFrameRotate e Q))

/-- The normal average depends only on the base point, first unit vector
and orientation, not on the chosen three-vector normal frame. -/
theorem normalFrameAverage_same_first (F : FrameBundle g → ℝ) {c : M}
    (e f : OrthonormalFrame g c) (hdet : 0 < e.matrix.det * f.matrix.det)
    (hfirst : e.vector 0 = f.vector 0) :
    normalFrameAverage F (⟨c, e⟩ : FrameBundle g) =
      normalFrameAverage F (⟨c, f⟩ : FrameBundle g) := by
  have h := normalFrameAverage_rotate F (⟨c, e⟩ : FrameBundle g)
    (normalFrameChange e f hdet hfirst)
  rw [normalFrameRotate_change] at h
  exact h.symm

theorem normalFrameAverage_parallel [T2Space M] [CompactSpace M]
    (f : FrameBundle g → ℝ) (t : ℝ) (e : FrameBundle g) :
    normalFrameAverage (fun a => f (parallelFrameFlowMap g 0 t a)) e =
      normalFrameAverage f (parallelFrameFlowMap g 0 t e) := by
  unfold normalFrameAverage
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun Q => congrArg f
    (parallelFrameFlowMap_normalFrameRotate g t e Q).symm)

theorem continuous_normalFrameAverage (f : FrameBundle g → ℝ) (hf : Continuous f) :
    Continuous (normalFrameAverage f) := by
  let F : C(FrameBundle g × NormalFrameRotation, ℝ) :=
    ⟨fun p => f (normalFrameRotate p.1 p.2), hf.comp (continuous_normalFrameRotate g)⟩
  exact normalIntegralCLM.continuous.comp F.curry.continuous

variable [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

/-- Normal-fiber averaging preserves the integral against the actual
canonical oriented-frame probability. -/
theorem integral_normalFrameAverage (o : FrameOrientation g)
    (f : FrameBundle g → ℝ) (hf : Continuous f) :
    (∫ e, normalFrameAverage f e ∂canonicalFrameMeasure g o) =
      ∫ e, f e ∂canonicalFrameMeasure g o := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hcont : Continuous (fun p : FrameBundle g × NormalFrameRotation =>
      f (normalFrameRotate p.1 p.2)) := hf.comp (continuous_normalFrameRotate g)
  have hint : Integrable (fun p : FrameBundle g × NormalFrameRotation =>
      f (normalFrameRotate p.1 p.2)) ((canonicalFrameMeasure g o).prod normalFrameHaar) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold normalFrameAverage
  rw [integral_integral_swap hint]
  have hinner (Q : NormalFrameRotation) :
      (∫ e, f (normalFrameRotate e Q) ∂canonicalFrameMeasure g o) =
        ∫ e, f e ∂canonicalFrameMeasure g o :=
    (canonicalFrameMeasure_normalFrameRotate g o Q).integral_comp
      (normalFrameHomeomorph g Q).measurableEmbedding f
  simp_rw [hinner]
  simp

/-- A transported frame test function has the same integral as its normal-fiber average.
Together with `normalFrameAverage_same_first`, this gives an integral on the unit tangent bundle. -/
theorem integral_parallel_eq_normalAverage (o : FrameOrientation g)
    (f : FrameBundle g → ℝ) (hf : Continuous f) (t : ℝ) :
    (∫ e, f (parallelFrameFlowMap g 0 t e) ∂canonicalFrameMeasure g o) =
      ∫ e, normalFrameAverage f (parallelFrameFlowMap g 0 t e)
        ∂canonicalFrameMeasure g o := by
  calc
    _ = ∫ e, normalFrameAverage (fun a => f (parallelFrameFlowMap g 0 t a)) e
        ∂canonicalFrameMeasure g o :=
      (integral_normalFrameAverage o _
        (hf.comp (parallelFrameFlowMap_continuous_slice g 0 t))).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall
      (normalFrameAverage_parallel f t))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Intrinsic unit tangent vectors and the actual first-vector projection
from oriented frames. Every unit vector has a positive orthonormal
completion, constructed with the explicit quaternionic completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular Bundle MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

instance instMeasurableSpaceUnitTangentBundle (g : SmoothMetric M) : MeasurableSpace (UnitTangentBundle g) :=
  borel (UnitTangentBundle g)

instance instBorelSpaceUnitTangentBundle (g : SmoothMetric M) : BorelSpace (UnitTangentBundle g) := ⟨rfl⟩

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

def canonicalUnitTangentMeasure (g : SmoothMetric M) (o : FrameOrientation g) :
    Measure (UnitTangentBundle g) :=
  Measure.map unitTangentOfFrame (canonicalFrameMeasure g o)

instance canonicalUnitTangentMeasure_probability (g : SmoothMetric M) (o : FrameOrientation g) :
    IsProbabilityMeasure (canonicalUnitTangentMeasure g o) :=
  (Measure.isProbabilityMeasure_map_iff
    (continuous_unitTangentOfFrame g).measurable.aemeasurable).mpr inferInstance

end
end PositiveEinsteinFour.Geometry
end


section

/-! The canonical unit tangent measure is normalized base volume times
spherical probability in every measurable positive reference frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance instIsProbabilityMeasureDirectionsSphereMeasure_2 : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability

theorem orientedDirection_first_apply (Q : OrientedOrthogonalFour) (i : Fin 4) :
    (orientedDirection Q firstDirection).val i = Q.val i 0 := by
  change (∑ j, Q.val i j * firstDirection.val j) = Q.val i 0
  simp only [firstDirection_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

theorem orientedDirection_first_measurePreserving :
    MeasurePreserving (fun Q => orientedDirection Q firstDirection)
      orientedFrameHaar sphereMeasure := by
  have hp : Continuous (fun Q : OrientedOrthogonalFour => (Q, firstDirection)) :=
    continuous_id.prodMk continuous_const
  have ha : Continuous ((fun p : OrientedOrthogonalFour × Directions =>
      orientedDirection p.1 p.2) ∘ (fun Q : OrientedOrthogonalFour => (Q, firstDirection))) :=
    continuous_orientedDirection.comp hp
  have hc : Continuous (fun Q => orientedDirection Q firstDirection) := by
    simpa only [Function.comp_def] using ha
  refine ⟨hc.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hc.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  exact haar_integral_direction f f.continuous firstDirection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem unitTangentTurn_first (e : FrameBundle g) (Q : OrientedOrthogonalFour) :
    unitTangentTurn e (orientedDirection Q firstDirection) =
      unitTangentOfFrame (e.rotate (orientedToOrthogonal Q)) := by
  apply unitTangent_ext
  · rfl
  · change (e.frame.turn (orientedDirection Q firstDirection)).vector 0 =
      (e.frame.rotate (orientedToOrthogonal Q)).vector 0
    rw [OrthonormalFrame.turn_first]
    ext i
    change (∑ j, e.frame.matrix i j * (orientedDirection Q firstDirection).val j) =
      ∑ j, e.frame.matrix i j * Q.val j 0
    simp only [orientedDirection_first_apply]

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

/-- Spherical disintegration is valid in any measurable positive frame
section, including sections obtained by switching to a local Gram frame. -/
theorem canonicalUnitTangentMeasure_eq_section (g : SmoothMetric M) (o : FrameOrientation g)
    (s : M → FrameBundle g) (hs : Measurable s)
    (hbase : ∀ x, (s x).base = x) (hpos : ∀ x, s x ∈ o.positive) :
    canonicalUnitTangentMeasure g o =
      Measure.map (fun p : M × Directions => unitTangentTurn (s p.1) p.2)
        ((normalizedVolume g).prod sphereMeasure) := by
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  have hm : Measurable (fun p : M × Directions => unitTangentTurn (s p.1) p.2) :=
    continuous_unitTangentTurn.measurable.comp ((hs.comp measurable_fst).prodMk measurable_snd)
  have hQ : Measurable (fun p : M × OrientedOrthogonalFour =>
      (s p.1).rotate (orientedToOrthogonal p.2)) :=
    (continuous_frameRotate g).measurable.comp ((hs.comp measurable_fst).prodMk
      (continuous_orientedToOrthogonal.measurable.comp measurable_snd))
  have hp := (MeasurePreserving.id (normalizedVolume g)).prod
    orientedDirection_first_measurePreserving
  change Measure.map unitTangentOfFrame (canonicalFrameMeasure g o) = _
  rw [canonicalFrameMeasure_eq_section g o s hs hbase hpos,
    Measure.map_map (continuous_unitTangentOfFrame g).measurable hQ,
    ← hp.map_eq, Measure.map_map hm hp.measurable]
  congr 1
  funext p
  exact (unitTangentTurn_first (s p.1) p.2).symm

theorem canonicalUnitTangentMeasure_eq_spherical (g : SmoothMetric M) (o : FrameOrientation g) :
    canonicalUnitTangentMeasure g o =
      Measure.map (fun p : M × Directions =>
        unitTangentTurn (positiveFrameSection g o p.1) p.2)
        ((normalizedVolume g).prod sphereMeasure) :=
  canonicalUnitTangentMeasure_eq_section g o (positiveFrameSection g o)
    (measurable_positiveFrameSection g o) (positiveFrameSection_base g o)
    (positiveFrameSection_positive g o)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The unit tangent fiber measure is independent of every orthonormal
reference frame, including its orientation. This allows the local Gram
frame in cotangent coordinates to compute the canonical spherical measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance instIsProbabilityMeasureDirectionsSphereMeasure_3 : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def unitTangentFiberMeasure (e : FrameBundle g) : Measure (UnitTangentBundle g) :=
  Measure.map (unitTangentTurn e) sphereMeasure

theorem orthogonalDirection_value (P : Mat4) (hP : Pᵀ * P = 1)
    (q : Directions) : (orthogonalDirection P hP q).val =
      WithLp.toLp 2 (P *ᵥ WithLp.ofLp q.val) := rfl

theorem frame_map_change {c : M} (e f : OrthonormalFrame g c)
    (Q : Mat4) (hQ : e.matrix * Q = f.matrix) (v : FourSpace) :
    e.map (WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v)) = f.map v := by
  ext i
  change (e.matrix *ᵥ (Q *ᵥ WithLp.ofLp v)) i = (f.matrix *ᵥ WithLp.ofLp v) i
  rw [Matrix.mulVec_mulVec, hQ]

theorem unitTangentTurn_change_matrix {c : M} (e f : OrthonormalFrame g c)
    (Q : Mat4) (hQ : Qᵀ * Q = 1) (hEF : e.matrix * Q = f.matrix) (q : Directions) :
    unitTangentTurn (⟨c, e⟩ : FrameBundle g) (orthogonalDirection Q hQ q) =
      unitTangentTurn (⟨c, f⟩ : FrameBundle g) q := by
  apply unitTangentRealization_injective g
  change (⟨c, (e.turn (orthogonalDirection Q hQ q)).vector 0⟩ : TangentBundle I4 M) =
    ⟨c, (f.turn q).vector 0⟩
  have hv : (e.turn (orthogonalDirection Q hQ q)).vector 0 = (f.turn q).vector 0 :=
    (e.turn_first _).trans
      ((congrArg e.map (orthogonalDirection_value Q hQ q)).trans
        ((frame_map_change e f Q hEF q.val).trans (f.turn_first q).symm))
  exact congrArg (fun v : TangentSpace I4 c => (⟨c, v⟩ : TangentBundle I4 M)) hv

theorem unitTangentTurn_change {c : M} (e f : OrthonormalFrame g c) (q : Directions) :
    unitTangentTurn (⟨c, e⟩ : FrameBundle g)
      (orthogonalDirection (e.changeMatrix f) (e.changeMatrix_orthogonal f) q) =
      unitTangentTurn (⟨c, f⟩ : FrameBundle g) q :=
  unitTangentTurn_change_matrix e f (e.changeMatrix f) (e.changeMatrix_orthogonal f)
    (e.mul_changeMatrix f) q

theorem unitTangentFiberMeasure_eq (e f : FrameBundle g) (hbase : e.base = f.base) :
    unitTangentFiberMeasure e = unitTangentFiberMeasure f := by
  cases e with
  | mk x E =>
    cases f with
    | mk y F =>
      change x = y at hbase
      subst y
      let A := orthogonalDirection (E.changeMatrix F) (E.changeMatrix_orthogonal F)
      have hA := sphereMeasure_preserving A
      have he : unitTangentTurn (⟨x, F⟩ : FrameBundle g) =
          unitTangentTurn (⟨x, E⟩ : FrameBundle g) ∘ A := by
        funext q
        exact (unitTangentTurn_change E F q).symm
      rw [unitTangentFiberMeasure, unitTangentFiberMeasure, he,
        ← Measure.map_map
          (continuous_unitTangentTurn_fixed _).measurable
          A.continuous.measurable, hA.map_eq]

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

/-- Orientation is irrelevant for the projected spherical measure, so
any measurable orthonormal frame section computes this same probability. -/
theorem canonicalUnitTangentMeasure_eq_any_section (g : SmoothMetric M)
    (o : FrameOrientation g) (s : M → FrameBundle g) (hs : Measurable s)
    (hbase : ∀ x, (s x).base = x) :
    canonicalUnitTangentMeasure g o =
      Measure.map (fun p : M × Directions => unitTangentTurn (s p.1) p.2)
        ((normalizedVolume g).prod sphereMeasure) := by
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  have hp : Measurable (fun p : M × Directions =>
      unitTangentTurn (positiveFrameSection g o p.1) p.2) :=
    continuous_unitTangentTurn.measurable.comp
      (((measurable_positiveFrameSection g o).comp measurable_fst).prodMk measurable_snd)
  have hs' : Measurable (fun p : M × Directions => unitTangentTurn (s p.1) p.2) :=
    continuous_unitTangentTurn.measurable.comp ((hs.comp measurable_fst).prodMk measurable_snd)
  rw [canonicalUnitTangentMeasure_eq_spherical g o]
  ext A hA
  rw [Measure.map_apply hp hA, Measure.map_apply hs' hA,
    Measure.prod_apply (hp hA), Measure.prod_apply (hs' hA)]
  apply lintegral_congr
  intro x
  have he := unitTangentFiberMeasure_eq (positiveFrameSection g o x) (s x)
    ((positiveFrameSection_base g o x).trans (hbase x).symm)
  have hv := congrArg (fun μ : Measure (UnitTangentBundle g) => μ A) he
  rw [unitTangentFiberMeasure, unitTangentFiberMeasure,
    Measure.map_apply
      (continuous_unitTangentTurn_fixed _).measurable hA,
    Measure.map_apply
      (continuous_unitTangentTurn_fixed _).measurable hA] at hv
  exact hv

end
end PositiveEinsteinFour.Geometry
end


section

/-! The positive-frame projection is a compact quotient. Consequently
the descended complete geodesic flow is jointly continuous, without a
continuous global choice of normal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M]

variable [CompactSpace M]

def unitTangentHomeomorph (g : SmoothMetric M) (o : FrameOrientation g) (t : ℝ) :
    UnitTangentBundle g ≃ₜ UnitTangentBundle g where
  toFun := unitTangentFlowMap g o t
  invFun := unitTangentFlowMap g o (-t)
  left_inv u := by
    rw [← unitTangentFlowMap_add, neg_add_cancel, unitTangentFlowMap_zero]
  right_inv u := by
    rw [← unitTangentFlowMap_add, add_neg_cancel, unitTangentFlowMap_zero]
  continuous_toFun := (unitTangentFlowMap_continuous g o).comp
    (continuous_const.prodMk continuous_id)
  continuous_invFun := (unitTangentFlowMap_continuous g o).comp
    (continuous_const.prodMk continuous_id)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Countable local trivializations supply the mild topological hypotheses
needed to identify the actual finite frame and unit-tangent measures from
continuous test functions. No auxiliary metric on the base is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set TopologicalSpace
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [CompactSpace M]

instance tangentBundle_secondCountable : SecondCountableTopology (TangentBundle I4 M) := by
  let : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact FourSpace M
  let e (x : M) := trivializationAt FourSpace (TangentSpace I4 : M → Type _) x
  obtain ⟨t, ht⟩ := finite_cover_nhds (fun x : M =>
    (e x).open_baseSet.mem_nhds (mem_baseSet_trivializationAt FourSpace (TangentSpace I4) x))
  let U (x : t) : Set (TangentBundle I4 M) := (e x.val).source
  let : ∀ x : t, SecondCountableTopology (U x) := fun x =>
    (e x.val).toOpenPartialHomeomorph.secondCountableTopology_source
  apply secondCountableTopology_of_countable_cover (U := U)
    (fun x => (e x.val).open_source)
  apply univ_subset_iff.mp
  intro p _
  have hp : p.proj ∈ ⋃ x ∈ t, (e x).baseSet := by rw [ht]; trivial
  obtain ⟨x, hxt, hx⟩ := mem_iUnion₂.mp hp
  exact mem_iUnion.mpr ⟨⟨x, hxt⟩, (e x).mem_source.mpr hx⟩

instance frameBundle_secondCountable (g : SmoothMetric M) :
    SecondCountableTopology (FrameBundle g) := by
  let : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact FourSpace M
  exact (isEmbedding_frameRealization g).secondCountableTopology

instance unitTangentBundle_secondCountable (g : SmoothMetric M) :
    SecondCountableTopology (UnitTangentBundle g) :=
  (isEmbedding_unitTangentRealization g).secondCountableTopology

variable [T2Space M]

instance frameBundle_pseudoMetrizable (g : SmoothMetric M) :
    PseudoMetrizableSpace (FrameBundle g) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem unitTangentBundle_pseudoMetrizable (g : SmoothMetric M) (o : FrameOrientation g) :
    PseudoMetrizableSpace (UnitTangentBundle g) := by
  let : CompactSpace (UnitTangentBundle g) := compact_unitTangentBundle g o
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Restrict the actual unit tangent probability to one base chart and
compute its spherical fibers in the smooth local Gram section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix MeasureTheory Set Bundle
open scoped Manifold ContDiff

noncomputable section

local instance instIsProbabilityMeasureDirectionsSphereMeasure_4 : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

omit [T3Space M] in
/-- Extend the Gram frame measurably outside its chart while retaining
its exact base point everywhere. The extension only computes measures. -/
theorem exists_measurable_gram_extension (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) : ∃ s : M → FrameBundle g, Measurable s ∧
      (∀ x, (s x).base = x) ∧
      EqOn s (localGramSection g c 1 (by simp)) (chartAt FourSpace c).source := by
  classical
  let U := (chartAt FourSpace c).source
  let a := localGramSection g c 1 (by simp)
  let f := U.piecewise a (fun _ => frameAt g c)
  have hf : Measurable f :=
    (continuousOn_localGramSection g c 1 (by simp)).measurable_piecewise
      continuousOn_const (chartAt FourSpace c).open_source.measurableSet
  let s := U.piecewise f (positiveFrameSection g o)
  have hs : Measurable s := hf.piecewise (chartAt FourSpace c).open_source.measurableSet
    (measurable_positiveFrameSection g o)
  have hlocal (x : M) (hx : x ∈ U) : s x = a x := by
    simp only [s, f, piecewise_eq_of_mem U _ _ hx]
  refine ⟨s, hs, ?_, fun x hx => hlocal x hx⟩
  intro x
  by_cases hx : x ∈ U
  · rw [hlocal x hx]
    exact localGramSection_base g c 1 (by simp) x
  · simp only [s, piecewise_eq_of_notMem U _ _ hx]
    exact positiveFrameSection_base g o x

/-- The restriction to a base chart has normalized base volume times
spherical probability, expressed using the actual smooth Gram frame. -/
theorem canonicalUnitTangentMeasure_restrict_chart (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) :
    (canonicalUnitTangentMeasure g o).restrict
      {u | u.base ∈ (chartAt FourSpace c).source} =
      Measure.map (fun p : M × Directions =>
        unitTangentTurn (localGramSection g c 1 (by simp) p.1) p.2)
        (((normalizedVolume g).restrict (chartAt FourSpace c).source).prod sphereMeasure) := by
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  obtain ⟨s, hs, hb, he⟩ := exists_measurable_gram_extension g o c
  let F : M × Directions → UnitTangentBundle g := fun p => unitTangentTurn (s p.1) p.2
  have hF : Measurable F := continuous_unitTangentTurn.measurable.comp
    ((hs.comp measurable_fst).prodMk measurable_snd)
  have hU : MeasurableSet {u : UnitTangentBundle g |
      u.base ∈ (chartAt FourSpace c).source} :=
    ((chartAt FourSpace c).open_source.preimage (continuous_unitTangentBase g)).measurableSet
  have hpre : F ⁻¹' {u | u.base ∈ (chartAt FourSpace c).source} =
      (chartAt FourSpace c).source ×ˢ (univ : Set Directions) := by
    ext p
    change (s p.1).base ∈ (chartAt FourSpace c).source ↔
      p.1 ∈ (chartAt FourSpace c).source ∧ p.2 ∈ univ
    simp only [hb, mem_univ, and_true]
  rw [canonicalUnitTangentMeasure_eq_any_section g o s hs hb,
    Measure.restrict_map hF hU, hpre, ← Measure.prod_restrict, Measure.restrict_univ]
  apply Measure.map_congr
  have hmem : ∀ᵐ p : M × Directions ∂
      (((normalizedVolume g).restrict (chartAt FourSpace c).source).prod sphereMeasure),
      p.1 ∈ (chartAt FourSpace c).source := by
    apply (Measure.ae_prod_iff_ae_ae
      ((chartAt FourSpace c).open_source.measurableSet.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem (chartAt FourSpace c).open_source.measurableSet] with x hx
    exact Filter.Eventually.of_forall (fun _ => hx)
  filter_upwards [hmem] with p hp
  exact congrArg (fun e => unitTangentTurn e p.2) (he hp)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normal-frame averaging descends to the intrinsic unit tangent bundle.
Consequently, preservation of its canonical probability by the actual
geodesic flow implies preservation of the complete oriented frame measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem normalFrameAverage_eq_of_unitTangent (o : FrameOrientation g)
    (F : FrameBundle g → ℝ) (e f : FrameBundle g)
    (he : e ∈ o.positive) (hf : f ∈ o.positive)
    (heq : unitTangentOfFrame e = unitTangentOfFrame f) :
    normalFrameAverage F e = normalFrameAverage F f := by
  cases e with
  | mk x E =>
    cases f with
    | mk y H =>
      have hxy : x = y := congrArg (fun u : UnitTangentBundle g => u.base) heq
      subst y
      have hfirst : E.vector 0 = H.vector 0 :=
        congrArg (fun u : UnitTangentBundle g => u.vector) heq
      exact normalFrameAverage_same_first F E H ((o.compatible x E H he).mp hf) hfirst

def unitTangentAverage (o : FrameOrientation g) (F : FrameBundle g → ℝ)
    (u : UnitTangentBundle g) : ℝ := normalFrameAverage F (unitTangentFrame g o u)

theorem unitTangentAverage_of_frame (o : FrameOrientation g) (F : FrameBundle g → ℝ)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    unitTangentAverage o F (unitTangentOfFrame e) = normalFrameAverage F e :=
  normalFrameAverage_eq_of_unitTangent o F _ e (unitTangentFrame_positive g o _) he
    (unitTangentOfFrame_lift g o _)

variable [T2Space M] [CompactSpace M]

theorem continuous_unitTangentAverage (o : FrameOrientation g)
    (F : FrameBundle g → ℝ) (hF : Continuous F) : Continuous (unitTangentAverage o F) := by
  apply (positiveFirstProjection_quotient g o).continuous_iff.mpr
  have h : Continuous (fun e : o.positive => normalFrameAverage F e.val) :=
    (continuous_normalFrameAverage F hF).comp continuous_subtype_val
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext e
  exact unitTangentAverage_of_frame o F e.val e.property

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem integral_unitTangentAverage (o : FrameOrientation g)
    (F : FrameBundle g → ℝ) (hF : Continuous F) :
    (∫ u, unitTangentAverage o F u ∂canonicalUnitTangentMeasure g o) =
      ∫ e, F e ∂canonicalFrameMeasure g o := by
  calc
    _ = ∫ e, unitTangentAverage o F (unitTangentOfFrame e)
        ∂canonicalFrameMeasure g o :=
      integral_map (continuous_unitTangentOfFrame g).measurable.aemeasurable
        (continuous_unitTangentAverage o F hF).aestronglyMeasurable
    _ = ∫ e, normalFrameAverage F e ∂canonicalFrameMeasure g o := by
      apply integral_congr_ae
      filter_upwards [canonicalFrameMeasure_supported g o] with e he
      exact unitTangentAverage_of_frame o F e he
    _ = _ := integral_normalFrameAverage o F hF

theorem integral_frameFlow_eq_unitTangentFlow (o : FrameOrientation g)
    (F : FrameBundle g → ℝ) (hF : Continuous F) (t : ℝ) :
    (∫ e, F (parallelFrameFlowMap g 0 t e) ∂canonicalFrameMeasure g o) =
      ∫ u, unitTangentAverage o F (unitTangentFlowMap g o t u)
        ∂canonicalUnitTangentMeasure g o := by
  rw [integral_parallel_eq_normalAverage o F hF t]
  symm
  calc
    _ = ∫ e, unitTangentAverage o F (unitTangentFlowMap g o t (unitTangentOfFrame e))
        ∂canonicalFrameMeasure g o :=
      integral_map (continuous_unitTangentOfFrame g).measurable.aemeasurable
        ((continuous_unitTangentAverage o F hF).comp
          (unitTangentHomeomorph g o t).continuous).aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [canonicalFrameMeasure_supported g o] with e he
      rw [unitTangentFlowMap_of_frame g o t e he]
      exact unitTangentAverage_of_frame o F _ (parallelFrameFlowMap_positive g o e he t)

theorem frameFlow_preserves_of_unitTangent (o : FrameOrientation g) (t : ℝ)
    (hunit : MeasurePreserving (unitTangentFlowMap g o t)
      (canonicalUnitTangentMeasure g o) (canonicalUnitTangentMeasure g o)) :
    MeasurePreserving (parallelFrameFlowMap g 0 t)
      (canonicalFrameMeasure g o) (canonicalFrameMeasure g o) := by
  refine ⟨(parallelFrameFlowMap_continuous_slice g 0 t).measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [integral_map (parallelFrameFlowMap_continuous_slice g 0 t).measurable.aemeasurable
    F.continuous.aestronglyMeasurable]
  rw [integral_frameFlow_eq_unitTangentFlow o F F.continuous t]
  rw [hunit.integral_comp (unitTangentHomeomorph g o t).measurableEmbedding]
  exact integral_unitTangentAverage o F F.continuous

theorem allFrameFlows_preserve_of_unitTangent (o : FrameOrientation g)
    (hunit : ∀ t, MeasurePreserving (unitTangentFlowMap g o t)
      (canonicalUnitTangentMeasure g o) (canonicalUnitTangentMeasure g o)) (k : Fin 4) (t : ℝ) :
    MeasurePreserving (parallelFrameFlowMap g k t)
      (canonicalFrameMeasure g o) (canonicalFrameMeasure g o) :=
  parallelFrameFlowMap_preserves_of_first g o
    (fun s => frameFlow_preserves_of_unitTangent o s (hunit s)) k t

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_first _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The positive radial extension of the actual unit-speed geodesic flow.
Its ambient measure preservation suffices for every unit-speed frame flow,
by continuity across energy shells and normal-frame averaging. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def unitTangentRadialHomeomorph (g : SmoothMetric M) (o : FrameOrientation g) (t : ℝ) :
    (PositiveRadius × UnitTangentBundle g) ≃ₜ (PositiveRadius × UnitTangentBundle g) where
  toFun := unitTangentRadialFlow g o t
  invFun := unitTangentRadialFlow g o (-t)
  left_inv p := by
    apply Prod.ext
    · rfl
    · change unitTangentFlowMap g o (p.1.val * -t)
        (unitTangentFlowMap g o (p.1.val * t) p.2) = p.2
      rw [← unitTangentFlowMap_add, mul_neg, neg_add_cancel, unitTangentFlowMap_zero]
  right_inv p := by
    apply Prod.ext
    · rfl
    · change unitTangentFlowMap g o (p.1.val * t)
        (unitTangentFlowMap g o (p.1.val * -t) p.2) = p.2
      rw [← unitTangentFlowMap_add, mul_neg, add_neg_cancel, unitTangentFlowMap_zero]
  continuous_toFun := unitTangentRadialFlow_continuous g o t
  continuous_invFun := unitTangentRadialFlow_continuous g o (-t)

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem unitTangentFlow_preserves_of_radial (g : SmoothMetric M) (o : FrameOrientation g)
    (t : ℝ) (hambient : MeasurePreserving (unitTangentRadialFlow g o t)
      ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o))
      ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o))) :
    MeasurePreserving (unitTangentFlowMap g o t)
      (canonicalUnitTangentMeasure g o) (canonicalUnitTangentMeasure g o) := by
  let : PseudoMetrizableSpace (UnitTangentBundle g) := unitTangentBundle_pseudoMetrizable g o
  have h := measurePreserving_cubicEnergyShell (canonicalUnitTangentMeasure g o)
    (fun p : PositiveRadius × UnitTangentBundle g =>
      unitTangentFlowMap g o (p.1.val * t) p.2)
    (continuous_snd.comp (unitTangentRadialFlow_continuous g o t)) hambient
    (⟨1, by norm_num [PositiveRadius]⟩ : PositiveRadius)
  simpa only [one_mul] using h

theorem allFrameFlows_preserve_of_radial (g : SmoothMetric M) (o : FrameOrientation g)
    (hambient : ∀ t, MeasurePreserving (unitTangentRadialFlow g o t)
      ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o))
      ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o))) (k : Fin 4) (t : ℝ) :
    MeasurePreserving (parallelFrameFlowMap g k t)
      (canonicalFrameMeasure g o) (canonicalFrameMeasure g o) :=
  allFrameFlows_preserve_of_unitTangent o
    (fun s => unitTangentFlow_preserves_of_radial g o s (hambient s)) k t

end
end PositiveEinsteinFour.Geometry
end


section

/-! Open cotangent neighborhoods for the actual radial flow. The local
Hamiltonian volume identity holds on every measurable subset of the initial
ball, and the intrinsic flow remains in the same chart on a common interval. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace KineticLocalFlow

/-- The proved unit Jacobian applies to any measurable part of the initial
ball. This is the form used after shrinking an intrinsic neighborhood. -/
theorem map_volume_restrict {g : SmoothMetric M} {c : M} {p : CotangentCoordinates}
    (F : KineticLocalFlow g c p) (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time)
    (s : Set CotangentCoordinates) (hs : MeasurableSet s)
    (hsub : s ⊆ Metric.ball p F.radius) :
    Measure.map (fun q => F.map (q, t)) (volume.restrict s) =
      volume.restrict ((fun q => F.map (q, t)) '' s) := by
  exact cotangent_map_volume_of_det_one _ s hs
    (fun q hq => (F.initial_derivative q (hsub hq) t ht).differentiableAt)
    ((F.injective_slice t ht).mono hsub)
    (fun q hq => by rw [F.jacobian_det q (hsub hq) t ht, abs_one])

end KineticLocalFlow

theorem unitRadialCotangentState_continuousOn (g : SmoothMetric M) (c : M) :
    ContinuousOn (unitRadialCotangentState g c)
      {q | q.2.base ∈ (chartAt FourSpace c).source} :=
  fun p hp => (unitRadialCotangentState_continuousAt g c p hp).continuousWithinAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! Put the actual metric and density comparisons into the same
constant-density form. All estimates are on genuine chart measures. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem exists_chartHausdorff_constant_bounds (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (δ : ℝ) (hδ : 0 < δ) (hδone : δ < 1) :
    ∃ U : Set FourSpace, IsOpen U ∧ z₀.val ∈ U ∧ U ⊆ (chartAt FourSpace c).target ∧
      ∀ A : Set FourSpace, MeasurableSet A → A ⊆ U →
        chartHausdorffMeasure g c A ≤ ENNReal.ofReal ((1 + δ) ^ 2) *
          ((euclideanHausdorffFactor : ℝ≥0∞) *
            (ENNReal.ofReal (chartVolumeDensity g c z₀) * volume A)) ∧
        ENNReal.ofReal ((1 - δ) ^ 2) *
          ((euclideanHausdorffFactor : ℝ≥0∞) *
            (ENNReal.ofReal (chartVolumeDensity g c z₀) * volume A)) ≤
          chartHausdorffMeasure g c A := by
  obtain ⟨U, hU, hzU, hUt, hbound⟩ := exists_metricHausdorff_chart_bounds g c z₀ δ hδ hδone
  refine ⟨U, hU, hzU, hUt, ?_⟩
  intro A hA hAU
  have h := hbound A hAU
  rw [hausdorff_frozenFrame_symm_image] at h
  rw [ofReal_sqrt_four _ (by linarith), ofReal_inv_sqrt_four _ (by linarith)] at h
  rw [chartHausdorffMeasure_apply g c A hA (hAU.trans hUt)]
  refine ⟨h.1, ?_⟩
  have hq : ENNReal.ofReal ((1 - δ) ^ 2) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (by linarith)))
  have hlow := mul_le_mul_right h.2 (ENNReal.ofReal ((1 - δ) ^ 2))
  have hcancel : ENNReal.ofReal ((1 - δ) ^ 2) *
      ((ENNReal.ofReal ((1 - δ) ^ 2))⁻¹ *
        metricHausdorffMeasure g ((chartAt FourSpace c).symm '' A)) =
      metricHausdorffMeasure g ((chartAt FourSpace c).symm '' A) := by
    rw [← mul_assoc, ENNReal.mul_inv_cancel hq ENNReal.ofReal_ne_top, one_mul]
  rw [hcancel] at hlow
  simpa only [mul_assoc] using hlow

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial canonical measure in actual cotangent coordinates. The only
technical geometric input is the exact normalized base-chart density; the
spherical factor and all fiber Jacobians follow from polar coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix MeasureTheory Set
open scoped BigOperators Manifold ContDiff _root_.Topology ENNReal

noncomputable section

local instance radialChartSphereProbability : IsProbabilityMeasure sphereMeasure :=
  actual_sphereMeasure_probability

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def chartBaseDensity (g : SmoothMetric M) (c : M) : Measure (ChartTarget c) :=
  (chartCoordinateMeasure c).withDensity
    (fun z => ENNReal.ofReal (chartVolumeDensity g c z))

instance chartBaseDensity_sfinite (g : SmoothMetric M) (c : M) :
    SFinite (chartBaseDensity g c) := by
  unfold chartBaseDensity
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def gramChartUnitTangent (g : SmoothMetric M) (c : M)
    (p : ChartTarget c × Directions) : UnitTangentBundle g :=
  unitTangentTurn (chartGramSection g c 1 (by simp) p.1) p.2

theorem continuous_gramChartUnitTangent (g : SmoothMetric M) (c : M) :
    Continuous (gramChartUnitTangent g c) :=
  continuous_unitTangentTurn.comp
    (((continuous_chartGramSection g c 1 (by simp)).comp continuous_fst).prodMk continuous_snd)

theorem localGramSection_chart_inverse (g : SmoothMetric M) (c : M)
    (z : ChartTarget c) :
    localGramSection g c 1 (by simp) ((chartAt FourSpace c).symm z.val) =
      chartGramSection g c 1 (by simp) z := by
  classical
  rw [localGramSection, dite_eq_left ((chartAt FourSpace c).map_target z.property)]
  apply congrArg (chartGramSection g c 1 (by simp))
  exact Subtype.ext ((chartAt FourSpace c).right_inv z.property)

theorem chartGramFrame_map (g : SmoothMetric M) (c : M)
    (z : ChartTarget c) (v : FourSpace) :
    (chartGramFrame g c 1 (by simp) z).map v =
      chartBackwardOperator c z.val
        (WithLp.toLp 2 (chartGramMatrix g c 1 z.val *ᵥ WithLp.ofLp v)) := by
  let e := chartGramFrame g c 1 (by simp) z
  have hvec (i : Fin 4) : e.map (coordinateVector i) = e.vector i := by
    ext j
    simp [OrthonormalFrame.map_apply, coordinateVector]
  have hv : (∑ i, v i • coordinateVector i) = v :=
    sum_coordinateVector (WithLp.ofLp v)
  calc
    e.map v = ∑ i, v i • e.vector i := by
      conv_lhs => rw [← hv]
      rw [map_sum]
      simp only [map_smul, hvec]
    _ = chartBackwardOperator c z.val
        (∑ i, v i • WithLp.toLp 2 (fun j => chartGramMatrix g c 1 z.val j i)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      exact congrArg (fun w : FourSpace => v i • w)
        (chartGramFrame_vector g c 1 (by simp) z i)
    _ = _ := by
      congr 1
      ext j
      simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
        smul_eq_mul, mulVec]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem gramChartUnitTangent_velocity (g : SmoothMetric M) (c : M)
    (z : ChartTarget c) (q : Directions) :
    unitChartVelocity c (gramChartUnitTangent g c (z, q)) =
      WithLp.toLp 2 (chartGramMatrix g c 1 z.val *ᵥ WithLp.ofLp q.val) := by
  have hbase : (gramChartUnitTangent g c (z, q)).base =
      (chartAt FourSpace c).symm z.val := rfl
  have hvector : unitTangentVector (gramChartUnitTangent g c (z, q)) =
      (chartGramFrame g c 1 (by simp) z).map q.val :=
    (chartGramFrame g c 1 (by simp) z).turn_first q
  have hu : (gramChartUnitTangent g c (z, q)).base ∈ (chartAt FourSpace c).source := by
    rw [hbase]
    exact (chartAt FourSpace c).map_target z.property
  rw [unitChartVelocity_eq_derivative c _ hu, hbase, hvector,
    chartGramFrame_map]
  exact congrArg (fun L : FourSpace →L[ℝ] FourSpace =>
    L (WithLp.toLp 2 (chartGramMatrix g c 1 z.val *ᵥ WithLp.ofLp q.val)))
    (chartForward_backward c z.val z.property)

def gramRadialLift (g : SmoothMetric M) (c : M)
    (p : ChartTarget c × (Directions × PositiveRadius)) :
    PositiveRadius × UnitTangentBundle g :=
  (p.2.2, gramChartUnitTangent g c (p.1, p.2.1))

theorem continuous_gramRadialLift (g : SmoothMetric M) (c : M) :
    Continuous (gramRadialLift g c) :=
  (continuous_snd.comp continuous_snd).prodMk
    ((continuous_gramChartUnitTangent g c).comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))

theorem gramRadialLift_cotangent (g : SmoothMetric M) (c : M)
    (p : ChartTarget c × (Directions × PositiveRadius)) :
    unitRadialCotangentState g c (gramRadialLift g c p) =
      ((chartPolarLowering g c p).1.val, (chartPolarLowering g c p).2) := by
  have hz := (chartAt FourSpace c).right_inv p.1.property
  have hv := gramChartUnitTangent_velocity g c p.1 p.2.1
  change (chartAt FourSpace c ((chartAt FourSpace c).symm p.1.val),
    p.2.2.val • WithLp.toLp 2
      (metricInChart g c (chartAt FourSpace c ((chartAt FourSpace c).symm p.1.val)) *ᵥ
        WithLp.ofLp (unitChartVelocity c (gramChartUnitTangent g c (p.1, p.2.1))))) = _
  rw [hz, hv]
  apply Prod.ext
  · rfl
  change p.2.2.val • WithLp.toLp 2
      (metricInChart g c p.1.val *ᵥ
        (chartGramMatrix g c 1 p.1.val *ᵥ WithLp.ofLp p.2.1.val)) =
    WithLp.toLp 2 ((metricInChart g c p.1.val * chartGramMatrix g c 1 p.1.val) *ᵥ
      WithLp.ofLp (p.2.2.val • p.2.1.val))
  rw [WithLp.ofLp_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rfl

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

theorem canonicalUnitTangentMeasure_chartDensity (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (K : ℝ≥0∞)
    (hbase : (normalizedVolume g).restrict (chartAt FourSpace c).source =
      K • Measure.map (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val)
        (chartBaseDensity g c)) :
    (canonicalUnitTangentMeasure g o).restrict
      {u | u.base ∈ (chartAt FourSpace c).source} =
      K • Measure.map (gramChartUnitTangent g c)
        ((chartBaseDensity g c).prod sphereMeasure) := by
  obtain ⟨s, hs, _hb, he⟩ := exists_measurable_gram_extension g o c
  let L : M × Directions → UnitTangentBundle g := fun p => unitTangentTurn (s p.1) p.2
  have hL : Measurable L := continuous_unitTangentTurn.measurable.comp
    ((hs.comp measurable_fst).prodMk measurable_snd)
  have hB : Measurable (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val) :=
    ((chartAt FourSpace c).continuousOn_symm.comp_continuous continuous_subtype_val
      (fun z => z.property)).measurable
  have hsection : (canonicalUnitTangentMeasure g o).restrict
      {u | u.base ∈ (chartAt FourSpace c).source} =
      Measure.map L (((normalizedVolume g).restrict (chartAt FourSpace c).source).prod
        sphereMeasure) := by
    rw [canonicalUnitTangentMeasure_restrict_chart]
    apply Measure.map_congr
    have hmem : ∀ᵐ p : M × Directions ∂
        (((normalizedVolume g).restrict (chartAt FourSpace c).source).prod sphereMeasure),
        p.1 ∈ (chartAt FourSpace c).source := by
      apply (Measure.ae_prod_iff_ae_ae
        ((chartAt FourSpace c).open_source.measurableSet.preimage measurable_fst)).mpr
      filter_upwards [ae_restrict_mem (chartAt FourSpace c).open_source.measurableSet] with x hx
      exact Filter.Eventually.of_forall (fun _ => hx)
    filter_upwards [hmem] with p hp
    exact congrArg (fun e => unitTangentTurn e p.2) (he hp).symm
  rw [hsection, hbase, Measure.prod_smul_left,
    Measure.map_smul]
  congr 1
  have hprod : (Measure.map (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val)
      (chartBaseDensity g c)).prod sphereMeasure =
      Measure.map (Prod.map (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val) id)
        ((chartBaseDensity g c).prod sphereMeasure) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (chartBaseDensity g c) sphereMeasure hB measurable_id)
  rw [hprod, Measure.map_map hL (hB.prodMap measurable_id)]
  apply congrArg (fun f => Measure.map f ((chartBaseDensity g c).prod sphereMeasure))
  funext p
  change unitTangentTurn (s ((chartAt FourSpace c).symm p.1.val)) p.2 = _
  rw [he ((chartAt FourSpace c).map_target p.1.property), localGramSection_chart_inverse]
  rfl

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
theorem gramRadialLift_map (g : SmoothMetric M) (c : M) :
    Measure.map (gramRadialLift g c)
      ((chartBaseDensity g c).prod (sphereMeasure.prod (Measure.volumeIoiPow 3))) =
      (Measure.volumeIoiPow 3).prod
        (Measure.map (gramChartUnitTangent g c) ((chartBaseDensity g c).prod sphereMeasure)) := by
  let ν := chartBaseDensity g c
  let ρ := Measure.volumeIoiPow 3
  have hA := (measurePreserving_prodAssoc ν sphereMeasure ρ).symm
    MeasurableEquiv.prodAssoc
  have hC : MeasurePreserving Prod.swap ((ν.prod sphereMeasure).prod ρ)
      (ρ.prod (ν.prod sphereMeasure)) := Measure.measurePreserving_swap
  have hU : MeasurePreserving (gramChartUnitTangent g c) (ν.prod sphereMeasure)
      (Measure.map (gramChartUnitTangent g c) (ν.prod sphereMeasure)) :=
    ⟨(continuous_gramChartUnitTangent g c).measurable, rfl⟩
  have h := ((MeasurePreserving.id ρ).prod hU).comp (hC.comp hA)
  exact h.map_eq

def measurableRadialState (g : SmoothMetric M) (c : M) :
    PositiveRadius × UnitTangentBundle g → CotangentCoordinates :=
  open Classical in
  {p | p.2.base ∈ (chartAt FourSpace c).source}.piecewise
    (unitRadialCotangentState g c) (fun _ => 0)

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem measurable_measurableRadialState (g : SmoothMetric M) (c : M) :
    Measurable (measurableRadialState g c) := by
  classical
  exact (unitRadialCotangentState_continuousOn g c).measurable_piecewise
    continuousOn_const (((chartAt FourSpace c).open_source.preimage
      ((continuous_unitTangentBase g).comp continuous_snd)).measurableSet)

omit [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [Nonempty M] in
theorem cotangentCoordinateInclusion_map (c : M) :
    Measure.map (fun p : ChartTarget c × FourSpace => (p.1.val, p.2))
      ((chartCoordinateMeasure c).prod volume) =
      (volume : Measure CotangentCoordinates).restrict
        {p | p.1 ∈ (chartAt FourSpace c).target} := by
  have hS : MeasurePreserving (Subtype.val : ChartTarget c → FourSpace)
      (chartCoordinateMeasure c) (volume.restrict (chartAt FourSpace c).target) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    exact map_comap_subtype_coe (chartAt FourSpace c).open_target.measurableSet
      (volume : Measure FourSpace)
  have h := hS.prod (MeasurePreserving.id (volume : Measure FourSpace))
  change Measure.map _ _ = ((volume : Measure FourSpace).prod volume).restrict _
  have hset : {p : CotangentCoordinates | p.1 ∈ (chartAt FourSpace c).target} =
      (chartAt FourSpace c).target ×ˢ (univ : Set FourSpace) := by ext p; simp
  rw [hset]
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  exact h.map_eq

/-- The normalization factor is the base density factor divided by the
actual Euclidean angular mass. No flow preservation is assumed. -/
theorem unitRadialCotangentState_map (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (K : ℝ≥0∞)
    (hbase : (normalizedVolume g).restrict (chartAt FourSpace c).source =
      K • Measure.map (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val)
        (chartBaseDensity g c)) :
    Measure.map (unitRadialCotangentState g c)
      (((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o)).restrict
        {p | p.2.base ∈ (chartAt FourSpace c).source}) =
      (K / polarAngularMass) • (volume : Measure CotangentCoordinates).restrict
        {p | p.1 ∈ (chartAt FourSpace c).target} := by
  classical
  let ν := (chartBaseDensity g c).prod (sphereMeasure.prod (Measure.volumeIoiPow 3))
  let D : Set (PositiveRadius × UnitTangentBundle g) :=
    {p | p.2.base ∈ (chartAt FourSpace c).source}
  let μ := ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o)).restrict D
  have hD : MeasurableSet D := ((chartAt FourSpace c).open_source.preimage
    ((continuous_unitTangentBase g).comp continuous_snd)).measurableSet
  have hμ : μ = K • Measure.map (gramRadialLift g c) ν := by
    have hDprod : D = univ ×ˢ {u | u.base ∈ (chartAt FourSpace c).source} := by
      ext p
      simp [D]
    dsimp [μ]
    rw [hDprod]
    rw [← Measure.prod_restrict, Measure.restrict_univ,
      canonicalUnitTangentMeasure_chartDensity g o c K hbase, Measure.prod_smul_right,
      ← gramRadialLift_map]
  have hactual : Measure.map (unitRadialCotangentState g c) μ =
      Measure.map (measurableRadialState g c) μ := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hD] with p hp
    exact (piecewise_eq_of_mem D _ _ hp).symm
  let P := chartPolarLowering g c
  have hP : Measurable P := by
    apply (continuous_chartCotangentLowering g c).measurable.comp
    exact (continuous_fst.prodMk
      (((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).smul
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))))).measurable
  have hpolar : Measure.map P ν = polarAngularMass⁻¹ •
      ((chartCoordinateMeasure c).prod (volume : Measure FourSpace)) := by
    have h := (chartPolarLowering_measurePreserving g c).map_eq
    rw [Measure.prod_smul_left, Measure.prod_smul_right,
      Measure.map_smul] at h
    have hi := congrArg (fun m : Measure (ChartTarget c × FourSpace) => polarAngularMass⁻¹ • m) h
    simpa only [ν, chartBaseDensity, smul_smul, ENNReal.inv_mul_cancel polarAngularMass_ne_zero
      polarAngularMass_ne_top, one_smul] using hi
  have hfun : measurableRadialState g c ∘ gramRadialLift g c =
      (fun p : ChartTarget c × FourSpace => (p.1.val, p.2)) ∘ P := by
    funext p
    rw [Function.comp_apply, measurableRadialState, piecewise_eq_of_mem]
    · exact gramRadialLift_cotangent g c p
    · exact (chartAt FourSpace c).map_target p.1.property
  have hI : Measurable (fun p : ChartTarget c × FourSpace => (p.1.val, p.2)) :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).measurable
  change Measure.map (unitRadialCotangentState g c) μ = _
  rw [hactual, hμ, Measure.map_smul,
    Measure.map_map (measurable_measurableRadialState g c)
      (continuous_gramRadialLift g c).measurable, hfun,
    ← Measure.map_map hI hP, hpolar, Measure.map_smul,
    cotangentCoordinateInclusion_map, smul_smul]
  rw [div_eq_mul_inv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identify metric Hausdorff measure in a chart from the proved sharp
metric comparison and the continuous density, using local measure gluing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem chartHausdorffMeasure_eq_density (g : SmoothMetric M) (c : M) :
    (chartHausdorffMeasure g c).restrict (chartAt FourSpace c).target =
      (euclideanHausdorffFactor : ℝ≥0∞) •
        ((volume.withDensity (fun z => ENNReal.ofReal (chartVolumeDensity g c z))).restrict
          (chartAt FourSpace c).target) := by
  let μ := chartHausdorffMeasure g c
  let C : ℝ≥0∞ := euclideanHausdorffFactor
  let D : Measure FourSpace := volume.withDensity (fun z => ENNReal.ofReal (chartVolumeDensity g c z))
  let ν : Measure FourSpace := C • D
  have hlocal (a : ℝ≥0∞) (ha : a < 1) (z : FourSpace)
      (hz : z ∈ (chartAt FourSpace c).target) :
      ∃ U : Set FourSpace, IsOpen U ∧ z ∈ U ∧ U ⊆ (chartAt FourSpace c).target ∧
        (a • μ).restrict U ≤ ν.restrict U ∧ (a • ν).restrict U ≤ μ.restrict U := by
    have hatop : a ≠ ⊤ := ne_top_of_lt ha
    have haReal : a.toReal < 1 := by
      exact (ENNReal.toReal_lt_toReal hatop (by simp)).mpr ha
    obtain ⟨δ, hδ, hδone, hc₁, hc₂⟩ :=
      density_comparison_parameter a.toReal ENNReal.toReal_nonneg haReal
    let z₀ : ChartTarget c := ⟨z, hz⟩
    obtain ⟨U₁, hU₁, hz₁, hUt₁, hM⟩ := exists_chartHausdorff_constant_bounds g c z₀ δ hδ hδone
    obtain ⟨U₂, hU₂, hz₂, _hUt₂, hD⟩ := exists_chartDensity_local_bounds g c z₀ δ hδ
    let U := U₁ ∩ U₂
    have hcE₁ : a * ENNReal.ofReal ((1 + δ) ^ 2) ≤ ENNReal.ofReal (1 - δ) := by
      rw [← ENNReal.ofReal_toReal hatop, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_le_ofReal hc₁
    have hcE₂ : a * ENNReal.ofReal (1 + δ) ≤ ENNReal.ofReal ((1 - δ) ^ 2) := by
      rw [← ENNReal.ofReal_toReal hatop, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_le_ofReal hc₂
    have hvalues (A : Set FourSpace) (hA : MeasurableSet A) (hAU : A ⊆ U) :
        a * μ A ≤ ν A ∧ a * ν A ≤ μ A := by
      let X : ℝ≥0∞ := C * (ENNReal.ofReal (chartVolumeDensity g c z₀) * volume A)
      have hm := hM A hA (fun x hx => (hAU hx).1)
      have hd := hD A hA (fun x hx => (hAU hx).2)
      have hdlo : ENNReal.ofReal (1 - δ) * X ≤ ν A := by
        calc
          _ = C * (ENNReal.ofReal ((1 - δ) * chartVolumeDensity g c z₀) * volume A) := by
            rw [ENNReal.ofReal_mul (by linarith : 0 ≤ 1 - δ)]
            dsimp [X]
            ac_rfl
          _ ≤ C * D A := mul_le_mul_right hd.1 C
          _ = ν A := rfl
      have hdhi : ν A ≤ ENNReal.ofReal (1 + δ) * X := by
        calc
          _ = C * D A := rfl
          _ ≤ C * (ENNReal.ofReal ((1 + δ) * chartVolumeDensity g c z₀) * volume A) :=
            mul_le_mul_right hd.2 C
          _ = _ := by
            rw [ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + δ)]
            dsimp [X]
            ac_rfl
      constructor
      · calc
          a * μ A ≤ a * (ENNReal.ofReal ((1 + δ) ^ 2) * X) :=
            mul_le_mul_right hm.1 a
          _ = (a * ENNReal.ofReal ((1 + δ) ^ 2)) * X := (mul_assoc _ _ _).symm
          _ ≤ ENNReal.ofReal (1 - δ) * X := mul_le_mul_left hcE₁ X
          _ ≤ ν A := hdlo
      · calc
          a * ν A ≤ a * (ENNReal.ofReal (1 + δ) * X) := mul_le_mul_right hdhi a
          _ = (a * ENNReal.ofReal (1 + δ)) * X := (mul_assoc _ _ _).symm
          _ ≤ ENNReal.ofReal ((1 - δ) ^ 2) * X := mul_le_mul_left hcE₂ X
          _ ≤ μ A := hm.2
    refine ⟨U, hU₁.inter hU₂, ⟨hz₁, hz₂⟩, fun x hx => hUt₁ hx.1, ?_, ?_⟩
    · apply Measure.le_iff.mpr
      intro A hA
      rw [Measure.restrict_apply hA, Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul]
      exact (hvalues (A ∩ U) (hA.inter (hU₁.inter hU₂).measurableSet) inter_subset_right).1
    · apply Measure.le_iff.mpr
      intro A hA
      rw [Measure.restrict_apply hA, Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul]
      exact (hvalues (A ∩ U) (hA.inter (hU₁.inter hU₂).measurableSet) inter_subset_right).2
  have heq : μ.restrict (chartAt FourSpace c).target = ν.restrict (chartAt FourSpace c).target := by
    apply le_antisymm
    · apply measure_restrict_le_of_sharp_local_comparison μ ν _ (chartAt FourSpace c).open_target
      intro a ha z hz
      obtain ⟨U, hU, hzU, hUt, hm, _⟩ := hlocal a ha z hz
      exact ⟨U, hU, hzU, hUt, hm⟩
    · apply measure_restrict_le_of_sharp_local_comparison ν μ _ (chartAt FourSpace c).open_target
      intro a ha z hz
      obtain ⟨U, hU, hzU, hUt, _, hm⟩ := hlocal a ha z hz
      exact ⟨U, hU, hzU, hUt, hm⟩
  simpa only [ν, Measure.restrict_smul] using heq

end
end PositiveEinsteinFour.Geometry
end


section

/-! Measurable extensions of the actual radial cotangent chart and its
inverse. The extensions agree with the homeomorphism on its genuine domain;
the arbitrary value outside that domain is used only for measurability. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def radialCotangentStateExtension (g : SmoothMetric M) (c : M) :
    PositiveRadius × UnitTangentBundle g → CotangentCoordinates :=
  open Classical in
  {p | p.2.base ∈ (chartAt FourSpace c).source}.piecewise
    (unitRadialCotangentState g c) (fun _ => 0)

theorem radialCotangentStateExtension_eq (g : SmoothMetric M) (c : M)
    (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    radialCotangentStateExtension g c p = unitRadialCotangentState g c p := by
  classical
  exact piecewise_eq_of_mem _ _ _ hp

theorem cotangentRadialRetraction_extension (g : SmoothMetric M) (c : M)
    (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    cotangentRadialRetraction g c (radialCotangentStateExtension g c p) = p := by
  rw [radialCotangentStateExtension_eq g c p hp]
  exact cotangentRadialRetraction_state g c p hp

variable [CompactSpace M]

theorem measurable_radialCotangentStateExtension (g : SmoothMetric M) (c : M) :
    Measurable (radialCotangentStateExtension g c) := by
  classical
  exact (unitRadialCotangentState_continuousOn g c).measurable_piecewise
    continuousOn_const (((chartAt FourSpace c).open_source.preimage
      ((continuous_unitTangentBase g).comp continuous_snd)).measurableSet)

theorem measurable_cotangentRadialRetraction (g : SmoothMetric M) (c : M) :
    Measurable (cotangentRadialRetraction g c) := by
  apply (MeasurableEmbedding.subtype_coe (s := {z : CotangentCoordinates |
    z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0})
      (((chartAt FourSpace c).open_target.preimage continuous_fst).inter
        (isOpen_compl_singleton.preimage continuous_snd)).measurableSet).measurable_extend
  · exact (continuous_cotangentRadialInverseOn g c).measurable
  · exact measurable_const

end
end PositiveEinsteinFour.Geometry
end


section

/-! Technical measure reductions for the actual radial flow. Local image
identities on a compact slab give every time on that slab; a countable
exhaustion then gives the ambient measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
theorem isClosed_radialSlab (g : SmoothMetric M) (a b : ℝ) :
    IsClosed (radialSlab g a b) :=
  isClosed_Icc.preimage (continuous_subtype_val.comp continuous_fst)

theorem unitTangentRadialFlow_preimage_slab (g : SmoothMetric M) (o : FrameOrientation g)
    (a b t : ℝ) :
    unitTangentRadialFlow g o t ⁻¹' radialSlab g a b = radialSlab g a b := rfl

theorem unitTangentRadialFlow_image_slab (g : SmoothMetric M) (o : FrameOrientation g)
    (a b t : ℝ) :
    unitTangentRadialFlow g o t '' radialSlab g a b = radialSlab g a b := by
  change unitTangentRadialHomeomorph g o t '' radialSlab g a b = _
  rw [(unitTangentRadialHomeomorph g o t).image_eq_preimage_symm]
  rfl

/-- A local ambient image identity restricts to the invariant slab. -/
theorem radialSlab_restrict_local_image (g : SmoothMetric M) (o : FrameOrientation g)
    (μ : Measure (PositiveRadius × UnitTangentBundle g)) (a b t : ℝ)
    (U : Set (PositiveRadius × UnitTangentBundle g))
    (hlocal : Measure.map (unitTangentRadialFlow g o t) (μ.restrict U) =
      μ.restrict (unitTangentRadialFlow g o t '' U)) :
    Measure.map (unitTangentRadialFlow g o t) ((μ.restrict (radialSlab g a b)).restrict U) =
      (μ.restrict (radialSlab g a b)).restrict (unitTangentRadialFlow g o t '' U) := by
  have hS := (isClosed_radialSlab g a b).measurableSet
  have hf := (unitTangentRadialFlow_continuous g o t).measurable
  calc
    _ = Measure.map (unitTangentRadialFlow g o t)
        ((μ.restrict U).restrict (radialSlab g a b)) :=
      congrArg (Measure.map (unitTangentRadialFlow g o t)) (Measure.restrict_comm hS).symm
    _ = (Measure.map (unitTangentRadialFlow g o t) (μ.restrict U)).restrict
        (radialSlab g a b) := by
      rw [Measure.restrict_map hf hS, unitTangentRadialFlow_preimage_slab]
    _ = (μ.restrict (unitTangentRadialFlow g o t '' U)).restrict (radialSlab g a b) := by
      rw [hlocal]
    _ = _ := Measure.restrict_comm hS

/-- It suffices to supply ambient local image identities at points of the
slab. Outside it, both restricted measures vanish. -/
theorem radialSlab_preserves_of_local_image (g : SmoothMetric M) (o : FrameOrientation g)
    (μ : Measure (PositiveRadius × UnitTangentBundle g)) (a b t : ℝ)
    (hlocal : ∀ p ∈ radialSlab g a b,
      ∃ U : Set (PositiveRadius × UnitTangentBundle g), IsOpen U ∧ p ∈ U ∧
        Measure.map (unitTangentRadialFlow g o t) (μ.restrict U) =
          μ.restrict (unitTangentRadialFlow g o t '' U)) :
    MeasurePreserving (unitTangentRadialFlow g o t)
      (μ.restrict (radialSlab g a b)) (μ.restrict (radialSlab g a b)) := by
  apply measurePreserving_of_local_image (unitTangentRadialHomeomorph g o t)
  intro p
  by_cases hp : p ∈ radialSlab g a b
  · obtain ⟨U, hU, hpU, hm⟩ := hlocal p hp
    exact ⟨U, hU, hpU, radialSlab_restrict_local_image g o μ a b t U hm⟩
  · have hS := (isClosed_radialSlab g a b).measurableSet
    refine ⟨(radialSlab g a b)ᶜ, (isClosed_radialSlab g a b).isOpen_compl, hp, ?_⟩
    have himage : unitTangentRadialFlow g o t '' (radialSlab g a b)ᶜ =
        (radialSlab g a b)ᶜ := by
      change unitTangentRadialHomeomorph g o t '' (radialSlab g a b)ᶜ = _
      rw [image_compl_eq (unitTangentRadialHomeomorph g o t).bijective]
      change (unitTangentRadialFlow g o t '' radialSlab g a b)ᶜ = _
      rw [unitTangentRadialFlow_image_slab]
    change Measure.map (unitTangentRadialFlow g o t)
        ((μ.restrict (radialSlab g a b)).restrict (radialSlab g a b)ᶜ) =
      (μ.restrict (radialSlab g a b)).restrict
        (unitTangentRadialFlow g o t '' (radialSlab g a b)ᶜ)
    rw [himage, Measure.restrict_restrict hS.compl, compl_inter_self,
      Measure.restrict_empty, Measure.map_zero]

/-- The group law turns a neighborhood of preserving times into all times,
for the measure restricted to one invariant slab. -/
theorem radialSlab_preserves_of_near_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (μ : Measure (PositiveRadius × UnitTangentBundle g)) (a b ε : ℝ) (hε : 0 < ε)
    (hnear : ∀ t ∈ Ioo (-ε) ε, MeasurePreserving (unitTangentRadialFlow g o t)
      (μ.restrict (radialSlab g a b)) (μ.restrict (radialSlab g a b))) (t : ℝ) :
    MeasurePreserving (unitTangentRadialFlow g o t)
      (μ.restrict (radialSlab g a b)) (μ.restrict (radialSlab g a b)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / ε)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hε.le) hn
  have hnzero : (n : ℝ) ≠ 0 := hnpos.ne'
  let s : ℝ := t / n
  have hs : |s| < ε := by
    dsimp [s]
    rw [abs_div, abs_of_pos hnpos]
    apply (div_lt_iff₀ hnpos).mpr
    have h := (div_lt_iff₀ hε).mp hn
    nlinarith
  have hstep := hnear s (abs_lt.mp hs)
  have hmul (m : ℕ) : MeasurePreserving (unitTangentRadialFlow g o ((m : ℝ) * s))
      (μ.restrict (radialSlab g a b)) (μ.restrict (radialSlab g a b)) := by
    induction m with
    | zero =>
      have hzero : unitTangentRadialFlow g o 0 = id :=
        funext (unitTangentRadialFlow_zero g o)
      simpa only [Nat.cast_zero, zero_mul, hzero] using
        MeasurePreserving.id (μ.restrict (radialSlab g a b))
    | succ m ih =>
      have h := ih.comp hstep
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      funext p
      rw [Nat.cast_succ, add_mul, one_mul, unitTangentRadialFlow_add]
      rfl
  have heq : (n : ℝ) * s = t := by dsimp [s]; field_simp [hnzero]
  simpa only [heq] using hmul n

def exhaustingRadialSlab (g : SmoothMetric M) (n : ℕ) :
    Set (PositiveRadius × UnitTangentBundle g) :=
  radialSlab g (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)

omit [T2Space M] [CompactSpace M] in
theorem iUnion_exhaustingRadialSlab (g : SmoothMetric M) :
    (⋃ n, exhaustingRadialSlab g n) = univ := by
  apply univ_subset_iff.mp
  intro p _
  obtain ⟨n, hn⟩ := exists_nat_gt (max p.1.val (p.1.val)⁻¹)
  have hu : p.1.val < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hl : (p.1.val)⁻¹ < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hp : 0 < p.1.val := p.1.property
  have hmul : 1 < (n : ℝ) * p.1.val :=
    (div_lt_iff₀ hp).mp (by simpa only [one_div] using hl)
  apply mem_iUnion.mpr
  refine ⟨n, ?_⟩
  change 1 / ((n : ℝ) + 1) ≤ p.1.val ∧ p.1.val ≤ (n : ℝ) + 1
  constructor
  · apply (div_le_iff₀ hnpos).mpr
    nlinarith
  · linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reconstruct the actual base measure from its proved chart density.
The last identity is the normalized base input for the cotangent product. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory MeasureTheory.Measure Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

omit [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M] in
theorem continuous_chartInverse_restrict (c : M) :
    Continuous (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact ((chartAt FourSpace c).symm.continuousAt z.property).comp
    continuous_subtype_val.continuousAt

theorem metricHausdorffMeasure_restrict_chart (g : SmoothMetric M) (c : M) :
    (metricHausdorffMeasure g).restrict (chartAt FourSpace c).source =
      (euclideanHausdorffFactor : ℝ≥0∞) •
        Measure.map (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val)
          ((chartCoordinateMeasure c).withDensity
            (fun z => ENNReal.ofReal (chartVolumeDensity g c z))) := by
  let φ : ChartTarget c → M := fun z => (chartAt FourSpace c).symm z.val
  have hφ : Measurable φ := (continuous_chartInverse_restrict c).measurable
  ext A hA
  let B : Set FourSpace := Subtype.val '' (φ ⁻¹' A)
  have hB : MeasurableSet B :=
    (MeasurableEmbedding.subtype_coe (chartAt FourSpace c).open_target.measurableSet).measurableSet_image'
      (hφ hA)
  have hBt : B ⊆ (chartAt FourSpace c).target := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hBA : (chartAt FourSpace c).symm '' B = A ∩ (chartAt FourSpace c).source := by
    ext x
    constructor
    · rintro ⟨z, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨hq, (chartAt FourSpace c).map_target q.property⟩
    · rintro ⟨hxA, hxs⟩
      refine ⟨chartAt FourSpace c x, ?_, (chartAt FourSpace c).left_inv hxs⟩
      refine ⟨⟨chartAt FourSpace c x, (chartAt FourSpace c).map_source hxs⟩, ?_, rfl⟩
      change (chartAt FourSpace c).symm (chartAt FourSpace c x) ∈ A
      rwa [(chartAt FourSpace c).left_inv hxs]
  have hchart := congrArg (fun μ : Measure FourSpace => μ B)
    (chartHausdorffMeasure_eq_density g c)
  simp only [Measure.restrict_apply hB, inter_eq_left.mpr hBt,
    Measure.smul_apply, smul_eq_mul] at hchart
  rw [chartHausdorffMeasure_apply g c B hB hBt, hBA] at hchart
  have hdensity : ((chartCoordinateMeasure c).withDensity
      (fun z => ENNReal.ofReal (chartVolumeDensity g c z))) (φ ⁻¹' A) =
      (volume.withDensity (fun z => ENNReal.ofReal (chartVolumeDensity g c z))) B := by
    rw [withDensity_apply _ (hφ hA), withDensity_apply _ hB]
    exact setLIntegral_subtype (chartAt FourSpace c).open_target.measurableSet
      (φ ⁻¹' A) (fun z => ENNReal.ofReal (chartVolumeDensity g c z))
  rw [Measure.restrict_apply hA, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hφ hA, hdensity]
  exact hchart

theorem volumeMeasure_restrict_chart (g : SmoothMetric M) (c : M) :
    (volumeMeasure g).restrict (chartAt FourSpace c).source =
      riemannianChartFactor •
        Measure.map (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val)
          ((chartCoordinateMeasure c).withDensity
            (fun z => ENNReal.ofReal (chartVolumeDensity g c z))) := by
  rw [volumeMeasure_eq_scaled_hausdorff, Measure.restrict_smul,
    metricHausdorffMeasure_restrict_chart, smul_smul]
  rfl

def normalizedChartFactor (g : SmoothMetric M) : ℝ≥0∞ :=
  (volumeMeasure g univ)⁻¹ * riemannianChartFactor

theorem normalizedVolume_restrict_chart (g : SmoothMetric M) (c : M) :
    (normalizedVolume g).restrict (chartAt FourSpace c).source =
      normalizedChartFactor g •
        Measure.map (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val)
          ((chartCoordinateMeasure c).withDensity
            (fun z => ENNReal.ofReal (chartVolumeDensity g c z))) := by
  rw [normalizedVolume, Measure.restrict_smul, volumeMeasure_restrict_chart, smul_smul]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial canonical measure in cotangent coordinates, with the base
chart identity derived from the metric Hausdorff measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem actual_unitRadialCotangentState_map (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) :
    Measure.map (unitRadialCotangentState g c)
      (((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o)).restrict
        {p | p.2.base ∈ (chartAt FourSpace c).source}) =
      (normalizedChartFactor g / polarAngularMass) •
        (volume : Measure CotangentCoordinates).restrict
          {p | p.1 ∈ (chartAt FourSpace c).target} := by
  apply unitRadialCotangentState_map g o c
  simpa only [chartBaseDensity] using normalizedVolume_restrict_chart g c

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual local preservation of radial canonical measure. The coordinate
measure is identified from Hausdorff density, and the Hamiltonian determinant
identity is transported through the genuine cotangent chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace KineticLocalFlow

def measurableSlice {g : SmoothMetric M} {c : M} {p : CotangentCoordinates}
    (F : KineticLocalFlow g c p) (t : ℝ) : CotangentCoordinates → CotangentCoordinates :=
  open Classical in
  (Metric.ball p F.radius).piecewise (fun z => F.map (z, t)) (fun _ => 0)

theorem measurableSlice_eq {g : SmoothMetric M} {c : M} {p : CotangentCoordinates}
    (F : KineticLocalFlow g c p) (t : ℝ) (z : CotangentCoordinates)
    (hz : z ∈ Metric.ball p F.radius) : F.measurableSlice t z = F.map (z, t) := by
  classical
  exact piecewise_eq_of_mem _ _ _ hz

theorem measurable_measurableSlice {g : SmoothMetric M} {c : M}
    {p : CotangentCoordinates} (F : KineticLocalFlow g c p) (t : ℝ)
    (ht : t ∈ Ioo (-F.time) F.time) : Measurable (F.measurableSlice t) := by
  classical
  have hc : ContinuousOn (fun z => F.map (z, t)) (Metric.ball p F.radius) :=
    F.continuous_map.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun z hz => ⟨hz, ht⟩)
  exact hc.measurable_piecewise continuousOn_const Metric.isOpen_ball.measurableSet

theorem measurableSlice_map_volume {g : SmoothMetric M} {c : M}
    {p : CotangentCoordinates} (F : KineticLocalFlow g c p) (t : ℝ)
    (ht : t ∈ Ioo (-F.time) F.time) (s : Set CotangentCoordinates)
    (hs : MeasurableSet s) (hsub : s ⊆ Metric.ball p F.radius) :
    Measure.map (F.measurableSlice t) (volume.restrict s) =
      volume.restrict (F.measurableSlice t '' s) := by
  have heq : EqOn (F.measurableSlice t) (fun z => F.map (z, t)) s :=
    fun z hz => F.measurableSlice_eq t z (hsub hz)
  calc
    _ = Measure.map (fun z => F.map (z, t)) (volume.restrict s) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hs] with z hz
      exact heq hz
    _ = volume.restrict ((fun z => F.map (z, t)) '' s) :=
      F.map_volume_restrict t ht s hs hsub
    _ = _ := congrArg (fun A => volume.restrict A) (image_congr heq).symm

end KineticLocalFlow

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem actual_radialCotangentStateExtension_map (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) :
    Measure.map (radialCotangentStateExtension g c)
      (((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o)).restrict
        {p | p.2.base ∈ (chartAt FourSpace c).source}) =
      (normalizedChartFactor g / polarAngularMass) •
        (volume : Measure CotangentCoordinates).restrict
          {p | p.1 ∈ (chartAt FourSpace c).target} := by
  rw [← actual_unitRadialCotangentState_map g o c]
  apply Measure.map_congr
  have hS : MeasurableSet {p : PositiveRadius × UnitTangentBundle g |
      p.2.base ∈ (chartAt FourSpace c).source} :=
    ((chartAt FourSpace c).open_source.preimage
      ((continuous_unitTangentBase g).comp continuous_snd)).measurableSet
  filter_upwards [ae_restrict_mem hS] with p hp
  exact radialCotangentStateExtension_eq g c p hp

/-- Every actual Hamiltonian chart preserves the actual radial measure
on its open domain for the full interval provided by that chart. -/
theorem RadialHamiltonianChart.map_radialMeasure (g : SmoothMetric M)
    (o : FrameOrientation g) (C : RadialHamiltonianChart g o)
    (t : ℝ) (ht : t ∈ Ioo (-C.flow.time) C.flow.time) :
    Measure.map (unitTangentRadialFlow g o t)
      (((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o)).restrict C.domain) =
      ((Measure.volumeIoiPow 3).prod (canonicalUnitTangentMeasure g o)).restrict
        (unitTangentRadialFlow g o t '' C.domain) := by
  let S : Set (PositiveRadius × UnitTangentBundle g) :=
    {p | p.2.base ∈ (chartAt FourSpace C.center).source}
  let f := radialCotangentStateExtension g C.center
  let r := cotangentRadialRetraction g C.center
  let Φ := unitTangentRadialFlow g o t
  let F := C.flow.measurableSlice t
  have hzero : (0 : ℝ) ∈ Ioo (-C.flow.time) C.flow.time := by
    constructor <;> linarith [C.flow.time_pos]
  have hUS : C.domain ⊆ S := by
    intro p hp
    have h := C.trajectory_in_chart p hp 0 hzero
    simpa only [unitTangentRadialFlow_zero] using! h
  have hΦS : Φ '' C.domain ⊆ S := by
    rintro _ ⟨p, hp, rfl⟩
    exact C.trajectory_in_chart p hp t ht
  have hS : MeasurableSet S :=
    ((chartAt FourSpace C.center).open_source.preimage
      ((continuous_unitTangentBase g).comp continuous_snd)).measurableSet
  have heq : EqOn f (unitRadialCotangentState g C.center) S :=
    fun p hp => radialCotangentStateExtension_eq g C.center p hp
  have hfU : f '' C.domain = C.image := by
    rw [C.image_eq]
    exact image_congr (fun p hp => heq (hUS hp))
  have hΦopen : IsOpen (Φ '' C.domain) :=
    (unitTangentRadialHomeomorph g o t).isOpenMap _ C.open_domain
  have hfΦU : IsOpen (f '' (Φ '' C.domain)) := by
    have himage : f '' (Φ '' C.domain) =
        unitRadialCotangentState g C.center '' (Φ '' C.domain) :=
      image_congr (fun p hp => heq (hΦS hp))
    rw [himage]
    exact isOpen_unitRadialCotangentState_image g C.center _ hΦopen hΦS
  apply local_image_measure_of_coordinates _ volume
    (normalizedChartFactor g / polarAngularMass) f r
    (measurable_radialCotangentStateExtension g C.center)
    (measurable_cotangentRadialRetraction g C.center) S
    {z | z.1 ∈ (chartAt FourSpace C.center).target} hS
    (fun p hp => cotangentRadialRetraction_extension g C.center p hp) ?_
    (actual_radialCotangentStateExtension_map g o C.center) Φ F
    (unitTangentRadialFlow_continuous g o t).measurable
    (C.flow.measurable_measurableSlice t ht) C.domain C.open_domain.measurableSet
    hUS hΦS hΦopen.measurableSet ?_ hfΦU.measurableSet ?_ ?_
  · intro p hp
    rw [heq hp]
    exact (chartAt FourSpace C.center).map_source hp
  · rw [hfU]
    exact C.open_image.measurableSet
  · intro p hp
    change f (Φ p) = C.flow.measurableSlice t (f p)
    rw [heq (hΦS ⟨p, hp, rfl⟩), heq (hUS hp),
      C.flow.measurableSlice_eq t _ (C.image_subset_ball (by
        rw [C.image_eq]; exact ⟨p, hp, rfl⟩))]
    exact (C.conjugacy p hp ht).symm
  · rw [hfU]
    exact C.flow.measurableSlice_map_volume t ht C.image C.open_image.measurableSet
      C.image_subset_ball

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth functions as degree-zero covariant fields and their actual
one-form differential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def smoothScalarCovariantField (f : SmoothScalar (M := M)) : smoothCovariantFields M 0 :=
  ⟨fun x _ => f.val x, by
    intro c z hz a
    simpa only [covariantFieldCoordinates, frameTensor_zero, scalarCoordinates] using
      scalarCoordinates_contDiffAt f.property c z hz a⟩

def smoothScalarDifferential (g : SmoothMetric M) (f : SmoothScalar (M := M)) :
    smoothCovariantFields M 1 := smoothCovariantDerivative g (smoothScalarCovariantField f)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual degree-zero differential as a linear map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def smoothScalarCovariantLinear : SmoothScalar (M := M) →ₗ[ℝ] smoothCovariantFields M 0 where
  toFun := smoothScalarCovariantField
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem smoothScalarDifferential_add (f h : SmoothScalar (M := M)) :
    smoothScalarDifferential g (f + h) =
      smoothScalarDifferential g f + smoothScalarDifferential g h := by
  change smoothCovariantDerivative g (smoothScalarCovariantLinear (f + h)) = _
  rw [map_add]
  apply Subtype.ext
  exact covariantFieldDerivative_add (smoothScalarCovariantField f)
    (smoothScalarCovariantField h)

theorem smoothScalarDifferential_smul (r : ℝ) (f : SmoothScalar (M := M)) :
    smoothScalarDifferential g (r • f) = r • smoothScalarDifferential g f := by
  change smoothCovariantDerivative g (smoothScalarCovariantLinear (r • f)) = _
  rw [map_smul]
  apply Subtype.ext
  exact covariantFieldDerivative_smul r (smoothScalarCovariantField f)

def smoothScalarDifferentialLinear (g : SmoothMetric M) :
    SmoothScalar (M := M) →ₗ[ℝ] smoothCovariantFields M 1 where
  toFun := smoothScalarDifferential g
  map_add' := smoothScalarDifferential_add
  map_smul' := smoothScalarDifferential_smul

end
end PositiveEinsteinFour.Geometry
end


section

/-! Inverse-metric contraction preserves actual smooth covariant fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def smoothCovariantMetricTrace (T : smoothCovariantFields M 3) : smoothCovariantFields M 1 :=
  ⟨covariantMetricTraceField g T.val, T.property.metricTrace⟩

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

/-! Finite regularity of the actual pulled-back normal-frame connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatNormalFrameConnection_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : ContDiffAt ℝ (n + 1 : ℕ) P x)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target) (hdet : (P x).2.det ≠ 0)
    (i j k : Fin 4) :
    ContDiffAt ℝ n (fun y => heatNormalFrameConnection g c P i y j k) x := by
  have hP0 : ContDiffAt ℝ n P x := hP.of_le (by exact_mod_cast Nat.le_succ n)
  have hE (a b : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2 a b) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP0.snd a) b
  have hEi (a b : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2⁻¹ a b) x :=
    heatMatrixInverse_contDiffAt n (fun y => (P y).2) x hE hdet a b
  have hD : ContDiffAt ℝ n (fun y => fderiv ℝ P y (coordinateVector i)) x :=
    (hP.fderiv_right (m := n) (by norm_num [Nat.cast_add])).clm_apply contDiffAt_const
  have hDE (a b : Fin 4) : ContDiffAt ℝ n
      (fun y => (fderiv ℝ P y (coordinateVector i)).2 a b) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hD.snd a) b
  have hDZ (a : Fin 4) : ContDiffAt ℝ n
      (fun y => (fderiv ℝ P y (coordinateVector i)).1 a) x := by
    let π : FourSpace →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 4 => ℝ) a
    exact π.contDiff.contDiffAt.comp x hD.fst
  have hΓ (r a b : Fin 4) : ContDiffAt ℝ n
      (fun y => christoffel g c (P y).1 a r b) x := by
    exact ContDiffAt.comp (f := fun y => (P y).1)
      (g := fun z => christoffel g c z a r b) x
      ((christoffel_contDiffAt g c (P x).1 hx
        (metricInChart_posDef g c (P x).1 hx).det_pos.ne' a r b).of_le (by first | simp | exact_mod_cast le_top)) hP0.fst
  change ContDiffAt ℝ n (fun y => ∑ l : Fin 4, (P y).2⁻¹ j l *
    ((fderiv ℝ P y (coordinateVector i)).2 l k +
      ∑ a : Fin 4, (∑ r : Fin 4, (fderiv ℝ P y (coordinateVector i)).1 r *
        christoffel g c (P y).1 l r a) * (P y).2 a k)) x
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

/-! The local H¹ derivatives give genuine global weak derivatives after a
compact cutoff. No differentiability of an L² representative is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

theorem scalar_partial_product (f q : FourSpace → ℝ) (z : FourSpace)
    (hf : DifferentiableAt ℝ f z) (hq : DifferentiableAt ℝ q z) (i : Fin 4) :
    partialDeriv (fun w => f w * q w) i z =
      partialDeriv f i z * q z + f z * partialDeriv q i z := by
  simp only [partialDeriv, fderiv_fun_mul hf hq, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

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

/-! The radial identity for the actual exponential pullback metric,
and the resulting cancellation of the Gaussian eikonal defect. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix
open scoped Manifold ContDiff _root_.Topology InnerProductSpace BigOperators

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalMetric_symm (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) : (heatNormalMetric g o e v)ᵀ = heatNormalMetric g o e v := by
  ext i j
  exact g.symm _ _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local four-component heat operator in a radial frame. The additional
first-order Gaussian term vanishes by the radial connection identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

def fourHeatOneFirst (B : Fin 4 → Mat4) (u : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (k : Fin 4) : ℝ :=
  ∑ i : Fin 4, ∑ l : Fin 4, B i k l * partialDeriv (fun y => u y l) i x

def fourHeatOneZero (C : Mat4) (u : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (k : Fin 4) : ℝ := ∑ l : Fin 4, C k l * u x l

def fourHeatOneOperator (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) (u : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (k : Fin 4) : ℝ :=
  fourHeatLocalOperator a b 0 (fun y => u y k) x +
    fourHeatOneFirst B u x k + fourHeatOneZero C u x k

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normalized leading scalar amplitude solves its transport
equation on a normal-coordinate ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalInverse_symm (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (x : FourSpace) :
    ((heatNormalMetric g o e x)⁻¹)ᵀ = (heatNormalMetric g o e x)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, heatNormalMetric_symm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite regularity of the actual differential expression used in the
heat transport recursion. Each application loses two derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

theorem fourHeat_partial_contDiff (n : ℕ) (u : FourSpace → ℝ)
    (hu : ContDiff ℝ (n + 1 : ℕ) u) (i : Fin 4) :
    ContDiff ℝ n (partialDeriv u i) :=
  (hu.fderiv_right (m := n) (by norm_num [Nat.cast_add])).clm_apply
    (contDiff_const (c := coordinateVector i))

theorem fourHeatLocalOperator_contDiff (n : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ) (c u : FourSpace → ℝ)
    (ha : ∀ i j, ContDiff ℝ n (fun x => a x i j))
    (hb : ∀ i, ContDiff ℝ n (fun x => b x i)) (hc : ContDiff ℝ n c)
    (hu : ContDiff ℝ (n + 2 : ℕ) u) :
    ContDiff ℝ n (fun x => fourHeatLocalOperator (a x) (b x) (c x) u x) := by
  have hp (i : Fin 4) : ContDiff ℝ (n + 1 : ℕ) (partialDeriv u i) := by
    apply fourHeat_partial_contDiff (n + 1) u _ i
    simpa only [Nat.add_assoc] using hu
  have hpp (i j : Fin 4) : ContDiff ℝ n (partialDeriv (partialDeriv u i) j) :=
    fourHeat_partial_contDiff n _ (hp i) j
  have hp' (i : Fin 4) : ContDiff ℝ n (partialDeriv u i) :=
    (hp i).of_le (by exact_mod_cast Nat.le_succ n)
  have hu' : ContDiff ℝ n u := hu.of_le (by exact_mod_cast Nat.le_add_right n 2)
  exact ((ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => (ha i j).mul
    (hpp i j)))).neg.add (ContDiff.sum (fun i _ => (hb i).mul (hp' i)))).add
      (hc.mul hu')

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linearity of the local heat operator on actual twice differentiable
functions. These formulas allow cancellation in the finite heat ansatz. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

theorem fourHeat_partial_add (u v : FourSpace → ℝ) (x : FourSpace)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) (i : Fin 4) :
    partialDeriv (fun y => u y + v y) i x = partialDeriv u i x + partialDeriv v i x := by
  simp only [partialDeriv, fderiv_fun_add hu hv, _root_.add_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite third-order scalar heat ansatz and its exact differential
identities. The coefficients here are actual scalar functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

def fourHeatPolynomial (u : Fin 4 → FourSpace → ℝ) (t : ℝ) (x : FourSpace) : ℝ :=
  u 0 x + t * u 1 x + t ^ 2 * u 2 x + t ^ 3 * u 3 x

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linearity and finite time polynomials for the actual six-component
differential expression. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

def fourHeatBundlePolynomial (u : Fin 4 → FourSpace → Fin 6 → ℝ)
    (t : ℝ) (x : FourSpace) (k : Fin 6) : ℝ :=
  fourHeatPolynomial (fun m y => u m y k) t x

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coordinate product rule for two successive covariant derivatives
of four-component fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeat_partial_sum_oneForm (f : Fin 4 → FourSpace → ℝ) (x : FourSpace)
    (hf : ∀ l, DifferentiableAt ℝ (f l) x) (i : Fin 4) :
    partialDeriv (fun y => ∑ l : Fin 4, f l y) i x =
      ∑ l : Fin 4, partialDeriv (f l) i x := by
  unfold partialDeriv
  rw [fderiv_fun_sum (u := Finset.univ) (A := f) (fun l _ => hf l), _root_.sum_apply]

theorem fourHeatOneCovariantDerivative_partial (A : Fin 4 → FourSpace → Mat4)
    (u : FourSpace → Fin 4 → ℝ) (x : FourSpace)
    (hA : ∀ i k l, DifferentiableAt ℝ (fun y => A i y k l) x)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) (i j : Fin 4) (k : Fin 4) :
    partialDeriv (fun y => fourHeatOneCovariantDerivative A u i y k) j x =
      partialDeriv (partialDeriv (fun y => u y k) i) j x +
        (∑ l : Fin 4, partialDeriv (fun y => A i y k l) j x * u x l) +
        ∑ l : Fin 4, A i x k l * partialDeriv (fun y => u y l) j x := by
  have hu0 (l : Fin 4) : DifferentiableAt ℝ (fun y => u y l) x :=
    (hu l).differentiableAt (by norm_num)
  have hdu : DifferentiableAt ℝ (partialDeriv (fun y => u y k) i) x :=
    (((hu k).fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiffAt_const (c := coordinateVector i))).differentiableAt one_ne_zero
  have hprod (l : Fin 4) : DifferentiableAt ℝ (fun y => A i y k l * u y l) x :=
    (hA i k l).mul (hu0 l)
  have hsum : DifferentiableAt ℝ (fun y => ∑ l : Fin 4, A i y k l * u y l) x :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun l _ => hprod l)
  unfold fourHeatOneCovariantDerivative
  rw [fourHeat_partial_add (partialDeriv (fun y => u y k) i)
    (fun y => ∑ l : Fin 4, A i y k l * u y l) x hdu hsum j,
    fourHeat_partial_sum_oneForm (fun l y => A i y k l * u y l) x hprod j]
  simp only [scalar_partial_product _ _ x (hA i k _) (hu0 _) j, Finset.sum_add_distrib]
  ring

theorem fourHeatOneCovariantDerivative_second (A : Fin 4 → FourSpace → Mat4)
    (u : FourSpace → Fin 4 → ℝ) (x : FourSpace)
    (hA : ∀ i k l, DifferentiableAt ℝ (fun y => A i y k l) x)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) (i j : Fin 4) (k : Fin 4) :
    fourHeatOneCovariantDerivative A (fourHeatOneCovariantDerivative A u i) j x k =
      partialDeriv (partialDeriv (fun y => u y k) i) j x +
        (∑ l : Fin 4, A i x k l * partialDeriv (fun y => u y l) j x) +
        (∑ l : Fin 4, A j x k l * partialDeriv (fun y => u y l) i x) +
        ∑ l : Fin 4, (partialDeriv (fun y => A i y k l) j x +
          (A j x * A i x) k l) * u x l := by
  change partialDeriv (fun y => fourHeatOneCovariantDerivative A u i y k) j x +
    (∑ l : Fin 4, A j x k l * fourHeatOneCovariantDerivative A u i x l) = _
  rw [fourHeatOneCovariantDerivative_partial A u x hA hu]
  have hquad : (∑ l : Fin 4, A j x k l * ∑ q : Fin 4, A i x l q * u x q) =
      ∑ q : Fin 4, (A j x * A i x) k q * u x q := by
    simp only [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp only [fourHeatOneCovariantDerivative, mul_add, Finset.sum_add_distrib]
  rw [hquad]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Expansion of the connection Laplacian into the exact coefficient
operator used in the bundle heat construction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

def fourHeatOneCovariantOperator (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → Mat4) (V : Mat4)
    (u : FourSpace → Fin 4 → ℝ) (x : FourSpace) (k : Fin 4) : ℝ :=
  -(∑ i : Fin 4, ∑ j : Fin 4, a i j *
      fourHeatOneCovariantDerivative A (fourHeatOneCovariantDerivative A u i) j x k) +
    (∑ i : Fin 4, b i * fourHeatOneCovariantDerivative A u i x k) +
    ∑ l : Fin 4, V k l * u x l

theorem fourHeatOneCovariantOperator_eq (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → Mat4) (V : Mat4)
    (u : FourSpace → Fin 4 → ℝ) (x : FourSpace)
    (hs : ∀ i j, a i j = a j i)
    (hA : ∀ i k l, DifferentiableAt ℝ (fun y => A i y k l) x)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) (k : Fin 4) :
    fourHeatOneCovariantOperator a b A V u x k =
      fourHeatOneOperator a b (fourHeatOneConnectionFirst a (fun i => A i x))
        (fourHeatOneConnectionZero a b A V x) u x k := by
  let Q := ∑ i : Fin 4, ∑ j : Fin 4, a i j *
    (∑ l : Fin 4, A j x k l * partialDeriv (fun y => u y l) i x)
  let Z := ∑ i : Fin 4, ∑ j : Fin 4, a i j *
    (∑ l : Fin 4, (partialDeriv (fun y => A i y k l) j x +
      (A j x * A i x) k l) * u x l)
  let Y := ∑ i : Fin 4, b i * (∑ l : Fin 4, A i x k l * u x l)
  have hswap : (∑ i : Fin 4, ∑ j : Fin 4, a i j *
      (∑ l : Fin 4, A i x k l * partialDeriv (fun y => u y l) j x)) = Q := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs]
  have hsecond : (∑ i : Fin 4, ∑ j : Fin 4, a i j *
      fourHeatOneCovariantDerivative A (fourHeatOneCovariantDerivative A u i) j x k) =
      (∑ i : Fin 4, ∑ j : Fin 4, a i j *
        partialDeriv (partialDeriv (fun y => u y k) i) j x) + 2 * Q + Z := by
    simp_rw [fourHeatOneCovariantDerivative_second A u x hA hu]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hswap]
    dsimp only [Q, Z]
    ring
  have hfirst : fourHeatOneFirst (fourHeatOneConnectionFirst a (fun i => A i x)) u x k = -2 * Q := by
    change (∑ i : Fin 4, ∑ l : Fin 4,
      (-2 * ∑ j : Fin 4, a i j * A j x k l) * partialDeriv (fun y => u y l) i x) = _
    dsimp only [Q]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hY : (∑ l : Fin 4, (∑ i : Fin 4, b i * A i x k l) * u x l) = Y := by
    dsimp only [Y]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hZ : (∑ l : Fin 4, (∑ i : Fin 4, ∑ j : Fin 4, a i j *
      (partialDeriv (fun y => A i y k l) j x + (A j x * A i x) k l)) * u x l) = Z := by
    dsimp only [Z]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hzero : fourHeatOneZero (fourHeatOneConnectionZero a b A V x) u x k =
      (∑ l : Fin 4, V k l * u x l) + Y - Z := by
    change (∑ l : Fin 4, (V k l + (∑ i : Fin 4, b i * A i x k l) -
      (∑ i : Fin 4, ∑ j : Fin 4, a i j *
        (partialDeriv (fun y => A i y k l) j x + (A j x * A i x) k l))) * u x l) = _
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hY, hZ]
  unfold fourHeatOneCovariantOperator fourHeatOneOperator
  rw [hsecond, hfirst, hzero]
  simp only [fourHeatOneCovariantDerivative, mul_add, Finset.sum_add_distrib]
  dsimp only [Y]
  unfold fourHeatLocalOperator
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal-frame bundle parametrix through order three. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def heatNormalBundleParametrix {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (t : ℝ) (x : FourSpace) : HeatMat6 :=
  fun k l => fourHeatGaussian t x *
    fourHeatBundlePolynomial (fun m y q => E.amplitude m y q l) t x k

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

def smoothTwoFormCodifferential : smoothTwoForms o →ₗ[ℝ] (FrameBundle g → Fin 4 → ℝ) where
  toFun u e k := twoFormCodiffComponent
    (fun p q r => twoFormFramedCovariantDerivative o u.val e ![p,q,r]) k
  map_add' u v := by
    funext e k
    simp only [twoFormCodiffComponent, twoFormFramedCovariantDerivative_add, Pi.add_apply,
      Finset.sum_add_distrib, neg_add]
  map_smul' r u := by
    funext e k
    change -(∑ i, twoFormFramedCovariantDerivative o (r • u.val) e ![i,i,k]) = _
    simp only [twoFormFramedCovariantDerivative_smul, Pi.smul_apply, smul_eq_mul,
      ← Finset.mul_sum, RingHom.id_apply]
    simp only [twoFormCodiffComponent, mul_neg]

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

/-! The codifferential of a smooth two-form is an actual smooth one-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothTwoFormCodifferentialField (u : smoothTwoForms o) : smoothCovariantFields M 1 :=
  smoothCovariantMetricTrace (g := g)
    (smoothCovariantDerivative g (smoothTwoFormCovariantField u))

theorem smoothTwoFormCovariantField_derivative_framed (u : smoothTwoForms o)
    (e : FrameBundle g) :
    covariantFieldFramed g (covariantFieldDerivative g (smoothTwoFormCovariantField u).val) e =
      twoFormFramedCovariantDerivative o u.val e := by
  rw [covariantFieldFramed_eq]
  rfl

theorem smoothTwoFormCodifferentialField_framed (u : smoothTwoForms o) (e : FrameBundle g) :
    covariantFieldFramed g (smoothTwoFormCodifferentialField u).val e =
      twoFormCodiffTensor (twoFormFramedCovariantDerivative o u.val e) := by
  have h := covariantMetricTraceField_framed
    (covariantFieldDerivative g (smoothTwoFormCovariantField u).val) e
  exact h.trans (congrArg twoFormCodiffTensor (smoothTwoFormCovariantField_derivative_framed u e))

theorem smoothTwoFormCodifferentialField_component (u : smoothTwoForms o)
    (e : FrameBundle g) (k : Fin 4) :
    covariantFieldFramed g (smoothTwoFormCodifferentialField u).val e ![k] =
      smoothTwoFormCodifferential u e k := by
  rw [smoothTwoFormCodifferentialField_framed]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual one-form components and the Levi-Civita derivative in the normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

omit [IsManifold I4 ∞ M] in
theorem heatNormalOneFormValue_regular (n : ℕ) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (u : smoothCovariantFields M 1)
    (x : FourSpace) (hP : ContDiffAt ℝ n P x)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target) (k : Fin 4) :
    ContDiffAt ℝ n (fun y => heatNormalOneFormValue c P u y k) x := by
  have hE (i j : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2 i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP.snd i) j
  have hT (a : Fin 1 → Fin 4) : ContDiffAt ℝ n
      (fun y => covariantFieldCoordinates u.val c (P y).1 a) x :=
    ContDiffAt.comp (f := fun y => (P y).1)
      (g := fun z => covariantFieldCoordinates u.val c z a) x
      ((u.property c (P x).1 hx a).of_le (by first | simp | exact_mod_cast le_top)) hP.fst
  unfold heatNormalOneFormValue frameTensor
  exact ContDiffAt.sum (fun a _ => (contDiffAt_prod (fun i _ => hE (a i) (![k] i))).mul (hT a))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual two-form codifferential as a linear map to smooth one-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoFormCodifferentialField_add (u v : smoothTwoForms o) :
    smoothTwoFormCodifferentialField (u + v) =
      smoothTwoFormCodifferentialField u + smoothTwoFormCodifferentialField v := by
  apply Subtype.ext
  apply covariantField_eq_of_framed (g := g)
  intro e
  simp only [Submodule.coe_add, covariantFieldFramed_add]
  funext a
  have ha : a = ![a 0] := by ext i; fin_cases i; rfl
  rw [ha]
  simp only [Pi.add_apply, smoothTwoFormCodifferentialField_component]
  exact congrFun (congrFun (map_add (smoothTwoFormCodifferential (o := o)) u v) e) (a 0)

theorem smoothTwoFormCodifferentialField_smul (r : ℝ) (u : smoothTwoForms o) :
    smoothTwoFormCodifferentialField (r • u) = r • smoothTwoFormCodifferentialField u := by
  apply Subtype.ext
  apply covariantField_eq_of_framed (g := g)
  intro e
  simp only [Submodule.coe_smul, covariantFieldFramed_smul]
  funext a
  have ha : a = ![a 0] := by ext i; fin_cases i; rfl
  rw [ha]
  simp only [Pi.smul_apply, smul_eq_mul, smoothTwoFormCodifferentialField_component]
  exact congrFun (congrFun (map_smul (smoothTwoFormCodifferential (o := o)) r u) e) (a 0)

def smoothTwoFormCodifferentialLinear :
    smoothTwoForms o →ₗ[ℝ] smoothCovariantFields M 1 where
  toFun := smoothTwoFormCodifferentialField
  map_add' := smoothTwoFormCodifferentialField_add
  map_smul' := smoothTwoFormCodifferentialField_smul

end
end PositiveEinsteinFour.Geometry
end


section

/-! First and second covariant derivatives in the actual four-component frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem heat_oneForm_covariant_second (A : Fin 4 → FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates 1) (x : FourSpace) (i j k : Fin 4)
    (hA : ∀ᶠ y in 𝓝 x, ∀ l, (A l y)ᵀ = -A l y) :
    tensorCovariantDirection A (tensorCovariantDirection A T i) j x ![k] =
      fourHeatOneCovariantDerivative A
        (fourHeatOneCovariantDerivative A (fun y l => T y ![l]) i) j x k := by
  have he (l : Fin 4) : (fun y => tensorCovariantDirection A T i y ![l]) =ᶠ[𝓝 x]
      (fun y => fourHeatOneCovariantDerivative A (fun z q => T z ![q]) i y l) := by
    filter_upwards [hA] with y hy
    exact heat_oneForm_covariant_component A T y i l (hy i)
  rw [heat_oneForm_covariant_component A (tensorCovariantDirection A T i) x j k (hA.self_of_nhds j)]
  change partialDeriv _ j x + (∑ l, A j x k l * _) = _
  have hd : partialDeriv (fun y => tensorCovariantDirection A T i y ![k]) j x =
      partialDeriv (fun y => fourHeatOneCovariantDerivative A (fun z q => T z ![q]) i y k) j x :=
    congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector j)) (he k).fderiv_eq
  rw [hd]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  exact congrArg (A j x k l * ·) (he l).self_of_nhds

end
end PositiveEinsteinFour.Geometry
end


section

/-! The degree-one Hodge Laplacian is the actual dδ+δd operator.
Its symmetry and nonnegative energy follow from the geometric adjoints. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothOneFormHodgeLaplacian : smoothCovariantFields M 1 →ₗ[ℝ] smoothCovariantFields M 1 :=
  (smoothTwoFormCodifferentialLinear (o := o)).comp smoothOneFormExteriorLinear -
    (smoothScalarDifferentialLinear g).comp (smoothOneFormDivergence g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The one-form transport operator is the actual geometric Hodge Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.oneValue_as_actual (D : HeatNormalFrameData g o c e)
    (u : smoothCovariantFields M 1) (x : FourSpace) (hx : x ∈ ball 0 D.radius) (k : Fin 4) :
    heatNormalOneFormValue c D.point u x k = covariantFieldFramed g u.val (D.frame x hx) ![k] := by
  rw [heat_covariantField_chart g u.val c (D.frame x hx)
    ((chartAt FourSpace c).map_target (D.in_chart x hx))]
  have hm : frameChartMatrix g c (D.frame x hx) = (D.point x).2 :=
    frameChartMatrix_chartFrameState g c
      ⟨D.point x, D.in_chart x hx, D.orthonormal x hx⟩
  have hb : chartAt FourSpace c (D.frame x hx).base = (D.point x).1 :=
    (chartAt FourSpace c).right_inv (D.in_chart x hx)
  rw [hm, hb]
  rfl

theorem HeatNormalFrameData.oneRough_components_at (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (hP : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hd : 0 < (heatNormalMetric g o e x).det)
    (u : smoothCovariantFields M 1) (k : Fin 4) :
    -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
      fourHeatOneCovariantDerivative (heatNormalFrameConnection g c D.point)
        (fourHeatOneCovariantDerivative (heatNormalFrameConnection g c D.point)
          (heatNormalOneFormValue c D.point u) i) j x k) +
      (∑ i, heatNormalDrift g o e x i *
        fourHeatOneCovariantDerivative (heatNormalFrameConnection g c D.point)
          (heatNormalOneFormValue c D.point u) i x k) =
      -(∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        (D.frame x hx) ![i,i,k]) := by
  have hsk : ∀ᶠ y in 𝓝 x, ∀ i, (heatNormalFrameConnection g c D.point i y)ᵀ =
      -heatNormalFrameConnection g c D.point i y := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact D.connection_skew y hy
  have h := D.oneTensor_rough_at x hx hP hs hd u k
  simp_rw [heat_oneForm_covariant_second _ _ x _ _ k hsk,
    heat_oneForm_covariant_component _ _ x _ k (hsk.self_of_nhds _)] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


