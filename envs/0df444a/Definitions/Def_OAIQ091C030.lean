-- Prove2me | Definitions.Def_OAIQ091C030
-- name    : OAIQ091C030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:02:48.786212+00:00
-- url     : https://prove2.me/theorems/9e8fb64e-c570-44ba-881a-60ceb56bde60
-- title:
--   Definitions bundle OAIQ091C030 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 149 declarations of OpenAI's Lean: 28 definitions and 121 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.oneFormCoexactEigensection`, `OAI.PositiveEinsteinFour.Geometry.oneFormCoexactLift`, `OAI.PositiveEinsteinFour.Geometry.oneFormCoexactLiftL2`, `OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSynthesis`, `OAI.PositiveEinsteinFour.Geometry.oneFormCoexactToTwoFormIndex`, `OAI.PositiveEinsteinFour.Geometry.oneFormEigenbasis`, `OAI.PositiveEinsteinFour.Geometry.oneFormExactSpectralLift`, `OAI.PositiveEinsteinFour.Geometry.oneFormExactSynthesis`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeat`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeatConvolution`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeatDiagonal`, `OAI.PositiveEinsteinFour.Geometry.oneFormInverseSquareRoot`, `OAI.PositiveEinsteinFour.Geometry.oneFormScalarPotential`, `OAI.PositiveEinsteinFour.Geometry.oneFormSpectralEquiv`, `OAI.PositiveEinsteinFour.Geometry.oneFormSpectralMultiplier`, `OAI.PositiveEinsteinFour.Geometry.scalarBaseHeatLiftSource`, `OAI.PositiveEinsteinFour.Geometry.scalarHeatColumn`, `OAI.PositiveEinsteinFour.Geometry.scalarHeatContinuousLinear`, `OAI.PositiveEinsteinFour.Geometry.scalarHeatContinuousValue`, `OAI.PositiveEinsteinFour.Geometry.scalarHeatEvaluation`, `OAI.PositiveEinsteinFour.Geometry.scalarHeatH1Lift`, `OAI.PositiveEinsteinFour.Geometry.scalarHeatToContinuous`, `OAI.PositiveEinsteinFour.Geometry.scalarPositiveSynthesis`, `OAI.PositiveEinsteinFour.Geometry.smoothH1CodifferentialCLM`, `OAI.PositiveEinsteinFour.Geometry.twoFormH1Codifferential`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatChartContinuous`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatSection`, `OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_GeodesicGeometry06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry06.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory09.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C044` and `OAIQ091C028` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C032`, `OAIQ091C033`, `OAIQ091C048`, `OAIQ091C049`, `OAIQ091C050`, `OAIQ091C051`, `OAIQ091C052`, `OAIQ091C053` and `OAIQ091C055`; the proof of `OAI.PositiveEinsteinFour.Geometry.actual_frameExponential_injOn_sqrt_three`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C044
import Definitions.Def_OAIQ091C028

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Compactness and the local no-corner argument give a minimizing radial
geodesic to every point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem frameGeodesic_reaches_of_positive_split (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (q : M) (r : ℝ) (hr : 0 < r)
    (hrsplit : r ∈ frameDistanceSplitTimes g e q) :
    frameGeodesic g 0 e (metricDistance g e.base q) = q := by
  obtain ⟨a, ha, hmax⟩ := (frameDistanceSplitTimes_compact g e q).exists_isMaxOn
    ⟨r, hrsplit⟩ continuous_id.continuousOn
  have hapos : 0 < a := hr.trans_le (hmax hrsplit)
  have had : a ≤ metricDistance g e.base q := by
    linarith [metricDistance_nonneg g (frameGeodesic g 0 e a) q, ha.2.2]
  have heq : a = metricDistance g e.base q := by
    apply le_antisymm had
    by_contra hnot
    have hlt : a < metricDistance g e.base q := lt_of_not_ge hnot
    obtain ⟨b, hb, _, hbm, hbs⟩ := frameGeodesic_minimizing_split_extends g o hRic e he q a
      hapos hlt ha.2.1 ha.2.2
    have hbmem : a + b ∈ frameDistanceSplitTimes g e q := ⟨by linarith, hbm, hbs⟩
    have hle : a + b ≤ a := hmax hbmem
    linarith
  have hz : metricDistance g (frameGeodesic g 0 e a) q = 0 := by linarith [ha.2.2]
  rw [← heq]
  exact (metricDistance_eq_zero_iff g _ _).mp hz

theorem frameExponential_global_minimizing (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (q : M) :
    ∃ v : FourSpace, frameExponential g o e v = q ∧ ‖v‖ = metricDistance g e.base q := by
  by_cases hzero : metricDistance g e.base q = 0
  · refine ⟨0, ?_, by simpa only [norm_zero] using hzero.symm⟩
    rw [frameExponential_zero]
    exact (metricDistance_eq_zero_iff g _ _).mp hzero
  have hd : 0 < metricDistance g e.base q :=
    lt_of_le_of_ne (metricDistance_nonneg g e.base q) (Ne.symm hzero)
  obtain ⟨R, hR, himages⟩ := exists_frameExponential_normal_ball_images g o hRic e he
  let r := min R (metricDistance g e.base q) / 2
  have hr : 0 < r := half_pos (lt_min hR hd)
  have hrm : r < min R (metricDistance g e.base q) := half_lt_self (lt_min hR hd)
  have hrR : r < R := hrm.trans_le (min_le_left _ _)
  have hrd : r < metricDistance g e.base q := hrm.trans_le (min_le_right _ _)
  obtain ⟨z, hz, hsplit⟩ := exists_metricDistance_real_split g e.base q r hr.le hrd.le
  have hzmem : z ∈ frameExponential g o e '' sphere 0 r := by
    rw [(himages r hr.le hrR).2]
    exact (metricDistance_eq_iff g e.base z hr.le).mp hz
  obtain ⟨v, hv, hvz⟩ := hzmem
  have hvn : ‖v‖ = r := by simpa only [mem_sphere, dist_zero_right] using hv
  let w : FourSpace := r⁻¹ • v
  have hwn : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), hvn, inv_mul_cancel₀ hr.ne']
  let Q := directionOrientedMatrix ⟨w, hwn⟩
  let f := e.rotate (orientedToOrthogonal Q)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hdir : orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
      (orientedToOrthogonal Q).property (coordinateVector 0) = w :=
    directionRotation_first ⟨w, hwn⟩
  have hexp (s : ℝ) : frameGeodesic g 0 f s = frameExponential g o e (s • w) := by
    rw [← frameExponential_first_ray_all g o f hf s, frameExponential_rotate]
    rw [map_smul, hdir]
  have hstart : frameGeodesic g 0 f r = z := by
    rw [hexp, show r • w = v by simp [w, smul_smul, hr.ne'], hvz]
  have hrmem : r ∈ frameDistanceSplitTimes g f q := by
    change 0 ≤ r ∧ metricDistance g e.base (frameGeodesic g 0 f r) = r ∧
      metricDistance g e.base q = r + metricDistance g (frameGeodesic g 0 f r) q
    rw [hstart]
    exact ⟨hr.le, hz, hsplit⟩
  have hend := frameGeodesic_reaches_of_positive_split g o hRic f hf q r hr hrmem
  refine ⟨metricDistance g e.base q • w, ?_, ?_⟩
  · rw [← hexp]
    exact hend
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (metricDistance_nonneg g e.base q), hwn, mul_one]

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

theorem actualMinimizingTangentDomain_image (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) :
    frameExponential g o e '' actualMinimizingTangentDomain g o e = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨v, hv, hn⟩ := frameExponential_global_minimizing g o hRic e he q
  exact ⟨v, by change metricDistance g e.base (frameExponential g o e v) = ‖v‖; rw [hv, hn], hv⟩

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

variable [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem volumeMeasure_le_exponentialAreaMeasure_on_chart (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (c : M) (A : Set M) (hA : MeasurableSet A)
    (hAc : A ⊆ (chartAt FourSpace c).source) :
    volumeMeasure g A ≤ exponentialAreaMeasure g o e A := by
  let s := (frameExponential g o e) ⁻¹' A ∩ actualMinimizingTangentDomain g o e
  let F := fun v => chartCoordinateExtension c (frameExponential g o e v)
  let D := fun v => fderiv ℝ (fun w => chartAt FourSpace c (frameExponential g o e w)) v
  have hs : MeasurableSet s := ((frameExponential_continuous g o e).measurable hA).inter
    (actualMinimizingTangentDomain_closed g o e).measurableSet
  have hF : Measurable F := (chartCoordinateExtension_measurable c).comp
    (frameExponential_continuous g o e).measurable
  have hD : ∀ v ∈ s, HasFDerivWithinAt F (D v) s v := by
    intro v hv
    have hx : frameExponential g o e v ∈ (chartAt FourSpace c).source := hAc hv.1
    have hd := (frameExponential_chart_contDiffAt g o c e v hx).differentiableAt (by first | simp | exact_mod_cast le_top)
    have hnear := (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hx)
    have heq : F =ᶠ[𝓝 v] (fun w => chartAt FourSpace c (frameExponential g o e w)) := by
      filter_upwards [hnear] with w hw
      exact chartCoordinateExtension_eq c _ hw
    exact (hd.hasFDerivAt.congr_of_eventuallyEq heq).hasFDerivWithinAt
  have himage : F '' s = (chartAt FourSpace c) '' A := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨frameExponential g o e v, hv.1, (chartCoordinateExtension_eq c _ (hAc hv.1)).symm⟩
    · rintro ⟨x, hx, rfl⟩
      have hximage : x ∈ frameExponential g o e '' actualMinimizingTangentDomain g o e := by
        rw [actualMinimizingTangentDomain_image g o hRic e he]
        trivial
      obtain ⟨v, hv, hvx⟩ := hximage
      refine ⟨v, ⟨by change frameExponential g o e v ∈ A; rwa [hvx], hv⟩, ?_⟩
      dsimp [F]
      rw [hvx, chartCoordinateExtension_eq c x (hAc hx)]
  have hb := weighted_area_inequality hs hF hD (chartWeight g c) (chartWeight_measurable g c)
  rw [himage] at hb
  have hleft : (∫⁻ z in (chartAt FourSpace c) '' A, chartWeight g c z) =
      ∫⁻ z in (chartAt FourSpace c) '' A, ENNReal.ofReal (chartVolumeDensity g c z) := by
    apply setLIntegral_congr_fun (chart_image_measurable c A hA hAc)
    rintro z ⟨x, hx, rfl⟩
    exact chartWeight_eq g c _ ((chartAt FourSpace c).map_source (hAc hx))
  have hright : (∫⁻ v in s, ENNReal.ofReal |(D v).det| * chartWeight g c (F v)) =
      ∫⁻ v in s, ENNReal.ofReal (frameExponentialJacobian g o e v) := by
    apply setLIntegral_congr_fun hs
    intro v hv
    have hx : frameExponential g o e v ∈ (chartAt FourSpace c).source := hAc hv.1
    dsimp [F, D]
    rw [chartCoordinateExtension_eq c _ hx,
      chartWeight_eq g c _ ((chartAt FourSpace c).map_source hx),
      ← ENNReal.ofReal_mul (abs_nonneg _), mul_comm,
      ← frameExponentialJacobian_chart g o e c v hx]
  rw [hleft, hright] at hb
  rw [volumeMeasure_chart_image g c A hA hAc, exponentialAreaMeasure_apply g o e A hA]
  exact mul_le_mul_right hb riemannianChartFactor

variable [SecondCountableTopology M]

theorem volumeMeasure_le_exponentialAreaMeasure (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) : volumeMeasure g ≤ exponentialAreaMeasure g o e := by
  have h := measure_restrict_le_of_local (volumeMeasure g) (exponentialAreaMeasure g o e)
    univ isOpen_univ (fun x _ => ?_)
  · simpa only [Measure.restrict_univ] using h
  refine ⟨(chartAt FourSpace x).source, (chartAt FourSpace x).open_source,
    mem_chart_source FourSpace x, subset_univ _, ?_⟩
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  exact volumeMeasure_le_exponentialAreaMeasure_on_chart g o hRic e he x
    (A ∩ (chartAt FourSpace x).source) (hA.inter (chartAt FourSpace x).open_source.measurableSet)
    inter_subset_right

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]

variable [SecondCountableTopology M]

theorem volume_lintegral_le_weighted_exponential (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (W : M → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ y, W y ∂volumeMeasure g) ≤ riemannianChartFactor *
      ∫⁻ v in actualMinimizingTangentDomain g o e,
        ENNReal.ofReal (frameExponentialJacobian g o e v) * W (frameExponential g o e v) := by
  have h := lintegral_mono' (volumeMeasure_le_exponentialAreaMeasure g o hRic e he)
    (le_rfl : W ≤ W)
  rw [exponentialAreaMeasure, lintegral_smul_measure,
    lintegral_map hW (frameExponential_continuous g o e).measurable] at h
  have hj : Measurable (fun v => ENNReal.ofReal (frameExponentialJacobian g o e v)) :=
    ENNReal.measurable_ofReal.comp (frameExponentialJacobian_continuous g o e).measurable
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hj
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at h
  simpa only [smul_eq_mul] using! h

theorem volume_lintegral_le_weighted_radial (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (W : M → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ y, W y ∂volumeMeasure g) ≤ riemannianChartFactor * polarAngularMass *
      ∫⁻ q : Directions, ∫⁻ r : Ioi (0 : ℝ),
        (if r.val ≤ actualCutTime g
            (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) then
          ENNReal.ofReal |((actualJacobiSolution g hRic
            (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det| *
              W (frameExponential g o e (r.val • q.val))
          else 0) ∂((volume : Measure ℝ).comap Subtype.val) ∂sphereMeasure := by
  have h := volume_lintegral_le_weighted_exponential g o hRic e he W hW
  rw [minimizing_exponential_weighted_radial g o hRic e he W hW, ← mul_assoc] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! A uniform finite radial domination constant, obtained from compactness of
the actual Jacobi family.  No curvature comparison estimate is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

variable [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  [SecondCountableTopology M]

theorem volume_lintegral_le_bounded_radial (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {C : ℝ}
    (hbound : ∀ e : FrameBundle g, ∀ r ∈ Icc (0 : ℝ) Real.pi,
      |((actualJacobiSolution g hRic e).J r).det| ≤ C)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (W : M → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ y, W y ∂volumeMeasure g) ≤
      riemannianChartFactor * polarAngularMass * ENNReal.ofReal C *
        ∫⁻ q : Directions, ∫⁻ r in Icc (0 : ℝ) Real.pi,
          W (frameExponential g o e (r • q.val)) ∂volume ∂sphereMeasure := by
  have h := volume_lintegral_le_weighted_radial g o hRic e he W hW
  let F : Directions → ℝ → ℝ≥0∞ := fun q r => W (frameExponential g o e (r • q.val))
  have hstep (q : Directions) :
      (∫⁻ r : Ioi (0 : ℝ),
        (if r.val ≤ actualCutTime g
            (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) then
          ENNReal.ofReal |((actualJacobiSolution g hRic
            (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det| * F q r.val
          else 0) ∂((volume : Measure ℝ).comap Subtype.val)) ≤
      ENNReal.ofReal C * ∫⁻ r in Icc (0 : ℝ) Real.pi, F q r := by
    have hpoint (r : Ioi (0 : ℝ)) :
        (if r.val ≤ actualCutTime g
            (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) then
          ENNReal.ofReal |((actualJacobiSolution g hRic
            (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det| * F q r.val
          else 0) ≤ ENNReal.ofReal C * (Icc (0 : ℝ) Real.pi).indicator (F q) r.val := by
      split_ifs with hr
      · have hri : r.val ∈ Icc (0 : ℝ) Real.pi := ⟨r.property.le,
          hr.trans (actualCutTime_le_pi g hRic _)⟩
        rw [Set.indicator_of_mem hri]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hbound _ _ hri)) _
      · exact zero_le
    calc
      _ ≤ ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal C *
          (Icc (0 : ℝ) Real.pi).indicator (F q) r.val
            ∂((volume : Measure ℝ).comap Subtype.val) := lintegral_mono hpoint
      _ = ENNReal.ofReal C * ∫⁻ r in Ioi (0 : ℝ),
          (Icc (0 : ℝ) Real.pi).indicator (F q) r := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_subtype_comap measurableSet_Ioi]
      _ ≤ ENNReal.ofReal C * ∫⁻ r, (Icc (0 : ℝ) Real.pi).indicator (F q) r := by
        exact mul_le_mul_right (lintegral_mono' Measure.restrict_le_self le_rfl) _
      _ = _ := by rw [lintegral_indicator measurableSet_Icc]
  calc
    _ ≤ riemannianChartFactor * polarAngularMass *
        ∫⁻ q : Directions, ENNReal.ofReal C *
          (∫⁻ r in Icc (0 : ℝ) Real.pi, F q r) ∂sphereMeasure :=
      h.trans (mul_le_mul_right (lintegral_mono hstep) _)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Global scalar pair oscillations are bounded by radial flow oscillations.
The measure comparison and all curves here are those of the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

variable [SecondCountableTopology M] [PreconnectedSpace M]

theorem scalar_pair_lintegral_le_radial (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {C : ℝ}
    (hbound : ∀ e : FrameBundle g, ∀ r ∈ Icc (0 : ℝ) Real.pi,
      |((actualJacobiSolution g hRic e).J r).det| ≤ C)
    (a : SmoothScalar (M := M)) :
    (∫⁻ e, ∫⁻ y, ENNReal.ofReal ((a.val y - a.val e.base) ^ 2)
      ∂volumeMeasure g ∂canonicalFrameMeasure g o) ≤
      riemannianChartFactor * polarAngularMass * ENNReal.ofReal C *
        ∫⁻ r in Icc (0 : ℝ) Real.pi, ∫⁻ e,
          scalarGeodesicOscillation g a r e ∂canonicalFrameMeasure g o := by
  let D := riemannianChartFactor * polarAngularMass * ENNReal.ofReal C
  have hD : D ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top) polarAngularMass_ne_top
    · exact ENNReal.ofReal_ne_top
  have hp (e : FrameBundle g) (he : e ∈ o.positive) :
      (∫⁻ y, ENNReal.ofReal ((a.val y - a.val e.base) ^ 2) ∂volumeMeasure g) ≤
      D * ∫⁻ q : Directions,
        scalarRadialOscillation g a
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) ∂sphereMeasure := by
    have hW : Measurable (fun y => ENNReal.ofReal ((a.val y - a.val e.base) ^ 2)) := by
      simpa only [Function.comp_apply, Pi.pow_apply, Pi.sub_apply] using!
        (ENNReal.continuous_ofReal.comp
          ((a.property.continuous.sub
            (continuous_const : Continuous (fun _ : M => a.val e.base))).pow 2)).measurable
    have h := volume_lintegral_le_bounded_radial g o hRic hbound e he
      (fun y => ENNReal.ofReal ((a.val y - a.val e.base) ^ 2)) hW
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply lintegral_congr
    intro q
    apply lintegral_congr
    intro r
    rw [frameExponential_direction_ray g o e he q r]
    rfl
  calc
    _ ≤ ∫⁻ e, D * (∫⁻ q : Directions,
        scalarRadialOscillation g a
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) ∂sphereMeasure)
          ∂canonicalFrameMeasure g o :=
      lintegral_mono_ae ((canonicalFrameMeasure_supported g o).mono hp)
    _ = D * ∫⁻ e, scalarRadialOscillation g a e ∂canonicalFrameMeasure g o := by
      rw [lintegral_const_mul' _ _ hD,
        canonicalFrame_lintegral_sphere_rotations g o _ (scalarRadialOscillation_measurable g a)]
    _ = _ := by rw [scalarRadialOscillation_integral]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrating the flow translation estimate over the bounded
radial interval gives a global pair-oscillation energy estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

variable [SecondCountableTopology M] [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarPairEnergy_compact
theorem scalar_pair_lintegral_energy_bound (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {C : ℝ}
    (hbound : ∀ e : FrameBundle g, ∀ r ∈ Icc (0 : ℝ) Real.pi,
      |((actualJacobiSolution g hRic e).J r).det| ≤ C)
    (a : SmoothScalar (M := M)) :
    (∫⁻ e, ∫⁻ y, ENNReal.ofReal ((a.val y - a.val e.base) ^ 2)
      ∂volumeMeasure g ∂canonicalFrameMeasure g o) ≤
      riemannianChartFactor * polarAngularMass * ENNReal.ofReal C *
        ENNReal.ofReal (Real.pi ^ 3 *
          ‖smoothScalarGradientL2 (canonicalParallelMetricData g o hRic) 0 a‖ ^ 2) :=
  (scalar_pair_lintegral_le_radial g o hRic hbound a).trans
    (mul_le_mul_right (scalar_radial_lintegral_energy_bound g o hRic a) _)

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarNormalizedPair_compact
theorem normalized_scalar_pair_energy_bound (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {C : ℝ}
    (hbound : ∀ e : FrameBundle g, ∀ r ∈ Icc (0 : ℝ) Real.pi,
      |((actualJacobiSolution g hRic e).J r).det| ≤ C)
    (a : SmoothScalar (M := M)) :
    (∫⁻ e, ∫⁻ f, ENNReal.ofReal ((a.val e.base - a.val f.base) ^ 2)
      ∂canonicalFrameMeasure g o ∂canonicalFrameMeasure g o) ≤
      scalarPairConstant g C *
        ENNReal.ofReal (‖smoothScalarGradientL2 (canonicalParallelMetricData g o hRic) 0 a‖ ^ 2) := by
  let μ := canonicalFrameMeasure g o
  have hp (e : FrameBundle g) :
      (∫⁻ f, ENNReal.ofReal ((a.val e.base - a.val f.base) ^ 2) ∂μ) =
        (volumeMeasure g univ)⁻¹ *
          ∫⁻ y, ENNReal.ofReal ((a.val y - a.val e.base) ^ 2) ∂volumeMeasure g := by
    have hm : Measurable (fun y => ENNReal.ofReal ((a.val y - a.val e.base) ^ 2)) := by
      simpa only [Function.comp_apply, Pi.pow_apply, Pi.sub_apply] using!
        (ENNReal.continuous_ofReal.comp ((a.property.continuous.sub
          (continuous_const : Continuous (fun _ : M => a.val e.base))).pow 2)).measurable
    have h := (canonicalFrameMeasure_base g o).lintegral_comp hm
    rw [normalizedVolume, lintegral_smul_measure] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply lintegral_congr
    intro f
    congr 1
    ring
  change (∫⁻ e, ∫⁻ f, ENNReal.ofReal ((a.val e.base - a.val f.base) ^ 2) ∂μ ∂μ) ≤ _
  simp_rw [hp]
  rw [lintegral_const_mul' _ _
    (ENNReal.inv_ne_top.mpr (actual_finitePositiveVolume g).positive.ne')]
  have h := mul_le_mul_right (scalar_pair_lintegral_energy_bound g o hRic hbound a)
    ((volumeMeasure g univ)⁻¹)
  refine h.trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.pi ^ 3)]
  simp only [scalarPairConstant, mul_assoc]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The geometric pair estimate gives an actual mean-zero Poincaré
inequality for smooth scalars. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarSmoothPoincare_compact
theorem smoothScalar_poincare_of_bound (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) {C : ℝ}
    (hbound : ∀ e : FrameBundle g, ∀ r ∈ Icc (0 : ℝ) Real.pi,
      |((actualJacobiSolution g hRic e).J r).det| ≤ C)
    (a : SmoothScalar (M := M))
    (hmean : (∫ e, a.val e.base ∂canonicalFrameMeasure g o) = 0) :
    ‖smoothScalarValueL2 g (canonicalFrameMeasure g o) a‖ ^ 2 ≤
      ((scalarPairConstant g C).toReal + 1) *
        ∑ i : Fin 4, ‖smoothScalarGradientL2 (canonicalParallelMetricData g o hRic) i a‖ ^ 2 := by
  let d := canonicalParallelMetricData g o hRic
  let μ := canonicalFrameMeasure g o
  let V := ‖smoothScalarValueL2 g μ a‖ ^ 2
  let E := ‖smoothScalarGradientL2 d 0 a‖ ^ 2
  have hp := normalized_scalar_pair_energy_bound g o hRic hbound a
  change (∫⁻ e, ∫⁻ f, ENNReal.ofReal
    (((smoothScalarValue g a) e - (smoothScalarValue g a) f) ^ 2) ∂μ ∂μ) ≤ _ at hp
  rw [continuous_pairwise_square_lintegral μ (smoothScalarValue g a)] at hp
  change ENNReal.ofReal (2 * ((∫ e, a.val e.base ^ 2 ∂μ) -
    (∫ e, a.val e.base ∂μ) ^ 2)) ≤ scalarPairConstant g C * ENNReal.ofReal E at hp
  rw [hmean, zero_pow (by norm_num : 2 ≠ 0), sub_zero,
    ← smoothScalar_value_norm_sq g o a] at hp
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (scalarPairConstant_ne_top g C) ENNReal.ofReal_ne_top) hp
  change (ENNReal.ofReal (2 * V)).toReal ≤
    (scalarPairConstant g C * ENNReal.ofReal E).toReal at hr
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * V), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ E)] at hr
  have hv : 0 ≤ V := sq_nonneg _
  have he : 0 ≤ E := sq_nonneg _
  have hE : E ≤ ∑ i : Fin 4, ‖smoothScalarGradientL2 d i a‖ ^ 2 := by
    change ‖smoothScalarGradientL2 d 0 a‖ ^ 2 ≤ _
    exact Finset.single_le_sum
      (fun i _ => sq_nonneg ‖smoothScalarGradientL2 d i a‖)
      (Finset.mem_univ (0 : Fin 4))
  have hK : 0 ≤ (scalarPairConstant g C).toReal := ENNReal.toReal_nonneg
  calc
    V ≤ ((scalarPairConstant g C).toReal + 1) * E := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (by positivity)

theorem exists_smoothScalar_poincare_constant (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : SmoothScalar (M := M),
      (∫ e, a.val e.base ∂canonicalFrameMeasure g o) = 0 →
      ‖smoothScalarValueL2 g (canonicalFrameMeasure g o) a‖ ^ 2 ≤
        K * ∑ i : Fin 4, ‖smoothScalarGradientL2 (canonicalParallelMetricData g o hRic) i a‖ ^ 2 := by
  obtain ⟨C, _hC, hC⟩ := exists_uniform_actualJacobi_det_bound g hRic
  exact ⟨(scalarPairConstant g C).toReal + 1, by positivity,
    fun a ha => smoothScalar_poincare_of_bound g o hRic hC a ha⟩

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.actualWeakPoisson_compact
/-- For every actual smooth source there is a mean-zero weak solution of
Δu = a - average(a), with an actual base L² representative. -/
theorem actual_scalar_weak_poisson (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a : SmoothScalar (M := M)) :
    ∃ u : scalarH1MeanZero (canonicalParallelMetricData g o hRic),
      (∃ b : Lp ℝ 2 (normalizedVolume g),
        scalarBasePullback g o b =
          scalarH1Value (canonicalParallelMetricData g o hRic) u.val) ∧
      ∀ v : scalarH1 (canonicalParallelMetricData g o hRic),
        (∑ i : Fin 4, inner ℝ
          (scalarH1Gradient (canonicalParallelMetricData g o hRic) i u.val)
          (scalarH1Gradient (canonicalParallelMetricData g o hRic) i v)) =
          -(inner ℝ
            (smoothScalarValueL2 g (canonicalFrameMeasure g o)
              (smoothScalarSubtractMean (μ := canonicalFrameMeasure g o) a))
            (scalarH1Value (canonicalParallelMetricData g o hRic) v)) := by
  let d := canonicalParallelMetricData g o hRic
  let μ := canonicalFrameMeasure g o
  obtain ⟨K, hK, hP⟩ := exists_smoothScalar_poincare_constant g o hRic
  let f := -(smoothScalarValueL2 g μ (smoothScalarSubtractMean (μ := μ) a))
  have hf : inner ℝ f (scalarL2One g μ) = 0 := by
    dsimp only [f]
    rw [inner_neg_left, smoothScalar_centered_orthogonal_one d a, neg_zero]
  refine ⟨scalarMeanZeroWeakPoisson d hK hP f,
    scalarH1_base_representative g o d _, ?_⟩
  intro v
  simpa only [f, inner_neg_left] using
    scalarMeanZeroWeakPoisson_all_tests d hK hP f hf v

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Global smooth representatives of the actual intrinsic weak Poisson
solutions, obtained from the proved local coordinate regularity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.poissonRegularity_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.poissonRegularity_probability
theorem actual_petersen_poisson [SecondCountableTopology M] [PreconnectedSpace M]
    (g : SmoothMetric M) (o : FrameOrientation g) (hRic : RicciThree g) :
    PetersenPoissonInput g (canonicalFrameMeasure g o) := by
  intro a ha
  let a₀ : SmoothScalar (M := M) := ⟨a, ha⟩
  let d := canonicalParallelMetricData g o hRic
  obtain ⟨u, _, hw⟩ := actual_scalar_weak_poisson g o hRic a₀
  obtain ⟨F, hF⟩ := scalar_weak_poisson_smooth_representative g o d
    (smoothScalarSubtractMean (μ := canonicalFrameMeasure g o) a₀) u.val hw
  refine ⟨F.val, F.property, ?_⟩
  exact scalar_poisson_pointwise_of_smooth_representative g o hRic a₀ F u.val hF hw

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar spectral multipliers and heat evolution for the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarBaseSpectralMultiplier_norm
    (a : ScalarBaseEigenIndex g o d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f : Lp ℝ 2 (normalizedVolume g)) :
    ‖scalarBaseSpectralMultiplier g o d a C hC ha f‖ ≤ C * ‖f‖ := by
  rw [← (scalarBaseSpectralEquiv g o d).norm_map (scalarBaseSpectralMultiplier g o d a C hC ha f),
    ← (scalarBaseSpectralEquiv g o d).norm_map f]
  calc
    _ ≤ ‖C • scalarBaseSpectralEquiv g o d f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro μ
      rw [scalarBaseSpectralMultiplier_coordinate, norm_smul, Real.norm_eq_abs]
      change |a μ| * ‖(scalarBaseSpectralEquiv g o d f) μ‖ ≤
        ‖C • (scalarBaseSpectralEquiv g o d f) μ‖
      change |a μ| * |(scalarBaseSpectralEquiv g o d f) μ| ≤
        |C * (scalarBaseSpectralEquiv g o d f) μ|
      rw [abs_mul, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha μ) (abs_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]

theorem scalarBaseSpectralMultiplier_inner
    (a : ScalarBaseEigenIndex g o d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f h : Lp ℝ 2 (normalizedVolume g)) :
    inner ℝ (scalarBaseSpectralMultiplier g o d a C hC ha f) h =
      ∑' μ, a μ * inner ℝ ((scalarBaseSpectralEquiv g o d f) μ)
        ((scalarBaseSpectralEquiv g o d h) μ) := by
  rw [← (scalarBaseSpectralEquiv g o d).inner_map_map, lp.inner_eq_tsum]
  apply tsum_congr
  intro μ
  rw [scalarBaseSpectralMultiplier_coordinate, real_inner_smul_left]

theorem scalarBaseSpectralMultiplier_selfAdjoint
    (a : ScalarBaseEigenIndex g o d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f h : Lp ℝ 2 (normalizedVolume g)) :
    inner ℝ (scalarBaseSpectralMultiplier g o d a C hC ha f) h =
      inner ℝ f (scalarBaseSpectralMultiplier g o d a C hC ha h) := by
  calc
    _ = ∑' μ, a μ * inner ℝ ((scalarBaseSpectralEquiv g o d f) μ)
        ((scalarBaseSpectralEquiv g o d h) μ) := scalarBaseSpectralMultiplier_inner g o d a C hC ha f h
    _ = ∑' μ, a μ * inner ℝ ((scalarBaseSpectralEquiv g o d h) μ)
        ((scalarBaseSpectralEquiv g o d f) μ) := by
      apply tsum_congr
      intro μ
      rw [real_inner_comm]
    _ = inner ℝ (scalarBaseSpectralMultiplier g o d a C hC ha h) f :=
      (scalarBaseSpectralMultiplier_inner g o d a C hC ha h f).symm
    _ = _ := real_inner_comm _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar spectral multipliers and heat evolution for the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarBaseHeat_contraction (t : ℝ≥0) (f : Lp ℝ 2 (normalizedVolume g)) :
    ‖scalarBaseHeat g o d t f‖ ≤ ‖f‖ := by
  simpa only [scalarBaseHeat, one_mul] using scalarBaseSpectralMultiplier_norm g o d
    (scalarBaseHeatWeight g o d t) 1 zero_le_one (scalarBaseHeatWeight_bound g o d t) f

theorem scalarBaseHeat_selfAdjoint (t : ℝ≥0) (f h : Lp ℝ 2 (normalizedVolume g)) :
    inner ℝ (scalarBaseHeat g o d t f) h = inner ℝ f (scalarBaseHeat g o d t h) :=
  scalarBaseSpectralMultiplier_selfAdjoint g o d _ _ _ _ f h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar spectral multipliers and heat evolution for the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarBaseSpectralMultiplier_sub_norm_sq
    (a b : ScalarBaseEigenIndex g o d → ℝ)
    (ha : ∀ μ, |a μ| ≤ 1) (hb : ∀ μ, |b μ| ≤ 1) (f : Lp ℝ 2 (normalizedVolume g)) :
    ‖scalarBaseSpectralMultiplier g o d a 1 zero_le_one ha f -
      scalarBaseSpectralMultiplier g o d b 1 zero_le_one hb f‖ ^ 2 =
      ∑' μ, (a μ - b μ) ^ 2 * ‖(scalarBaseSpectralEquiv g o d f) μ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← (scalarBaseSpectralEquiv g o d).inner_map_map,
    map_sub, lp.inner_eq_tsum]
  apply tsum_congr
  intro μ
  change inner ℝ
    ((scalarBaseSpectralEquiv g o d (scalarBaseSpectralMultiplier g o d a 1 zero_le_one ha f)) μ -
      (scalarBaseSpectralEquiv g o d (scalarBaseSpectralMultiplier g o d b 1 zero_le_one hb f)) μ)
    ((scalarBaseSpectralEquiv g o d (scalarBaseSpectralMultiplier g o d a 1 zero_le_one ha f)) μ -
      (scalarBaseSpectralEquiv g o d (scalarBaseSpectralMultiplier g o d b 1 zero_le_one hb f)) μ) = _
  rw [scalarBaseSpectralMultiplier_coordinate, scalarBaseSpectralMultiplier_coordinate,
    ← sub_smul, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

theorem scalarBaseSpectralMultiplier_tendsto {α : Type*} {l : Filter α}
    (a : α → ScalarBaseEigenIndex g o d → ℝ)
    (b : ScalarBaseEigenIndex g o d → ℝ)
    (ha : ∀ x μ, |a x μ| ≤ 1) (hb : ∀ μ, |b μ| ≤ 1)
    (hab : ∀ μ, Tendsto (fun x => a x μ) l (𝓝 (b μ))) (f : Lp ℝ 2 (normalizedVolume g)) :
    Tendsto (fun x => scalarBaseSpectralMultiplier g o d (a x) 1 zero_le_one (ha x) f) l
      (𝓝 (scalarBaseSpectralMultiplier g o d b 1 zero_le_one hb f)) := by
  have hsum : Summable (fun μ : ScalarBaseEigenIndex g o d =>
      4 * ‖(scalarBaseSpectralEquiv g o d f) μ‖ ^ 2) := by
    have hs := lp.summable_inner (𝕜 := ℝ)
      (scalarBaseSpectralEquiv g o d f) (scalarBaseSpectralEquiv g o d f)
    simp only [real_inner_self_eq_norm_sq] at hs
    exact hs.mul_left 4
  have hbound (x : α) (μ : ScalarBaseEigenIndex g o d) :
      ‖(a x μ - b μ) ^ 2 * ‖(scalarBaseSpectralEquiv g o d f) μ‖ ^ 2‖ ≤
        4 * ‖(scalarBaseSpectralEquiv g o d f) μ‖ ^ 2 := by
    have hdiff : |a x μ - b μ| ≤ 2 :=
      (abs_sub (a x μ) (b μ)).trans (by linarith only [ha x μ, hb μ])
    have hsq : (a x μ - b μ) ^ 2 ≤ 4 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hdiff)
        (add_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (abs_nonneg (a x μ - b μ)))
      nlinarith only [hprod, sq_abs (a x μ - b μ)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hpoint (μ : ScalarBaseEigenIndex g o d) :
      Tendsto (fun x => (a x μ - b μ) ^ 2 * ‖(scalarBaseSpectralEquiv g o d f) μ‖ ^ 2)
        l (𝓝 (0 : ℝ)) := by
    convert (((hab μ).sub_const (b μ)).pow 2).mul_const
      (‖(scalarBaseSpectralEquiv g o d f) μ‖ ^ 2) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have ht := tendsto_tsum_of_dominated_convergence hsum hpoint
    (Eventually.of_forall hbound)
  simp only [tsum_zero] at ht
  have hn : Tendsto (fun x => ‖scalarBaseSpectralMultiplier g o d (a x) 1 zero_le_one (ha x) f -
      scalarBaseSpectralMultiplier g o d b 1 zero_le_one hb f‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    simpa only [scalarBaseSpectralMultiplier_sub_norm_sq] using ht
  have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  convert hs using 1
  · funext x
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · exact congrArg nhds Real.sqrt_zero.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar spectral multipliers and heat evolution for the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarBaseHeat_continuous (f : Lp ℝ 2 (normalizedVolume g)) :
    Continuous (fun t : ℝ≥0 => scalarBaseHeat g o d t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact scalarBaseSpectralMultiplier_tendsto g o d (scalarBaseHeatWeight g o d)
    (scalarBaseHeatWeight g o d t) (scalarBaseHeatWeight_bound g o d)
    (scalarBaseHeatWeight_bound g o d t)
    (fun μ => (scalarBaseHeatWeight_continuous g o d μ).continuousAt) f

theorem scalarBaseHeat_joint_continuous :
    Continuous (fun tf : ℝ≥0 × Lp ℝ 2 (normalizedVolume g) => scalarBaseHeat g o d tf.1 tf.2) := by
  apply continuous_iff_continuousAt.mpr
  intro tf
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have htime := Metric.continuousAt_iff.mp
    ((scalarBaseHeat_continuous g o d tf.2).continuousAt (x := tf.1))
    (ε / 2) (half_pos hε)
  obtain ⟨δ, hδ, htime⟩ := htime
  refine ⟨min δ (ε / 2), lt_min hδ (half_pos hε), ?_⟩
  intro sf hsf
  have hst : dist sf.1 tf.1 < δ := by
    calc
      dist sf.1 tf.1 ≤ dist sf tf := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ < δ := lt_of_lt_of_le hsf (min_le_left _ _)
  have hsu : dist sf.2 tf.2 < ε / 2 := by
    calc
      dist sf.2 tf.2 ≤ dist sf tf := by rw [Prod.dist_eq]; exact le_max_right _ _
      _ < ε / 2 := lt_of_lt_of_le hsf (min_le_right _ _)
  calc
    dist (scalarBaseHeat g o d sf.1 sf.2) (scalarBaseHeat g o d tf.1 tf.2) ≤
        dist (scalarBaseHeat g o d sf.1 sf.2) (scalarBaseHeat g o d sf.1 tf.2) +
        dist (scalarBaseHeat g o d sf.1 tf.2) (scalarBaseHeat g o d tf.1 tf.2) := dist_triangle _ _ _
    _ ≤ dist sf.2 tf.2 + dist (scalarBaseHeat g o d sf.1 tf.2) (scalarBaseHeat g o d tf.1 tf.2) := by
      apply add_le_add_left
      rw [dist_eq_norm, ← map_sub, dist_eq_norm]
      exact scalarBaseHeat_contraction g o d sf.1 (sf.2 - tf.2)
    _ < ε / 2 + ε / 2 := add_lt_add hsu (htime hst)
    _ = ε := add_halves ε

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth scalar eigenfunctions chosen from the actual orthonormal basis,
with their exact heat evolution and geometric Laplace equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarBaseHeat_eigenvector (t : ℝ≥0) (i : ScalarBaseEigenIndex g o d) :
    scalarBaseHeat g o d t (scalarBaseEigenvector g o d i) =
      scalarBaseHeatWeight g o d t i • scalarBaseEigenvector g o d i := by
  classical
  apply (scalarBaseSpectralEquiv g o d).injective
  apply lp.ext
  funext j
  rw [scalarBaseHeat_coordinate, map_smul]
  have hbi : scalarBaseEigenbasis g o d i = scalarBaseEigenvector g o d i := by
    simp only [scalarBaseEigenbasis, HilbertBasis.coe_mk]
  have hb : scalarBaseSpectralEquiv g o d (scalarBaseEigenvector g o d i) =
      lp.single 2 i (1 : ℝ) := by
    change (scalarBaseEigenbasis g o d).repr _ = _
    simpa only [hbi] using (scalarBaseEigenbasis g o d).repr_self i
  rw [hb]
  by_cases h : j = i
  · subst j
    simp
  · simp [lp.single_apply, h]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The concrete shifted scalar resolvent supplies the local elliptic chain.
No regularity of its L2 input is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.resolventChain_frameCompact
theorem scalarBaseResolvent_local_orders (c : M) (z₀ : ChartTarget c) :
    ∃ r : ℝ, 0 < r ∧
      (∀ y ∈ closedBall (0 : FourSpace) 1,
        scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target) ∧
      ∀ f : Lp ℝ 2 (normalizedVolume g), ∃ w : ℕ → Lp ℝ 2 (volume : Measure FourSpace),
        (∀ k, (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
          ((scalarBaseResolvent g o d ^ (k + 1)) f)
            ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
              volume.restrict (ball (0 : FourSpace) 1)] w k) ∧
        ∀ (n : ℕ) (φ : 𝓢(FourSpace, ℂ)), HasCompactSupport (φ : FourSpace → ℂ) →
          tsupport (φ : FourSpace → ℂ) ⊆ ball 0 (1 / 2) →
          MemSobolev ((2 * n + 1 : ℕ) : ℝ) 2
            (smulLeftCLM ℂ φ (scalarComplexL2 (w n) : 𝓢'(FourSpace, ℂ))) := by
  obtain ⟨r, hr, ht, hchain⟩ := scalar_resolvent_chain_local g o d c z₀
  refine ⟨r, hr, ht, ?_⟩
  intro f
  obtain ⟨w, hw, hreg⟩ := hchain (fun n => scalarBaseResolventJet g o d n f)
    (fun k v => scalarBaseResolventJet_weak g o d k f v)
  refine ⟨w, ?_, hreg⟩
  intro k
  simpa only [scalarBaseResolventJet_value] using hw k

end
end PositiveEinsteinFour.Geometry
end


section

/-! All local integer Sobolev orders of the actual positive-time scalar heat
output, on a single chart neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarBaseHeat_local_all_orders (t : ℝ≥0) (ht : 0 < t)
    (f : Lp ℝ 2 (normalizedVolume g)) (c : M) (z₀ : ChartTarget c) :
    ∃ r : ℝ, 0 < r ∧
      (∀ y ∈ closedBall (0 : FourSpace) 1,
        scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target) ∧
      ∃ w : Lp ℝ 2 (volume : Measure FourSpace),
        (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
          scalarBaseHeat g o d t f
            ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
              volume.restrict (ball (0 : FourSpace) 1)] w ∧
        ∀ (n : ℕ) (φ : 𝓢(FourSpace, ℂ)), HasCompactSupport (φ : FourSpace → ℂ) →
          tsupport (φ : FourSpace → ℂ) ⊆ ball 0 (1 / 2) →
          MemSobolev (n : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2 w : 𝓢'(FourSpace, ℂ))) := by
  obtain ⟨r, hr, htarget, hchain⟩ := scalarBaseResolvent_local_orders g o d c z₀
  let F := fun n => scalarBaseHeatPowerSource g o d t ht (n + 1) f
  obtain ⟨w₀, hw₀, _⟩ := hchain (F 0)
  have he₀ : (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
      scalarBaseHeat g o d t f
        ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
        volume.restrict (ball (0 : FourSpace) 1)] w₀ 0 := by
    have he := scalarBaseHeatPowerSource_resolvent g o d t ht 1 f
    simpa only [Nat.zero_add, F, he] using hw₀ 0
  refine ⟨r, hr, htarget, w₀ 0, he₀, ?_⟩
  intro n φ hc hs
  obtain ⟨w, hw, hreg⟩ := hchain (F n)
  have he : (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
      scalarBaseHeat g o d t f
        ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
        volume.restrict (ball (0 : FourSpace) 1)] w n := by
    simpa only [F, scalarBaseHeatPowerSource_resolvent] using hw n
  have heq := scalar_localized_distribution_eq (ball (0 : FourSpace) 1)
    isOpen_ball.measurableSet (w₀ 0) (w n) (he₀.symm.trans he) φ
    (hs.trans (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)))
  rw [heq]
  exact (hreg n φ hc hs).mono (by exact_mod_cast (show n ≤ 2 * n + 1 by omega))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual L2 values and Laplacians of C4 cutoffs. Their spectral pairing
is obtained from the finite-regularity geometric Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarFinite_probability
theorem scalarFiniteLaplacian_eigen (f : M → ℝ) (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f)
    (i : ScalarBaseEigenIndex g o d) :
    inner ℝ (scalarFiniteLaplacianL2 g f hf) (scalarBaseEigenvector g o d i) =
      -scalarBaseHeatRate g o d i *
        inner ℝ (scalarFiniteValueL2 g f hf) (scalarBaseEigenvector g o d i) := by
  let F := scalarBaseEigenfunction g o d i
  have hF : scalarBaseEigenvector g o d i =ᵐ[normalizedVolume g] F.val := by
    rw [scalarBaseEigenfunction_L2]
    exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g) _
  have h1 : inner ℝ (scalarFiniteLaplacianL2 g f hf) (scalarBaseEigenvector g o d i) =
      ∫ x, scalarLaplacianBase g f x * F.val x ∂normalizedVolume g := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [scalarFiniteLaplacianL2_coe g f hf, hF] with x hx hFx
    simp only [RCLike.inner_apply', conj_trivial, hx, hFx]
  have h2 : inner ℝ (scalarFiniteValueL2 g f hf) (scalarBaseEigenvector g o d i) =
      ∫ x, f x * F.val x ∂normalizedVolume g := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [scalarFiniteValueL2_coe g f hf, hF] with x hx hFx
    simp only [RCLike.inner_apply', conj_trivial, hx, hFx]
  have hLF (x : M) : scalarLaplacianBase g F.val x =
      -scalarBaseHeatRate g o d i * F.val x := by
    exact congrArg (fun v : SmoothScalar (M := M) => v.val x)
      (scalarBaseEigenfunction_laplacian g o d i)
  rw [h1, h2, scalar_finite_laplacian_base_symmetric o d hf
    (F.property.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  simp_rw [hLF, mul_left_comm (f _) (-scalarBaseHeatRate g o d i)]
  exact integral_const_mul _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Bochner heat convolution, its eigenmode pairing and its
quadratic norm bound for a linearly vanishing residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarHeatConvolution_integrable
    (R : ℝ → Lp ℝ 2 (normalizedVolume g)) (t : ℝ) (ht : 0 ≤ t) (hR : ContinuousOn R (Icc 0 t)) :
    IntervalIntegrable (fun s => scalarBaseHeat g o d (t - s).toNNReal (R s)) volume 0 t := by
  have htime : Continuous (fun s : ℝ => (t - s).toNNReal) :=
    continuous_real_toNNReal.comp (continuous_const.sub continuous_id)
  exact ((scalarBaseHeat_joint_continuous g o d).comp_continuousOn
    (htime.continuousOn.prodMk hR)).intervalIntegrable_of_Icc ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! Undo the positive chart density and the invertible affine rescaling
in the local smooth representative of the actual scalar heat output. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

local instance heatUnweighting_frameCompact_ra4f0fb_1 (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g
theorem scalarBaseHeat_local_chart_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (t : ℝ≥0) (ht : 0 < t) (input : Lp ℝ 2 (normalizedVolume g)) (c : M) (z₀ : ChartTarget c) :
    ∃ U : Set FourSpace, IsOpen U ∧ z₀.val ∈ U ∧ U ⊆ (chartAt FourSpace c).target ∧
      ∃ F : FourSpace → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
        (fun z => scalarBaseHeat g o d t input ((chartAt FourSpace c).symm z)) =ᵐ[
          volume.restrict U] F := by
  obtain ⟨r, hr, ht, w, hw, hreg⟩ := scalarBaseHeat_local_all_orders g o d t ht input c z₀
  obtain ⟨F, hF, hFw⟩ := scalar_half_smooth_real_representative w
    hreg
  have hwsmall : (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
      scalarBaseHeat g o d t input ((chartAt FourSpace c).symm
        (scalarRescaledPoint g c z₀ r y))) =ᵐ[
      volume.restrict (ball (0 : FourSpace) (1 / 8))] w :=
    ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by norm_num : (1 / 8 : ℝ) ≤ 1)) hw
  have heq := hwsmall.trans hFw
  let A := scalarRescalingLinearEquiv g c z₀ r hr.ne'
  let U : Set FourSpace := {z | A.symm (z - z₀) ∈ ball (0 : FourSpace) (1 / 8)}
  have hU : IsOpen U := isOpen_ball.preimage (by fun_prop)
  have hz₀ : z₀.val ∈ U := by
    simp only [U, mem_ofPred_eq, sub_self, map_zero, mem_ball, dist_self]
    norm_num
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ r (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ r hr.ne']
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hUt : U ⊆ (chartAt FourSpace c).target := by
    intro z hz
    have hy : A.symm (z - z₀) ∈ closedBall (0 : FourSpace) 1 :=
      ball_subset_closedBall (ball_subset_ball (by norm_num : (1 / 8 : ℝ) ≤ 1) hz)
    have h := ht _ hy
    rwa [hinv] at h
  let H : FourSpace → ℝ := fun z => F (A.symm (z - z₀)) / chartVolumeDensity g c z
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H U := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    exact ((hF.contDiffAt).comp z
      (A.symm.contDiff.contDiffAt.comp z (contDiffAt_id.sub contDiffAt_const))).div
      (chartVolumeDensity_contDiffAt g c z (hUt hz))
      (chartVolumeDensity_pos g c z (hUt hz)).ne'
  refine ⟨U, hU, hz₀, hUt, H, hH, ?_⟩
  have hmp : Measure.QuasiMeasurePreserving
      (fun z : FourSpace => A.symm (z - z₀)) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    have hfun : (fun z : FourSpace => A.symm (z - z₀)) =
        (fun z => A.symm z + (-A.symm z₀)) := by
      funext z
      rw [map_sub, sub_eq_add_neg]
    rw [hfun, scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  have hglob := hmp.ae ((ae_restrict_iff' isOpen_ball.measurableSet).mp heq)
  apply (ae_restrict_iff' hU.measurableSet).mpr
  filter_upwards [hglob] with z hz
  intro hzU
  have he := hz hzU
  rw [hinv] at he
  apply (eq_div_iff (chartVolumeDensity_pos g c z (hUt hzU)).ne').mpr
  simpa only [mul_comm] using he

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

local instance heatSmooth_frameCompact_ra4f0fb_1 (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.heatSmooth_probability
theorem scalarBaseHeat_smooth_representative (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (t : ℝ≥0) (ht : 0 < t) (input : Lp ℝ 2 (normalizedVolume g)) :
    ∃ F : SmoothScalar (M := M), scalarBaseHeat g o d t input = smoothScalarBaseL2 g F := by
  let b := scalarBaseHeat g o d t input
  have hlocal (x : M) : ∃ U : Set M, ∃ F : M → ℝ,
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn I4 𝓘(ℝ, ℝ) ∞ F U ∧
        (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict U] F := by
    let z₀ : ChartTarget x := ⟨chartAt FourSpace x x,
      (chartAt FourSpace x).map_source (mem_chart_source FourSpace x)⟩
    obtain ⟨U, hU, hxU, _, F, hF, he⟩ := scalarBaseHeat_local_chart_smooth g o d t ht input x z₀
    let W := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' U
    refine ⟨W, fun y => F (chartAt FourSpace x y),
      (chartAt FourSpace x).isOpen_inter_preimage hU, ⟨mem_chart_source FourSpace x, hxU⟩,
      ?_, scalar_chart_representative_ae g x U hU b F he⟩
    intro y hy
    have hFC : ContDiffAt ℝ (⊤ : ℕ∞) F (chartAt FourSpace x y) :=
      (hF _ hy.2).contDiffAt (hU.mem_nhds hy.2)
    exact (hFC.contMDiffAt.comp y
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hy.1)).contMDiffWithinAt
  obtain ⟨F, hF⟩ := scalar_smooth_representative_of_local g b hlocal
  have hb : smoothScalarBaseL2 g F = b := by
    apply Lp.ext
    have hcoe := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
      (⟨F.val, F.property.continuous⟩ : C(M, ℝ))
    filter_upwards [hcoe, hF] with x hx hFx
    exact hx.trans hFx
  exact ⟨F, hb.symm⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine scalar heat operator lifts boundedly to continuous functions
on the compact manifold. Closedness of its graph follows from the L2 identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o)) (t : ℝ≥0) (ht : 0 < t)

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarHeatContinuous_probability
def scalarHeatContinuousValue (f : Lp ℝ 2 (normalizedVolume g)) : C(M, ℝ) :=
  ⟨(scalarBaseHeat_smooth_representative g o d t ht f).choose.val,
    (scalarBaseHeat_smooth_representative g o d t ht f).choose.property.continuous⟩

theorem scalarHeatContinuousValue_L2 (f : Lp ℝ 2 (normalizedVolume g)) :
    ContinuousMap.toLp 2 (normalizedVolume g) ℝ (scalarHeatContinuousValue g o d t ht f) =
      scalarBaseHeat g o d t f :=
  (scalarBaseHeat_smooth_representative g o d t ht f).choose_spec.symm

def scalarHeatContinuousLinear : Lp ℝ 2 (normalizedVolume g) →ₗ[ℝ] C(M, ℝ) where
  toFun := scalarHeatContinuousValue g o d t ht
  map_add' f h := by
    let := normalizedVolume_isOpenPosMeasure g
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) (normalizedVolume g)
    rw [map_add, scalarHeatContinuousValue_L2, scalarHeatContinuousValue_L2,
      scalarHeatContinuousValue_L2, map_add]
  map_smul' c f := by
    let := normalizedVolume_isOpenPosMeasure g
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) (normalizedVolume g)
    rw [map_smul, scalarHeatContinuousValue_L2, scalarHeatContinuousValue_L2, map_smul]
    rfl

theorem scalarHeatContinuous_graph_closed :
    IsClosed ((scalarHeatContinuousLinear g o d t ht).graph :
      Set (Lp ℝ 2 (normalizedVolume g) × C(M, ℝ))) := by
  have heq : ((scalarHeatContinuousLinear g o d t ht).graph :
      Set (Lp ℝ 2 (normalizedVolume g) × C(M, ℝ))) =
      {p | ContinuousMap.toLp 2 (normalizedVolume g) ℝ p.2 = scalarBaseHeat g o d t p.1} := by
    ext p
    change p.2 = scalarHeatContinuousValue g o d t ht p.1 ↔
      ContinuousMap.toLp 2 (normalizedVolume g) ℝ p.2 = scalarBaseHeat g o d t p.1
    constructor
    · intro hp
      rw [hp]
      exact scalarHeatContinuousValue_L2 g o d t ht p.1
    · intro h
      let := normalizedVolume_isOpenPosMeasure g
      apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) (normalizedVolume g)
      exact h.trans (scalarHeatContinuousValue_L2 g o d t ht p.1).symm
  rw [heq]
  exact isClosed_eq ((ContinuousMap.toLp 2 (normalizedVolume g) ℝ).continuous.comp continuous_snd)
    ((scalarBaseHeat g o d t).continuous.comp continuous_fst)

def scalarHeatToContinuous : Lp ℝ 2 (normalizedVolume g) →L[ℝ] C(M, ℝ) :=
  ContinuousLinearMap.ofIsClosedGraph (scalarHeatContinuous_graph_closed g o d t ht)

theorem scalarHeatToContinuous_L2 (f : Lp ℝ 2 (normalizedVolume g)) :
    ContinuousMap.toLp 2 (normalizedVolume g) ℝ (scalarHeatToContinuous g o d t ht f) =
      scalarBaseHeat g o d t f := scalarHeatContinuousValue_L2 g o d t ht f

theorem scalarHeatToContinuous_bound (f : Lp ℝ 2 (normalizedVolume g)) (x : M) :
    |scalarHeatToContinuous g o d t ht f x| ≤ ‖scalarHeatToContinuous g o d t ht‖ * ‖f‖ := by
  have hc : |scalarHeatToContinuous g o d t ht f x| ≤
      ‖scalarHeatToContinuous g o d t ht f‖ :=
    ContinuousMap.norm_coe_le_norm (scalarHeatToContinuous g o d t ht f) x
  exact hc.trans ((scalarHeatToContinuous g o d t ht).le_opNorm f)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Riesz representatives of scalar heat evaluation. The columns are
actual L2 functions, with a uniform bound over the compact manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o)) (t : ℝ≥0) (ht : 0 < t)

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarColumn_probability
def scalarHeatEvaluation (x : M) : Lp ℝ 2 (normalizedVolume g) →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ x).comp (scalarHeatToContinuous g o d t ht)

def scalarHeatColumn (x : M) : Lp ℝ 2 (normalizedVolume g) :=
  (InnerProductSpace.toDual ℝ (Lp ℝ 2 (normalizedVolume g))).symm
    (scalarHeatEvaluation g o d t ht x)

theorem scalarHeatColumn_pairing (x : M) (f : Lp ℝ 2 (normalizedVolume g)) :
    inner ℝ (scalarHeatColumn g o d t ht x) f = scalarHeatToContinuous g o d t ht f x :=
  InnerProductSpace.toDual_symm_apply

theorem scalarHeatColumn_norm (x : M) :
    ‖scalarHeatColumn g o d t ht x‖ ≤ ‖scalarHeatToContinuous g o d t ht‖ := by
  rw [scalarHeatColumn, LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound (scalarHeatEvaluation g o d t ht x)
    (norm_nonneg (scalarHeatToContinuous g o d t ht))
  intro f
  exact scalarHeatToContinuous_bound g o d t ht f x

theorem scalarHeatContinuous_eigen (i : ScalarBaseEigenIndex g o d) :
    scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i) =
      scalarBaseHeatWeight g o d t i •
        (⟨(scalarBaseEigenfunction g o d i).val,
          (scalarBaseEigenfunction g o d i).property.continuous⟩ : C(M, ℝ)) := by
  let := normalizedVolume_isOpenPosMeasure g
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) (normalizedVolume g)
  rw [scalarHeatToContinuous_L2, map_smul, scalarBaseHeat_eigenvector]
  congr 1
  exact scalarBaseEigenfunction_L2 g o d i

theorem scalarHeatColumn_eigen (x : M) (i : ScalarBaseEigenIndex g o d) :
    inner ℝ (scalarHeatColumn g o d t ht x) (scalarBaseEigenvector g o d i) =
      scalarBaseHeatWeight g o d t i * (scalarBaseEigenfunction g o d i).val x := by
  rw [scalarHeatColumn_pairing, scalarHeatContinuous_eigen]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Trace summability follows from the actual bounded scalar heat evaluation
map and integration of Bessel's inequality over normalized volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarTrace_probability
theorem scalarHeat_eigen_integral (t : ℝ≥0) (ht : 0 < t) (i : ScalarBaseEigenIndex g o d) :
    (∫ x, (scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i) x) ^ 2
      ∂normalizedVolume g) = scalarBaseHeatWeight g o d t i ^ 2 := by
  have h := ContinuousMap.inner_toLp (normalizedVolume g)
    (scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i))
    (scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i))
  rw [scalarHeatToContinuous_L2] at h
  calc
    _ = inner ℝ (scalarBaseHeat g o d t (scalarBaseEigenvector g o d i))
        (scalarBaseHeat g o d t (scalarBaseEigenvector g o d i)) := by
      simpa only [conj_trivial, pow_two] using h.symm
    _ = _ := by
      rw [real_inner_self_eq_norm_sq, scalarBaseHeat_eigenvector, norm_smul,
        Real.norm_eq_abs, (scalarBaseEigenvector_orthonormal g o d).1 i, mul_one, sq_abs]

theorem scalarHeat_diagonal_bound (t : ℝ≥0) (ht : 0 < t)
    (s : Finset (ScalarBaseEigenIndex g o d)) (x : M) :
    (∑ i ∈ s, (scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i) x) ^ 2) ≤
      ‖scalarHeatToContinuous g o d t ht‖ ^ 2 := by
  have hb := (scalarBaseEigenvector_orthonormal g o d).sum_inner_products_le
    (scalarHeatColumn g o d t ht x) (s := s)
  have he (i : ScalarBaseEigenIndex g o d) :
      inner ℝ (scalarBaseEigenvector g o d i) (scalarHeatColumn g o d t ht x) =
        scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i) x :=
    (real_inner_comm _ _).trans (scalarHeatColumn_pairing g o d t ht x _)
  simp_rw [he, Real.norm_eq_abs, sq_abs] at hb
  have hn := scalarHeatColumn_norm g o d t ht x
  have hsq : ‖scalarHeatColumn g o d t ht x‖ ^ 2 ≤
      ‖scalarHeatToContinuous g o d t ht‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg (scalarHeatColumn g o d t ht x))
      (norm_nonneg (scalarHeatToContinuous g o d t ht))).mpr hn
  exact hb.trans hsq

theorem scalarHeat_weight_square_summable (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i : ScalarBaseEigenIndex g o d => scalarBaseHeatWeight g o d t i ^ 2) := by
  apply summable_of_sum_le (fun _ => sq_nonneg _) (c := ‖scalarHeatToContinuous g o d t ht‖ ^ 2)
  intro s
  have hi (i : ScalarBaseEigenIndex g o d) : Integrable
      (fun x => (scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i) x) ^ 2)
      (normalizedVolume g) :=
    ((scalarHeatToContinuous g o d t ht _).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ x, ∑ i ∈ s, (scalarHeatToContinuous g o d t ht (scalarBaseEigenvector g o d i) x) ^ 2
        ∂normalizedVolume g := by
      rw [integral_finsetSum s (fun i _ => hi i)]
      exact Finset.sum_congr rfl (fun i _ => (scalarHeat_eigen_integral g o d t ht i).symm)
    _ ≤ ∫ _x, ‖scalarHeatToContinuous g o d t ht‖ ^ 2 ∂normalizedVolume g :=
      integral_mono (integrable_finsetSum s (fun i _ => hi i)) (integrable_const _)
        (scalarHeat_diagonal_bound g o d t ht s)
    _ = _ := by simp

theorem scalarHeat_weight_summable (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i : ScalarBaseEigenIndex g o d => scalarBaseHeatWeight g o d t i) := by
  have hs := scalarHeat_weight_square_summable g o d (t / 2) (half_pos ht)
  apply hs.congr
  intro i
  simp only [scalarBaseHeatWeight, pow_two, ← Real.exp_add, NNReal.coe_div, NNReal.coe_ofNat]
  congr 1
  ring

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Scalar spectral multipliers and heat evolution for the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

def scalarBaseHeatLiftSource (t : ℝ≥0) (ht : 0 < t) :
    Lp ℝ 2 (normalizedVolume g) →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  scalarBaseHeatPowerSource g o d t ht 1

end
end PositiveEinsteinFour.Geometry
end


section

/-! Weak Hodge Poisson solvability for actual L2 two-form sources
orthogonal to the harmonic kernel, with the normalized solution unique. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_weakHodgePoisson (hRic : RicciThree g) (f : TwoFormL2 o)
    (hf : ∀ v ∈ twoFormWeitzenbockKernel (o := o), inner ℝ f (twoFormH1ToL2 v) = 0) :
    ∃ u : TwoFormH1 o,
      (∀ v ∈ twoFormWeitzenbockKernel (o := o), inner ℝ u v = 0) ∧
      ∀ v : TwoFormH1 o, twoFormHodgeForm u v = inner ℝ f (twoFormH1ToL2 v) := by
  obtain ⟨u, hu⟩ := twoFormRegularizedHodge_surjective (o := o) hRic (twoFormRoughSolution f)
  have he (v : TwoFormH1 o) : twoFormHodgeForm u v +
      inner ℝ (twoFormHarmonicProjection u) v = inner ℝ f (twoFormH1ToL2 v) := by
    have h := congrArg (fun w : TwoFormH1 o => inner ℝ w v) hu
    change inner ℝ (twoFormHodgeOperator u + twoFormHarmonicProjection u) v =
      inner ℝ (twoFormRoughSolution f) v at h
    rw [inner_add_left, twoFormHodgeOperator_inner, twoFormRoughSolution_weak] at h
    exact h
  have hp : twoFormHarmonicProjection u ∈ twoFormWeitzenbockKernel (o := o) :=
    Submodule.starProjection_apply_mem _ u
  have hz : twoFormHodgeForm u (twoFormHarmonicProjection u) = 0 := by
    rw [twoFormHodgeForm_comm]
    exact twoFormHodgeForm_zero_left hRic _
      ((mem_twoFormWeitzenbockKernel_iff_energy_zero hRic _).mp hp) u
  have hP : twoFormHarmonicProjection u = 0 := by
    have h := he (twoFormHarmonicProjection u)
    rw [hz, hf _ hp, zero_add] at h
    exact inner_self_eq_zero.mp h
  refine ⟨u, ?_, fun v => ?_⟩
  · intro v hv
    have h := Submodule.starProjection_inner_eq_zero
      (K := twoFormWeitzenbockKernel (o := o)) u v hv
    change inner ℝ (u - twoFormHarmonicProjection u) v = 0 at h
    simpa only [hP, sub_zero] using h
  · simpa only [hP, inner_zero_left, add_zero] using he v

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

variable (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_11
def scalarHeatH1Lift (t : ℝ≥0) (ht : 0 < t) : Lp ℝ 2 (normalizedVolume g) →L[ℝ] scalarH1 d :=
  (scalarBaseShiftedSolution g o d).comp (scalarBaseHeatLiftSource g o d t ht)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual codifferential extends continuously from the two-form H1
completion into the one-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothH1Codifferential_norm_le (hRic : RicciThree g) (u : SmoothH1TwoForm o) :
    ‖smoothH1Codifferential u‖ ≤ (1 + ‖twoFormWeitzenbockPotential (o := o)‖) * ‖u‖ := by
  let v := smoothTwoFormToH1 u
  let w := twoFormH1ToL2 v
  let K := ‖twoFormWeitzenbockPotential (o := o)‖
  have hK : 0 ≤ K := norm_nonneg _
  have hv : ‖v‖ = ‖u‖ := smoothTwoFormToH1.norm_map u
  have hw : ‖w‖ ≤ ‖u‖ := (twoFormH1ToL2_norm_le v).trans_eq hv
  have hc : 0 ≤ twoFormCodiffPairing (smoothTwoFormHodge o (u : smoothTwoForms o))
      (smoothTwoFormHodge o (u : smoothTwoForms o)) := by
    exact integral_nonneg fun e => Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have he : ‖smoothH1Codifferential u‖ ^ 2 ≤ twoFormHodgeForm v v := by
    have hf := twoFormHodgeForm_smooth hRic u
    have hs := smoothTwoFormDeRhamEnergy_codiff (u : smoothTwoForms o)
    have hn := smoothH1Codifferential_norm_sq u
    change twoFormHodgeForm v v = _ at hf
    linarith only [hf, hs, hn, hc]
  have hi : -inner ℝ (twoFormWeitzenbockPotential w) w ≤ K * ‖u‖ ^ 2 := by
    calc
      -inner ℝ (twoFormWeitzenbockPotential w) w ≤
          ‖twoFormWeitzenbockPotential w‖ * ‖w‖ :=
        (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
      _ ≤ (K * ‖w‖) * ‖w‖ := mul_le_mul_of_nonneg_right
        (twoFormWeitzenbockPotential.le_opNorm w) (norm_nonneg _)
      _ ≤ K * ‖u‖ ^ 2 := by
        have hs := (sq_le_sq₀ (norm_nonneg w) (norm_nonneg u)).mpr hw
        nlinarith [mul_le_mul_of_nonneg_left hs hK]
  have hb : ‖smoothH1Codifferential u‖ ^ 2 ≤ (1 + K) * ‖u‖ ^ 2 := by
    change ‖smoothH1Codifferential u‖ ^ 2 ≤ inner ℝ v v -
      inner ℝ (twoFormWeitzenbockPotential w) w at he
    rw [real_inner_self_eq_norm_sq, hv] at he
    nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp
  have hk : 1 + K ≤ (1 + K) ^ 2 := by nlinarith
  calc
    ‖smoothH1Codifferential u‖ ^ 2 ≤ (1 + K) * ‖u‖ ^ 2 := hb
    _ ≤ (1 + K) ^ 2 * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right hk (sq_nonneg _)
    _ = ((1 + K) * ‖u‖) ^ 2 := by ring

def smoothH1CodifferentialCLM (hRic : RicciThree g) :
    SmoothH1TwoForm o →L[ℝ] SmoothL2OneForm o :=
  smoothH1Codifferential.mkContinuous (1 + ‖twoFormWeitzenbockPotential (o := o)‖)
    (smoothH1Codifferential_norm_le hRic)

def twoFormH1Codifferential (hRic : RicciThree g) : TwoFormH1 o →L[ℝ] OneFormL2 o :=
  (smoothOneFormToL2.toContinuousLinearMap.comp (smoothH1CodifferentialCLM hRic)).fromCompletion

theorem twoFormH1Codifferential_smooth (hRic : RicciThree g) (u : SmoothH1TwoForm o) :
    twoFormH1Codifferential hRic (smoothTwoFormToH1 u) =
      smoothOneFormToL2 ⟨smoothTwoFormCodifferentialField (u : smoothTwoForms o)⟩ :=
  ContinuousLinearMap.fromCompletion_apply_coe _ u

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory09
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The harmonic equation has actual integer-order forcing in its scalar
principal part. No regularity of the weak solution is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hreg in
theorem twoFormHarmonic_principalWeakInteger (b : TwoFormFour) :
    ∃ R : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 R : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
      inner ℝ R (twoFormScalarTestL2 ψ hψ hcψ) := by
  obtain ⟨D, hD, hDH⟩ := twoFormFluxCorrection_integer_derivatives n c S hS hK hKt hVK u hreg
    η hη hcη hηV b
  let F := fun j => twoFormDivergenceFlux (g := g) c η hη hcη ((hηV.trans hVK).trans hKt) b
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u) j
  let C := fun j => twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j
  let R₀ := twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
    (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)
  refine ⟨R₀ - ∑ j : Fin 4, D j, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (_ - _))
    rw [map_sub]
    have hsum : MemSobolev (n : ℝ) 2 (scalarComplexL2 (∑ j : Fin 4, D j) :
        𝓢'(FourSpace, ℂ)) := by
      apply scalarReal_memSobolev_finset n
      intro j _
      exact hDH j
    exact (twoFormHarmonicDivergenceSource_integer n c S hS hK hKt hV hVK u hreg
      η hη hcη hηV b).sub hsum
  · intro ψ hψ hcψ hψK hon
    have hF := twoFormRough_scalarWeakEquation c S hS η ψ hη hcη hψ hcψ hon b
      hK hKt (hηV.trans hVK) hψK U hU hUt hKU hp u
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u)) hu
    have he := scalar_divergence_corrected_flux F C D R₀ hD ψ hψ hcψ hF
    have heq : (∑ j : Fin 4, inner ℝ (F j + C j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
        ∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
          (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
            (hcψ.fderiv_apply ℝ (coordinateVector j))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v => inner ℝ v (twoFormScalarTestL2 (fun z => partialDeriv ψ j z)
        (twoFormCutoffPartial_smooth ψ hψ j) (hcψ.fderiv_apply ℝ (coordinateVector j))))
        (twoFormPrincipalFlux_eq c S hS hK hKt η hη hcη (hηV.trans hVK) b u j)
    rw [heq] at he
    exact he

include hV hU hKU hp hu hreg in
theorem twoFormHarmonic_weightedWeakInteger (r : Fin 6) :
    ∃ F : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 F : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = ∫ z, F z * ψ z := by
  obtain ⟨R, hRH, hR⟩ := twoFormHarmonic_principalWeakInteger n c S hS hK hKt hV hVK U hU hUt hKU hp u hu hreg η hη hcη hηV
      (EuclideanSpace.basisFun (Fin 6) ℝ r)
  refine ⟨-R, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (-R))
    rw [map_neg]
    exact hRH.neg
  · intro ψ hψ hcψ hψK hon
    have he := hR ψ hψ hcψ hψK hon
    rw [twoFormPrincipalFlux_integrationByParts c η ψ hη hψ hcψ S hK hKt hcη (hηV.trans hVK) u r,
      twoFormWeightedComponent_operator_pairing c S hK hKt η hη hcη (hηV.trans hVK) r u
        ψ hψ hcψ (hψK.trans hKt) hon] at he
    have hv : (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = inner ℝ (-R) (twoFormScalarTestL2 ψ hψ hcψ) := by
      rw [inner_neg_left]
      linarith only [he]
    rw [hv, L2.inner_def]
    simp only [RCLike.inner_apply', conj_trivial]
    apply integral_congr_ae
    filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with z hz
    exact congrArg (fun t => (-R) z * t) hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! One actual local elliptic step for harmonic two-forms at any finite
Sobolev order, with the metric coefficients and forcing from the Hodge equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hreg in
theorem twoFormHarmonic_weighted_integer (r : Fin 6) (z₀ : ChartTarget c)
    (hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val) :
    ∃ (t : ℝ) (ht : 0 < t),
      (∀ y ∈ closedBall (0 : FourSpace) 1,
        scalarRescaledPoint g c z₀ t y ∈ K ∧ η (scalarRescaledPoint g c z₀ t y) = 1) ∧
      ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
        tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
        MemSobolev ((n + 2 : ℕ) : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2
          (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht.ne') z₀
            (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u)) :
              𝓢'(FourSpace, ℂ))) := by
  obtain ⟨F, hFH, hF⟩ := twoFormHarmonic_weightedWeakInteger n c S hS hK hKt hV hVK
    U hU hUt hKU hp u hu hreg η hη hcη hηV r
  apply scalarEuclidean_local_integer n g c z₀ {z | z ∈ K ∧ η z = 1} hnear
    (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u) F
    (twoFormWeightedComponent_H1 c S hK hKt η hη hcη (hηV.trans hVK) r u) hFH
  intro ψ hψ hcψ hsψ
  exact hF ψ hψ hcψ (fun z hz => (hsψ hz).1) (fun z hz => (hsψ hz).2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The smooth-source Hodge-Poisson equation has actual integer-order forcing in its scalar
principal part. No regularity of the weak solution is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o) (f : smoothTwoForms o)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hreg in
theorem twoFormPoisson_principalWeakInteger (b : TwoFormFour) :
    ∃ R : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 R : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
      inner ℝ R (twoFormScalarTestL2 ψ hψ hcψ) := by
  obtain ⟨D, hD, hDH⟩ := twoFormFluxCorrection_integer_derivatives n c S hS hK hKt hVK u hreg
    η hη hcη hηV b
  let F := fun j => twoFormDivergenceFlux (g := g) c η hη hcη ((hηV.trans hVK).trans hKt) b
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u) j
  let C := fun j => twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j
  let R₀ := twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
    (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o)))
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)
  refine ⟨R₀ - ∑ j : Fin 4, D j, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (_ - _))
    rw [map_sub]
    have hsum : MemSobolev (n : ℝ) 2 (scalarComplexL2 (∑ j : Fin 4, D j) :
        𝓢'(FourSpace, ℂ)) := by
      apply scalarReal_memSobolev_finset n
      intro j _
      exact hDH j
    exact (twoFormPoissonDivergenceSource_integer n c S hS hK hKt hV hVK u f hreg
      η hη hcη hηV b).sub hsum
  · intro ψ hψ hcψ hψK hon
    have hF := twoFormRough_scalarWeakEquation c S hS η ψ hη hcη hψ hcψ hon b
      hK hKt (hηV.trans hVK) hψK U hU hUt hKU hp u
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o)) hu
    have he := scalar_divergence_corrected_flux F C D R₀ hD ψ hψ hcψ hF
    have heq : (∑ j : Fin 4, inner ℝ (F j + C j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
        ∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
          (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
            (hcψ.fderiv_apply ℝ (coordinateVector j))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v => inner ℝ v (twoFormScalarTestL2 (fun z => partialDeriv ψ j z)
        (twoFormCutoffPartial_smooth ψ hψ j) (hcψ.fderiv_apply ℝ (coordinateVector j))))
        (twoFormPrincipalFlux_eq c S hS hK hKt η hη hcη (hηV.trans hVK) b u j)
    rw [heq] at he
    exact he

include hV hU hKU hp hu hreg in
theorem twoFormPoisson_weightedWeakInteger (r : Fin 6) :
    ∃ F : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 F : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = ∫ z, F z * ψ z := by
  obtain ⟨R, hRH, hR⟩ := twoFormPoisson_principalWeakInteger n c S hS hK hKt hV hVK U hU hUt hKU hp u f hu hreg η hη hcη hηV
      (EuclideanSpace.basisFun (Fin 6) ℝ r)
  refine ⟨-R, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (-R))
    rw [map_neg]
    exact hRH.neg
  · intro ψ hψ hcψ hψK hon
    have he := hR ψ hψ hcψ hψK hon
    rw [twoFormPrincipalFlux_integrationByParts c η ψ hη hψ hcψ S hK hKt hcη (hηV.trans hVK) u r,
      twoFormWeightedComponent_operator_pairing c S hK hKt η hη hcη (hηV.trans hVK) r u
        ψ hψ hcψ (hψK.trans hKt) hon] at he
    have hv : (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = inner ℝ (-R) (twoFormScalarTestL2 ψ hψ hcψ) := by
      rw [inner_neg_left]
      linarith only [he]
    rw [hv, L2.inner_def]
    simp only [RCLike.inner_apply', conj_trivial]
    apply integral_congr_ae
    filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with z hz
    exact congrArg (fun t => (-R) z * t) hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite-regularity-source Hodge equation has actual integer-order forcing in its scalar
principal part. No regularity of the weak solution is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o) (f : TwoFormL2 o)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + f))

  (hsource : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (r : Fin 6), MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormVectorComponentL2 r (twoFormL2GramValue c S hK hKt a ha hc
        (hs.trans hVK) hS f)) : 𝓢'(FourSpace, ℂ)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hsource hreg in
theorem twoFormRegularSource_principalWeakInteger (b : TwoFormFour) :
    ∃ R : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 R : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
      inner ℝ R (twoFormScalarTestL2 ψ hψ hcψ) := by
  obtain ⟨D, hD, hDH⟩ := twoFormFluxCorrection_integer_derivatives n c S hS hK hKt hVK u hreg
    η hη hcη hηV b
  let F := fun j => twoFormDivergenceFlux (g := g) c η hη hcη ((hηV.trans hVK).trans hKt) b
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u) j
  let C := fun j => twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j
  let R₀ := twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
    (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + f))
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)
  refine ⟨R₀ - ∑ j : Fin 4, D j, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (_ - _))
    rw [map_sub]
    have hsum : MemSobolev (n : ℝ) 2 (scalarComplexL2 (∑ j : Fin 4, D j) :
        𝓢'(FourSpace, ℂ)) := by
      apply scalarReal_memSobolev_finset n
      intro j _
      exact hDH j
    exact (twoFormRegularSourceDivergenceSource_integer n c S hS hK hKt hV hVK u f hsource hreg
      η hη hcη hηV b).sub hsum
  · intro ψ hψ hcψ hψK hon
    have hF := twoFormRough_scalarWeakEquation c S hS η ψ hη hcη hψ hcψ hon b
      hK hKt (hηV.trans hVK) hψK U hU hUt hKU hp u
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + f) hu
    have he := scalar_divergence_corrected_flux F C D R₀ hD ψ hψ hcψ hF
    have heq : (∑ j : Fin 4, inner ℝ (F j + C j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
        ∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
          (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
            (hcψ.fderiv_apply ℝ (coordinateVector j))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v => inner ℝ v (twoFormScalarTestL2 (fun z => partialDeriv ψ j z)
        (twoFormCutoffPartial_smooth ψ hψ j) (hcψ.fderiv_apply ℝ (coordinateVector j))))
        (twoFormPrincipalFlux_eq c S hS hK hKt η hη hcη (hηV.trans hVK) b u j)
    rw [heq] at he
    exact he

include hV hU hKU hp hu hsource hreg in
theorem twoFormRegularSource_weightedWeakInteger (r : Fin 6) :
    ∃ F : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 F : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = ∫ z, F z * ψ z := by
  obtain ⟨R, hRH, hR⟩ := twoFormRegularSource_principalWeakInteger n c S hS hK hKt hV hVK U hU hUt hKU hp u f hu hsource hreg η hη hcη hηV
      (EuclideanSpace.basisFun (Fin 6) ℝ r)
  refine ⟨-R, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (-R))
    rw [map_neg]
    exact hRH.neg
  · intro ψ hψ hcψ hψK hon
    have he := hR ψ hψ hcψ hψK hon
    rw [twoFormPrincipalFlux_integrationByParts c η ψ hη hψ hcψ S hK hKt hcη (hηV.trans hVK) u r,
      twoFormWeightedComponent_operator_pairing c S hK hKt η hη hcη (hηV.trans hVK) r u
        ψ hψ hcψ (hψK.trans hKt) hon] at he
    have hv : (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = inner ℝ (-R) (twoFormScalarTestL2 ψ hψ hcψ) := by
      rw [inner_neg_left]
      linarith only [he]
    rw [hv, L2.inner_def]
    simp only [RCLike.inner_apply', conj_trivial]
    apply integral_congr_ae
    filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with z hz
    exact congrArg (fun t => (-R) z * t) hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! A harmonic two-form with local H^(n+1) control has actual H^(n+2)
representatives near each point, in the original chart coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHarmonic_improved_representative (n : ℕ) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) {K V : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
    (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
    (r : Fin 6) (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ w : Lp ℂ 2 (volume : Measure FourSpace),
          MemSobolev ((n + 2 : ℕ) : ℝ) 2 (w : 𝓢'(FourSpace, ℂ)) ∧
          (w : FourSpace → ℂ) =ᵐ[volume.restrict W] fun z =>
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u z : ℂ) := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val := by
    filter_upwards [η.eventuallyEq_one] with z hz
    exact ⟨hηK (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [show η z = 1 from hz]; norm_num)), hz⟩
  obtain ⟨t, ht, hpoint, hgain⟩ := twoFormHarmonic_weighted_integer n c S hS hK hKt hV hVK
    U hU hUt hKU hp u hu hreg η η.contDiff η.hasCompactSupport hηV r z₀ hnear
  let A := scalarRescalingLinearEquiv g c z₀ t ht.ne'
  let β : ContDiffBump (0 : FourSpace) :=
    { rIn := 1 / 8
      rOut := 1 / 4
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  have hsβ : tsupport (β : FourSpace → ℝ) ⊆ ball (0 : FourSpace) (1 / 2) := by
    rw [β.tsupport_eq]
    exact closedBall_subset_ball (by norm_num)
  obtain ⟨w, hw, he⟩ := twoFormInteger_unweight_unscale c S hK hKt η η.contDiff η.hasCompactSupport
    hηK r u z₀ t ht.ne' hpoint (n + 2) hgain β β.contDiff β.hasCompactSupport hsβ
  let W : Set FourSpace := (fun z => A.symm (z - z₀)) ⁻¹' ball 0 (1 / 8)
  have hW : IsOpen W := isOpen_ball.preimage (by fun_prop)
  have hzW : z₀.val ∈ W := by
    dsimp only [W]
    simp only [Set.mem_preimage, sub_self, map_zero, mem_ball, dist_self]
    norm_num
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ t (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ t ht.ne']
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hone (z : FourSpace) (hz : z ∈ W) : η z = 1 := by
    have hpz := hpoint (A.symm (z - z₀))
      (closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hz))
    rw [hinv] at hpz
    exact hpz.2
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, W, hW, hzW, ?_, hone, w, hw, ?_⟩
  · intro z hz
    exact hηV (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [hone z hz]; norm_num))
  · filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hW.measurableSet] with z hz hzW
    rw [hz, β.one_of_mem_closedBall (ball_subset_closedBall hzW), one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! One actual local elliptic step for smooth-source Hodge-Poisson two-forms at any finite
Sobolev order, with the metric coefficients and forcing from the Hodge equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o) (f : smoothTwoForms o)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hreg in
theorem twoFormPoisson_weighted_integer (r : Fin 6) (z₀ : ChartTarget c)
    (hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val) :
    ∃ (t : ℝ) (ht : 0 < t),
      (∀ y ∈ closedBall (0 : FourSpace) 1,
        scalarRescaledPoint g c z₀ t y ∈ K ∧ η (scalarRescaledPoint g c z₀ t y) = 1) ∧
      ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
        tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
        MemSobolev ((n + 2 : ℕ) : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2
          (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht.ne') z₀
            (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u)) :
              𝓢'(FourSpace, ℂ))) := by
  obtain ⟨F, hFH, hF⟩ := twoFormPoisson_weightedWeakInteger n c S hS hK hKt hV hVK
    U hU hUt hKU hp u f hu hreg η hη hcη hηV r
  apply scalarEuclidean_local_integer n g c z₀ {z | z ∈ K ∧ η z = 1} hnear
    (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u) F
    (twoFormWeightedComponent_H1 c S hK hKt η hη hcη (hηV.trans hVK) r u) hFH
  intro ψ hψ hcψ hsψ
  exact hF ψ hψ hcψ (fun z hz => (hsψ hz).1) (fun z hz => (hsψ hz).2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! One actual local elliptic step for finite-regularity-source Hodge two-forms at any finite
Sobolev order, with the metric coefficients and forcing from the Hodge equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o) (f : TwoFormL2 o)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + f))

  (hsource : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (r : Fin 6), MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormVectorComponentL2 r (twoFormL2GramValue c S hK hKt a ha hc
        (hs.trans hVK) hS f)) : 𝓢'(FourSpace, ℂ)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hsource hreg in
theorem twoFormRegularSource_weighted_integer (r : Fin 6) (z₀ : ChartTarget c)
    (hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val) :
    ∃ (t : ℝ) (ht : 0 < t),
      (∀ y ∈ closedBall (0 : FourSpace) 1,
        scalarRescaledPoint g c z₀ t y ∈ K ∧ η (scalarRescaledPoint g c z₀ t y) = 1) ∧
      ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
        tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
        MemSobolev ((n + 2 : ℕ) : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2
          (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht.ne') z₀
            (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u)) :
              𝓢'(FourSpace, ℂ))) := by
  obtain ⟨F, hFH, hF⟩ := twoFormRegularSource_weightedWeakInteger n c S hS hK hKt hV hVK
    U hU hUt hKU hp u f hu hsource hreg η hη hcη hηV r
  apply scalarEuclidean_local_integer n g c z₀ {z | z ∈ K ∧ η z = 1} hnear
    (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u) F
    (twoFormWeightedComponent_H1 c S hK hKt η hη hcη (hηV.trans hVK) r u) hFH
  intro ψ hψ hcψ hsψ
  exact hF ψ hψ hcψ (fun z hz => (hsψ hz).1) (fun z hz => (hsψ hz).2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every compact chart cutoff of an actual weak harmonic two-form has
all integer Sobolev orders. The bootstrap stays on a fixed open set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHarmonic_local_all_orders (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u))) :
    ∀ (n : ℕ) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev (n : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
  have hreg : ∀ (n : ℕ) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
    intro n
    induction n with
    | zero =>
        intro a ha hc hs v
        simpa only [Nat.zero_add, Nat.cast_one] using
          twoFormGram_memSobolev_one c S hK hKt a ha hc (hs.trans hVK) v u
    | succ n ih =>
        intro a ha hc hs v
        change MemSobolev ((n + 2 : ℕ) : ℝ) 2 _
        apply twoForm_local_sobolev_assembly (n + 2) c S hS hK hKt hVK u _ a ha hc hs v
        intro r x hx
        let z₀ : ChartTarget c := ⟨x, hKt (hVK hx)⟩
        obtain ⟨η, hη, hcη, hηK, W, hW, hxW, _, hone, w, hw, he⟩ :=
          twoFormHarmonic_improved_representative n c S hS hK hKt hV hVK U hU hUt hKU hp
            u hu ih r z₀ hx
        exact ⟨η, hη, hcη, hηK, W, hW, hxW, hone, w, hw, he⟩
  intro n a ha hc hs v
  exact (hreg n a ha hc hs v).mono (by exact_mod_cast Nat.le_succ n)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth-source Hodge-Poisson two-form with local H^(n+1) control has actual H^(n+2)
representatives near each point, in the original chart coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormPoisson_improved_representative (n : ℕ) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) {K V : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (f : smoothTwoForms o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o)))
    (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
    (r : Fin 6) (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ w : Lp ℂ 2 (volume : Measure FourSpace),
          MemSobolev ((n + 2 : ℕ) : ℝ) 2 (w : 𝓢'(FourSpace, ℂ)) ∧
          (w : FourSpace → ℂ) =ᵐ[volume.restrict W] fun z =>
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u z : ℂ) := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val := by
    filter_upwards [η.eventuallyEq_one] with z hz
    exact ⟨hηK (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [show η z = 1 from hz]; norm_num)), hz⟩
  obtain ⟨t, ht, hpoint, hgain⟩ := twoFormPoisson_weighted_integer n c S hS hK hKt hV hVK
    U hU hUt hKU hp u f hu hreg η η.contDiff η.hasCompactSupport hηV r z₀ hnear
  let A := scalarRescalingLinearEquiv g c z₀ t ht.ne'
  let β : ContDiffBump (0 : FourSpace) :=
    { rIn := 1 / 8
      rOut := 1 / 4
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  have hsβ : tsupport (β : FourSpace → ℝ) ⊆ ball (0 : FourSpace) (1 / 2) := by
    rw [β.tsupport_eq]
    exact closedBall_subset_ball (by norm_num)
  obtain ⟨w, hw, he⟩ := twoFormInteger_unweight_unscale c S hK hKt η η.contDiff η.hasCompactSupport
    hηK r u z₀ t ht.ne' hpoint (n + 2) hgain β β.contDiff β.hasCompactSupport hsβ
  let W : Set FourSpace := (fun z => A.symm (z - z₀)) ⁻¹' ball 0 (1 / 8)
  have hW : IsOpen W := isOpen_ball.preimage (by fun_prop)
  have hzW : z₀.val ∈ W := by
    dsimp only [W]
    simp only [Set.mem_preimage, sub_self, map_zero, mem_ball, dist_self]
    norm_num
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ t (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ t ht.ne']
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hone (z : FourSpace) (hz : z ∈ W) : η z = 1 := by
    have hpz := hpoint (A.symm (z - z₀))
      (closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hz))
    rw [hinv] at hpz
    exact hpz.2
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, W, hW, hzW, ?_, hone, w, hw, ?_⟩
  · intro z hz
    exact hηV (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [hone z hz]; norm_num))
  · filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hW.measurableSet] with z hz hzW
    rw [hz, β.one_of_mem_closedBall (ball_subset_closedBall hzW), one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A finite-regularity-source Hodge two-form with local H^(n+1) control has actual H^(n+2)
representatives near each point, in the original chart coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormRegularSource_improved_representative (n : ℕ) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) {K V : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + f))

  (hsource : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (r : Fin 6), MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormVectorComponentL2 r (twoFormL2GramValue c S hK hKt a ha hc
        (hs.trans hVK) hS f)) : 𝓢'(FourSpace, ℂ)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
    (r : Fin 6) (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ w : Lp ℂ 2 (volume : Measure FourSpace),
          MemSobolev ((n + 2 : ℕ) : ℝ) 2 (w : 𝓢'(FourSpace, ℂ)) ∧
          (w : FourSpace → ℂ) =ᵐ[volume.restrict W] fun z =>
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u z : ℂ) := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val := by
    filter_upwards [η.eventuallyEq_one] with z hz
    exact ⟨hηK (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [show η z = 1 from hz]; norm_num)), hz⟩
  obtain ⟨t, ht, hpoint, hgain⟩ := twoFormRegularSource_weighted_integer n c S hS hK hKt hV hVK
    U hU hUt hKU hp u f hu hsource hreg η η.contDiff η.hasCompactSupport hηV r z₀ hnear
  let A := scalarRescalingLinearEquiv g c z₀ t ht.ne'
  let β : ContDiffBump (0 : FourSpace) :=
    { rIn := 1 / 8
      rOut := 1 / 4
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  have hsβ : tsupport (β : FourSpace → ℝ) ⊆ ball (0 : FourSpace) (1 / 2) := by
    rw [β.tsupport_eq]
    exact closedBall_subset_ball (by norm_num)
  obtain ⟨w, hw, he⟩ := twoFormInteger_unweight_unscale c S hK hKt η η.contDiff η.hasCompactSupport
    hηK r u z₀ t ht.ne' hpoint (n + 2) hgain β β.contDiff β.hasCompactSupport hsβ
  let W : Set FourSpace := (fun z => A.symm (z - z₀)) ⁻¹' ball 0 (1 / 8)
  have hW : IsOpen W := isOpen_ball.preimage (by fun_prop)
  have hzW : z₀.val ∈ W := by
    dsimp only [W]
    simp only [Set.mem_preimage, sub_self, map_zero, mem_ball, dist_self]
    norm_num
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ t (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ t ht.ne']
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hone (z : FourSpace) (hz : z ∈ W) : η z = 1 := by
    have hpz := hpoint (A.symm (z - z₀))
      (closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hz))
    rw [hinv] at hpz
    exact hpz.2
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, W, hW, hzW, ?_, hone, w, hw, ?_⟩
  · intro z hz
    exact hηV (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [hone z hz]; norm_num))
  · filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hW.measurableSet] with z hz hzW
    rw [hz, β.one_of_mem_closedBall (ball_subset_closedBall hzW), one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth representatives of the six actual harmonic chart coefficients,
on one common neighborhood. All Sobolev estimates come from the weak
harmonic equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHarmonic_smooth_coefficients (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
    (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ F : Fin 6 → FourSpace → ℝ,
          (∀ r, ContDiff ℝ ∞ (F r)) ∧ ∀ r,
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u :
              FourSpace → ℝ) =ᵐ[volume] F r := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hreg (r : Fin 6) (n : ℕ) : MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u) : 𝓢'(FourSpace, ℂ)) :=
    twoFormHarmonic_local_all_orders c S hS hK hKt hV hVK U hU hUt hKU hp u hu n
      η η.contDiff η.hasCompactSupport hηV (twoFormComponentIndex r)
  have hrep (r : Fin 6) : ∃ f : FourSpace → ℝ, ContDiff ℝ ∞ f ∧
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u : FourSpace → ℝ) =ᵐ[volume] f := by
    obtain ⟨f, hf, he⟩ := scalar_L2_sobolev_smooth_real_representative
      (scalarComplexL2 (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u)) (hreg r)
    refine ⟨f, hf, ?_⟩
    filter_upwards [he, scalarComplexL2_coe (twoFormGramValueL2 c S hK hKt η η.contDiff
      η.hasCompactSupport hηK (twoFormComponentIndex r) u)] with z hz hc
    simpa only [hc, Complex.ofReal_re] using hz
  choose F hF he using hrep
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, ball z₀.val (d / 2), isOpen_ball,
    mem_ball_self (half_pos hd), ?_, ?_, F, hF, he⟩
  · exact (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (half_le_self hd.le))).trans hdV
  · intro z hz
    exact η.one_of_mem_closedBall (ball_subset_closedBall hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every compact chart cutoff of an actual weak smooth-source Hodge-Poisson two-form has
all integer Sobolev orders. The bootstrap stays on a fixed open set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormPoisson_local_all_orders (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (f : smoothTwoForms o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o))) :
    ∀ (n : ℕ) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev (n : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
  have hreg : ∀ (n : ℕ) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
    intro n
    induction n with
    | zero =>
        intro a ha hc hs v
        simpa only [Nat.zero_add, Nat.cast_one] using
          twoFormGram_memSobolev_one c S hK hKt a ha hc (hs.trans hVK) v u
    | succ n ih =>
        intro a ha hc hs v
        change MemSobolev ((n + 2 : ℕ) : ℝ) 2 _
        apply twoForm_local_sobolev_assembly (n + 2) c S hS hK hKt hVK u _ a ha hc hs v
        intro r x hx
        let z₀ : ChartTarget c := ⟨x, hKt (hVK hx)⟩
        obtain ⟨η, hη, hcη, hηK, W, hW, hxW, _, hone, w, hw, he⟩ :=
          twoFormPoisson_improved_representative n c S hS hK hKt hV hVK U hU hUt hKU hp
            u f hu ih r z₀ hx
        exact ⟨η, hη, hcη, hηK, W, hW, hxW, hone, w, hw, he⟩
  intro n a ha hc hs v
  exact (hreg n a ha hc hs v).mono (by exact_mod_cast Nat.le_succ n)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite-order local regularity of the actual shifted Hodge resolvent.
The forcing is an H1 section with the indicated local Sobolev order. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormRegularSource_chart_gain (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
    (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + f))
    (hsource : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (r : Fin 6), MemSobolev (n : ℝ) 2 (scalarComplexL2
        (twoFormVectorComponentL2 r (twoFormL2GramValue c S hK hKt a ha hc
          (hs.trans hVK) hS f)) : 𝓢'(FourSpace, ℂ)))
    (hreg : TwoFormChartSobolev (n + 1) c S hK hKt hVK u) :
    TwoFormChartSobolev (n + 2) c S hK hKt hVK u := by
  intro a ha hc hs v
  apply twoForm_local_sobolev_assembly (n + 2) c S hS hK hKt hVK u _ a ha hc hs v
  intro r x hx
  let z₀ : ChartTarget c := ⟨x, hKt (hVK hx)⟩
  obtain ⟨η, hη, hcη, hηK, W, hW, hxW, _, hone, w, hw, he⟩ :=
    twoFormRegularSource_improved_representative n c S hS hK hKt hV hVK U hU hUt hKU hp
      u f hu hsource hreg r z₀ hx
  exact ⟨η, hη, hcη, hηK, W, hW, hxW, hone, w, hw, he⟩

theorem twoFormShiftedSolution_chart_gain (n : ℕ) (hRic : RicciThree g)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
    (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (v : TwoFormH1 o) (hv : TwoFormChartSobolev n c S hK hKt hVK v) :
    TwoFormChartSobolev (n + 2) c S hK hKt hVK
      (twoFormShiftedSolution hRic (twoFormH1ToL2 v)) := by
  let u := twoFormShiftedSolution hRic (twoFormH1ToL2 v)
  have hgain (k : ℕ) (hk : k ≤ n) (hu : TwoFormChartSobolev (k + 1) c S hK hKt hVK u) :
      TwoFormChartSobolev (k + 2) c S hK hKt hVK u := by
    apply twoFormRegularSource_chart_gain k c S hS hK hKt hV hVK U hU hUt hKU hp u
      (twoFormH1ToL2 v - twoFormH1ToL2 u) (twoFormShiftedSolution_rough hRic _) _ hu
    intro a ha hc hs r
    let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (k : ℝ) 2 (C (twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt a ha hc (hs.trans hVK) hS
        (twoFormH1ToL2 v - twoFormH1ToL2 u))))
    rw [map_sub, map_sub, map_sub, twoFormL2GramValue_H1, twoFormL2GramValue_H1,
      twoFormGramVectorComponent, twoFormGramVectorComponent]
    exact ((hv.mono hk) a ha hc hs (twoFormComponentIndex r)).sub
      ((hu.mono (Nat.le_succ k)) a ha hc hs (twoFormComponentIndex r))
  have hrec (k : ℕ) : k ≤ n → TwoFormChartSobolev (k + 2) c S hK hKt hVK u := by
    induction k with
    | zero =>
        intro hk
        exact hgain 0 hk (twoFormChartSobolev_one c S hK hKt hVK u)
    | succ k ih =>
        intro hk
        exact hgain (k + 1) hk (ih (Nat.le_trans (Nat.le_succ k) hk))
  exact hrec n le_rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual finite-order smoothing of the positive-time Hodge heat operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
  {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hV hU hKU hp in
theorem twoFormResolvent_iterate_chart_order (k : ℕ) (f : TwoFormL2 o) :
    TwoFormChartSobolev (2 * k + 1) c S hK hKt hVK
      (twoFormShiftedSolution hRic ((twoFormShiftedResolvent hRic ^ k) f)) := by
  induction k with
  | zero =>
      change TwoFormChartSobolev 1 c S hK hKt hVK (twoFormShiftedSolution hRic f)
      exact twoFormChartSobolev_one c S hK hKt hVK (twoFormShiftedSolution hRic f)
  | succ k ih =>
      have he : twoFormH1ToL2 (twoFormShiftedSolution hRic
          ((twoFormShiftedResolvent hRic ^ k) f)) =
          (twoFormShiftedResolvent hRic ^ (k + 1)) f := by
        rw [pow_succ']
        rfl
      have hg := twoFormShiftedSolution_chart_gain (2 * k + 1) hRic c S hS hK hKt hV hVK
        U hU hUt hKU hp (twoFormShiftedSolution hRic ((twoFormShiftedResolvent hRic ^ k) f)) ih
      rw [he] at hg
      convert hg using 1
      all_goals try with_reducible_and_instances rfl

include hV hU hKU hp in
theorem twoFormHeatLift_chart_order (t : ℝ≥0) (ht : 0 < t) (f : TwoFormL2 o) (n : ℕ) :
    TwoFormChartSobolev n c S hK hKt hVK (twoFormHeatLift hRic t ht f) := by
  let F := twoFormHeatPowerSource hRic t ht (n + 1) f
  let u := twoFormShiftedSolution hRic ((twoFormShiftedResolvent hRic ^ n) F)
  have he : twoFormH1ToL2 u = twoFormHeat hRic t f := by
    change twoFormShiftedResolvent hRic ((twoFormShiftedResolvent hRic ^ n) F) = _
    have hpw := twoFormHeatPowerSource_resolvent hRic t ht (n + 1) f
    rw [pow_succ'] at hpw
    exact hpw
  have hu : u = twoFormHeatLift hRic t ht f :=
    twoFormH1ToL2_injective hRic (he.trans (twoFormHeatLift_value hRic t ht f).symm)
  have hg := twoFormResolvent_iterate_chart_order hRic c S hS hK hKt hV hVK U hU hUt hKU hp n F
  change TwoFormChartSobolev (2 * n + 1) c S hK hKt hVK u at hg
  rw [hu] at hg
  exact hg.mono (by omega)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth representatives of the six actual smooth-source Hodge-Poisson chart coefficients,
on one common neighborhood. All Sobolev estimates come from the weak
harmonic equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormPoisson_smooth_coefficients (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (f : smoothTwoForms o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o)))
    (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ F : Fin 6 → FourSpace → ℝ,
          (∀ r, ContDiff ℝ ∞ (F r)) ∧ ∀ r,
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u :
              FourSpace → ℝ) =ᵐ[volume] F r := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hreg (r : Fin 6) (n : ℕ) : MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u) : 𝓢'(FourSpace, ℂ)) :=
    twoFormPoisson_local_all_orders c S hS hK hKt hV hVK U hU hUt hKU hp u f hu n
      η η.contDiff η.hasCompactSupport hηV (twoFormComponentIndex r)
  have hrep (r : Fin 6) : ∃ f : FourSpace → ℝ, ContDiff ℝ ∞ f ∧
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u : FourSpace → ℝ) =ᵐ[volume] f := by
    obtain ⟨f, hf, he⟩ := scalar_L2_sobolev_smooth_real_representative
      (scalarComplexL2 (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u)) (hreg r)
    refine ⟨f, hf, ?_⟩
    filter_upwards [he, scalarComplexL2_coe (twoFormGramValueL2 c S hK hKt η η.contDiff
      η.hasCompactSupport hηK (twoFormComponentIndex r) u)] with z hz hc
    simpa only [hc, Complex.ofReal_re] using hz
  choose F hF he using hrep
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, ball z₀.val (d / 2), isOpen_ball,
    mem_ball_self (half_pos hd), ?_, ?_, F, hF, he⟩
  · exact (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (half_le_self hd.le))).trans hdV
  · intro z hz
    exact η.one_of_mem_closedBall (ball_subset_closedBall hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every actual weak harmonic two-form agrees locally, in all smooth
test pairings, with a constructed smooth global section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHarmonic_local_smooth (u : TwoFormH1 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u))) (x : M) :
    ∃ (O : Set M) (v : smoothTwoForms o), IsOpen O ∧ x ∈ O ∧
      ∀ w : smoothTwoForms o, tsupport w.val ⊆ O →
        inner ℝ (twoFormH1ToL2 u) (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) =
          inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o))
            (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) := by
  let z₀ : ChartTarget x := ⟨chartAt FourSpace x x, mem_chart_target FourSpace x⟩
  obtain ⟨S, hS, U, hU, hUt, hp, χ, hχ, hcχ, hχU, hnear⟩ :=
    twoForm_regularity_cutoff o x z₀
  let K := tsupport χ
  have hKt : K ⊆ (chartAt FourSpace x).target := hχU.trans hUt
  obtain ⟨V, hVKχ, hV, hzV⟩ := _root_.mem_nhds_iff.mp hnear
  have hVK : V ⊆ K := fun z hz => (hVKχ hz).1
  obtain ⟨η, hη, hcη, hηK, W, hW, hzW, hWV, hone, F, hF, heF⟩ :=
    twoFormHarmonic_smooth_coefficients x S hS hcχ hKt hV hVK U hU hUt hχU hp u hu z₀ hzV
  let B : FourSpace → TwoFormFour := fun z => WithLp.toLp 2 (fun r => F r z)
  have hB : ContDiff ℝ ∞ B := (contDiff_piLp (p := 2)).mpr hF
  have hrep : twoFormGramVectorL2 x S hcχ hKt η hη hcη hηK u =ᵐ[volume] B :=
    twoFormAssembleL2_coe _ u B heF
  obtain ⟨Z, v, hZ, hzZ, hZW, he⟩ := twoForm_smooth_local_representative x S hS hcχ hKt
    η hη hcη hηK hW (hWV.trans hVK) hone u B hB hrep z₀ hzW
  let O := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' Z
  refine ⟨O, v, (chartAt FourSpace x).isOpen_inter_preimage hZ,
    ⟨mem_chart_source FourSpace x, hzZ⟩, ?_⟩
  intro w hw
  have hws : tsupport w.val ⊆ (chartAt FourSpace x).symm '' Z := by
    intro y hy
    exact ⟨chartAt FourSpace x y, (hw hy).2, (chartAt FourSpace x).left_inv (hw hy).1⟩
  obtain ⟨a, ha, has, haw⟩ := twoForm_supported_gramTest x S hS hcχ hKt
    (hZW.trans (hWV.trans hVK)) w hws
  have he' := he a ha has
  have hl : smoothTwoFormToL2 (twoFormGramTest o x S a ha hcχ hKt
      (has.trans (hZW.trans (hWV.trans hVK)))) = smoothTwoFormToL2 (w : SmoothL2TwoForm o) :=
    congrArg (fun t : smoothTwoForms o => smoothTwoFormToL2 (t : SmoothL2TwoForm o)) haw
  exact (congrArg (fun t : TwoFormL2 o => inner ℝ (twoFormH1ToL2 u) t) hl).symm.trans
    (he'.trans (congrArg (fun t : TwoFormL2 o =>
      inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) t) hl))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local heat coefficients are bounded continuous functions, with a bound
by the L2 norm of the initial section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap NNReal BoundedContinuousFunction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
  (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
  {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
  (hs : tsupport a ⊆ V) (r : Fin 6)

include hV hU hKU hp in
theorem twoFormHeatChartL2_regular (f : TwoFormL2 o) :
    MemSobolev 3 2 (twoFormHeatChartL2 hRic t ht c S hK hKt hVK a ha hc hs r f :
      𝓢'(FourSpace, ℂ)) := by
  exact twoFormHeatLift_chart_order hRic c S hS hK hKt hV hVK U hU hUt hKU hp t ht f 3
    a ha hc hs (twoFormComponentIndex r)

def twoFormHeatChartContinuous : TwoFormL2 o →L[ℝ] (FourSpace →ᵇ ℂ) :=
  scalarH3ContinuousLift (twoFormHeatChartL2 hRic t ht c S hK hKt hVK a ha hc hs r)
    (twoFormHeatChartL2_regular hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r)

theorem twoFormHeatChartContinuous_ae (f : TwoFormL2 o) :
    (twoFormHeatChartL2 hRic t ht c S hK hKt hVK a ha hc hs r f : FourSpace → ℂ) =ᵐ[volume]
      twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r f :=
  scalarH3ContinuousLift_ae _ _ f

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth representatives of the six actual positive-time Hodge heat chart coefficients,
on one common neighborhood. All Sobolev estimates come from the weak
heat resolvent identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_smooth_coefficients (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (input : TwoFormL2 o)
    (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ F : Fin 6 → FourSpace → ℝ,
          (∀ r, ContDiff ℝ ∞ (F r)) ∧ ∀ r,
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) (twoFormHeatLift hRic t ht input) :
              FourSpace → ℝ) =ᵐ[volume] F r := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hreg (r : Fin 6) (n : ℕ) : MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) (twoFormHeatLift hRic t ht input)) : 𝓢'(FourSpace, ℂ)) :=
    twoFormHeatLift_chart_order hRic c S hS hK hKt hV hVK U hU hUt hKU hp t ht input n
      η η.contDiff η.hasCompactSupport hηV (twoFormComponentIndex r)
  have hrep (r : Fin 6) : ∃ f : FourSpace → ℝ, ContDiff ℝ ∞ f ∧
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) (twoFormHeatLift hRic t ht input) : FourSpace → ℝ) =ᵐ[volume] f := by
    obtain ⟨f, hf, he⟩ := scalar_L2_sobolev_smooth_real_representative
      (scalarComplexL2 (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) (twoFormHeatLift hRic t ht input))) (hreg r)
    refine ⟨f, hf, ?_⟩
    filter_upwards [he, scalarComplexL2_coe (twoFormGramValueL2 c S hK hKt η η.contDiff
      η.hasCompactSupport hηK (twoFormComponentIndex r) (twoFormHeatLift hRic t ht input))] with z hz hc
    simpa only [hc, Complex.ofReal_re] using hz
  choose F hF he using hrep
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, ball z₀.val (d / 2), isOpen_ball,
    mem_ball_self (half_pos hd), ?_, ?_, F, hF, he⟩
  · exact (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (half_le_self hd.le))).trans hdV
  · intro z hz
    exact η.one_of_mem_closedBall (ball_subset_closedBall hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every actual weak smooth-source Hodge-Poisson two-form agrees locally, in all smooth
test pairings, with a constructed smooth global section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormPoisson_local_smooth (u : TwoFormH1 o) (f : smoothTwoForms o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o))) (x : M) :
    ∃ (O : Set M) (v : smoothTwoForms o), IsOpen O ∧ x ∈ O ∧
      ∀ w : smoothTwoForms o, tsupport w.val ⊆ O →
        inner ℝ (twoFormH1ToL2 u) (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) =
          inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o))
            (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) := by
  let z₀ : ChartTarget x := ⟨chartAt FourSpace x x, mem_chart_target FourSpace x⟩
  obtain ⟨S, hS, U, hU, hUt, hp, χ, hχ, hcχ, hχU, hnear⟩ :=
    twoForm_regularity_cutoff o x z₀
  let K := tsupport χ
  have hKt : K ⊆ (chartAt FourSpace x).target := hχU.trans hUt
  obtain ⟨V, hVKχ, hV, hzV⟩ := _root_.mem_nhds_iff.mp hnear
  have hVK : V ⊆ K := fun z hz => (hVKχ hz).1
  obtain ⟨η, hη, hcη, hηK, W, hW, hzW, hWV, hone, F, hF, heF⟩ :=
    twoFormPoisson_smooth_coefficients x S hS hcχ hKt hV hVK U hU hUt hχU hp u f hu z₀ hzV
  let B : FourSpace → TwoFormFour := fun z => WithLp.toLp 2 (fun r => F r z)
  have hB : ContDiff ℝ ∞ B := (contDiff_piLp (p := 2)).mpr hF
  have hrep : twoFormGramVectorL2 x S hcχ hKt η hη hcη hηK u =ᵐ[volume] B :=
    twoFormAssembleL2_coe _ u B heF
  obtain ⟨Z, v, hZ, hzZ, hZW, he⟩ := twoForm_smooth_local_representative x S hS hcχ hKt
    η hη hcη hηK hW (hWV.trans hVK) hone u B hB hrep z₀ hzW
  let O := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' Z
  refine ⟨O, v, (chartAt FourSpace x).isOpen_inter_preimage hZ,
    ⟨mem_chart_source FourSpace x, hzZ⟩, ?_⟩
  intro w hw
  have hws : tsupport w.val ⊆ (chartAt FourSpace x).symm '' Z := by
    intro y hy
    exact ⟨chartAt FourSpace x y, (hw hy).2, (chartAt FourSpace x).left_inv (hw hy).1⟩
  obtain ⟨a, ha, has, haw⟩ := twoForm_supported_gramTest x S hS hcχ hKt
    (hZW.trans (hWV.trans hVK)) w hws
  have he' := he a ha has
  have hl : smoothTwoFormToL2 (twoFormGramTest o x S a ha hcχ hKt
      (has.trans (hZW.trans (hWV.trans hVK)))) = smoothTwoFormToL2 (w : SmoothL2TwoForm o) :=
    congrArg (fun t : smoothTwoForms o => smoothTwoFormToL2 (t : SmoothL2TwoForm o)) haw
  exact (congrArg (fun t : TwoFormL2 o => inner ℝ (twoFormH1ToL2 u) t) hl).symm.trans
    (he'.trans (congrArg (fun t : TwoFormL2 o =>
      inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) t) hl))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual weak harmonic two-forms have smooth global representatives.
A finite partition of unity assembles the local test-pairing identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHarmonic_smooth_representative (u : TwoFormH1 o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u))) :
    ∃ v : smoothTwoForms o, twoFormH1ToL2 u = smoothTwoFormToL2 (v : SmoothL2TwoForm o) := by
  choose O v hO hx he using twoFormHarmonic_local_smooth u hu
  have hcover : (univ : Set M) ⊆ ⋃ x : M, O x := by
    intro x _
    exact mem_iUnion_of_mem x (hx x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  let ι := {x : M // x ∈ s}
  let : Fintype ι := Finset.Subtype.fintype s
  have hfinite : (univ : Set M) ⊆ ⋃ i : ι, O i.val := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨y, hy⟩ hxy
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := I4) (s := (univ : Set M)) isClosed_univ (fun i : ι => O i.val)
      (fun i => hO i.val) hfinite
  let R : ι → SmoothScalar (M := M) := fun i => ⟨ρ i, (ρ i).contMDiff⟩
  have hR (x : M) : ∑ i : ι, (R i).val x = 1 := by
    simpa only [R, finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  let V : smoothTwoForms o := ∑ i : ι, smoothTwoFormProduct (R i) (v i.val)
  refine ⟨V, twoFormL2_eq_of_smooth_pairings _ _ ?_⟩
  intro w
  have hpart := smoothTwoForm_partition_weights R hR (w : smoothTwoForms o)
  have hsum : smoothTwoFormToL2 w = ∑ i : ι,
      smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o) := by
    have heq := congrArg (fun a : smoothTwoForms o => smoothTwoFormToL2 (a : SmoothL2TwoForm o)) hpart
    exact heq.symm.trans (map_sum smoothTwoFormToL2 _ _)
  calc
    inner ℝ (twoFormH1ToL2 u) (smoothTwoFormToL2 w) =
        ∑ i : ι, inner ℝ (twoFormH1ToL2 u)
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      rw [hsum, inner_sum]
    _ = ∑ i : ι, inner ℝ (smoothTwoFormToL2 (v i.val : SmoothL2TwoForm o))
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply he i.val
      exact (tsupport_smul_subset_left (R i).val (w : smoothTwoForms o).val).trans (hρ i)
    _ = ∑ i : ι, inner ℝ
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (v i.val) : SmoothL2TwoForm o))
          (smoothTwoFormToL2 w) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (smoothTwoForm_product_inner (R i) (v i.val) (w : smoothTwoForms o)).symm
    _ = inner ℝ (smoothTwoFormToL2 (V : SmoothL2TwoForm o)) (smoothTwoFormToL2 w) := by
      rw [← sum_inner]
      congr 1
      exact (map_sum smoothTwoFormToL2 _ _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every positive-time Hodge heat output agrees locally, in all smooth
test pairings, with a constructed smooth global section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_local_smooth (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (input : TwoFormL2 o) (x : M) :
    ∃ (O : Set M) (v : smoothTwoForms o), IsOpen O ∧ x ∈ O ∧
      ∀ w : smoothTwoForms o, tsupport w.val ⊆ O →
        inner ℝ (twoFormH1ToL2 (twoFormHeatLift hRic t ht input)) (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) =
          inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o))
            (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) := by
  let z₀ : ChartTarget x := ⟨chartAt FourSpace x x, mem_chart_target FourSpace x⟩
  obtain ⟨S, hS, U, hU, hUt, hp, χ, hχ, hcχ, hχU, hnear⟩ :=
    twoForm_regularity_cutoff o x z₀
  let K := tsupport χ
  have hKt : K ⊆ (chartAt FourSpace x).target := hχU.trans hUt
  obtain ⟨V, hVKχ, hV, hzV⟩ := _root_.mem_nhds_iff.mp hnear
  have hVK : V ⊆ K := fun z hz => (hVKχ hz).1
  obtain ⟨η, hη, hcη, hηK, W, hW, hzW, hWV, hone, F, hF, heF⟩ :=
    twoFormHeat_smooth_coefficients x S hS hcχ hKt hV hVK U hU hUt hχU hp hRic t ht input z₀ hzV
  let B : FourSpace → TwoFormFour := fun z => WithLp.toLp 2 (fun r => F r z)
  have hB : ContDiff ℝ ∞ B := (contDiff_piLp (p := 2)).mpr hF
  have hrep : twoFormGramVectorL2 x S hcχ hKt η hη hcη hηK (twoFormHeatLift hRic t ht input) =ᵐ[volume] B :=
    twoFormAssembleL2_coe _ (twoFormHeatLift hRic t ht input) B heF
  obtain ⟨Z, v, hZ, hzZ, hZW, he⟩ := twoForm_smooth_local_representative x S hS hcχ hKt
    η hη hcη hηK hW (hWV.trans hVK) hone (twoFormHeatLift hRic t ht input) B hB hrep z₀ hzW
  let O := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' Z
  refine ⟨O, v, (chartAt FourSpace x).isOpen_inter_preimage hZ,
    ⟨mem_chart_source FourSpace x, hzZ⟩, ?_⟩
  intro w hw
  have hws : tsupport w.val ⊆ (chartAt FourSpace x).symm '' Z := by
    intro y hy
    exact ⟨chartAt FourSpace x y, (hw hy).2, (chartAt FourSpace x).left_inv (hw hy).1⟩
  obtain ⟨a, ha, has, haw⟩ := twoForm_supported_gramTest x S hS hcχ hKt
    (hZW.trans (hWV.trans hVK)) w hws
  have he' := he a ha has
  have hl : smoothTwoFormToL2 (twoFormGramTest o x S a ha hcχ hKt
      (has.trans (hZW.trans (hWV.trans hVK)))) = smoothTwoFormToL2 (w : SmoothL2TwoForm o) :=
    congrArg (fun t : smoothTwoForms o => smoothTwoFormToL2 (t : SmoothL2TwoForm o)) haw
  exact (congrArg (fun z : TwoFormL2 o => inner ℝ (twoFormH1ToL2 (twoFormHeatLift hRic t ht input)) z) hl).symm.trans
    (he'.trans (congrArg (fun t : TwoFormL2 o =>
      inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) t) hl))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual weak smooth-source Hodge-Poisson two-forms have smooth global representatives.
A finite partition of unity assembles the local test-pairing identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormPoisson_smooth_representative (u : TwoFormH1 o) (f : smoothTwoForms o)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o))) :
    ∃ v : smoothTwoForms o, twoFormH1ToL2 u = smoothTwoFormToL2 (v : SmoothL2TwoForm o) := by
  choose O v hO hx he using twoFormPoisson_local_smooth u f hu
  have hcover : (univ : Set M) ⊆ ⋃ x : M, O x := by
    intro x _
    exact mem_iUnion_of_mem x (hx x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  let ι := {x : M // x ∈ s}
  let : Fintype ι := Finset.Subtype.fintype s
  have hfinite : (univ : Set M) ⊆ ⋃ i : ι, O i.val := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨y, hy⟩ hxy
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := I4) (s := (univ : Set M)) isClosed_univ (fun i : ι => O i.val)
      (fun i => hO i.val) hfinite
  let R : ι → SmoothScalar (M := M) := fun i => ⟨ρ i, (ρ i).contMDiff⟩
  have hR (x : M) : ∑ i : ι, (R i).val x = 1 := by
    simpa only [R, finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  let V : smoothTwoForms o := ∑ i : ι, smoothTwoFormProduct (R i) (v i.val)
  refine ⟨V, twoFormL2_eq_of_smooth_pairings _ _ ?_⟩
  intro w
  have hpart := smoothTwoForm_partition_weights R hR (w : smoothTwoForms o)
  have hsum : smoothTwoFormToL2 w = ∑ i : ι,
      smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o) := by
    have heq := congrArg (fun a : smoothTwoForms o => smoothTwoFormToL2 (a : SmoothL2TwoForm o)) hpart
    exact heq.symm.trans (map_sum smoothTwoFormToL2 _ _)
  calc
    inner ℝ (twoFormH1ToL2 u) (smoothTwoFormToL2 w) =
        ∑ i : ι, inner ℝ (twoFormH1ToL2 u)
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      rw [hsum, inner_sum]
    _ = ∑ i : ι, inner ℝ (smoothTwoFormToL2 (v i.val : SmoothL2TwoForm o))
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply he i.val
      exact (tsupport_smul_subset_left (R i).val (w : smoothTwoForms o).val).trans (hρ i)
    _ = ∑ i : ι, inner ℝ
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (v i.val) : SmoothL2TwoForm o))
          (smoothTwoFormToL2 w) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (smoothTwoForm_product_inner (R i) (v i.val) (w : smoothTwoForms o)).symm
    _ = inner ℝ (smoothTwoFormToL2 (V : SmoothL2TwoForm o)) (smoothTwoFormToL2 w) := by
      rw [← sum_inner]
      congr 1
      exact (map_sum smoothTwoFormToL2 _ _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak harmonic kernel and the smooth closed and coclosed
two-forms coincide. The equivalence uses proved elliptic regularity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHarmonic_smooth_H1 (hRic : RicciThree g) (u : TwoFormH1 o)
    (hu : u ∈ twoFormWeitzenbockKernel (o := o)) :
    ∃ v : smoothTwoForms o, v ∈ smoothHarmonicTwoForms ∧
      u = smoothTwoFormToH1 (v : SmoothH1TwoForm o) := by
  obtain ⟨v, hv⟩ := twoFormHarmonic_smooth_representative u (twoFormWeakHarmonic_rough u hu)
  have he : u = smoothTwoFormToH1 (v : SmoothH1TwoForm o) :=
    twoFormH1ToL2_injective hRic (hv.trans (twoFormH1ToL2_smooth (v : SmoothH1TwoForm o)).symm)
  have hk : smoothTwoFormToH1 (v : SmoothH1TwoForm o) ∈ twoFormWeitzenbockKernel (o := o) :=
    he ▸ hu
  have hE := (mem_twoFormWeitzenbockKernel_iff_energy_zero hRic _).mp hk
  have henergy : smoothTwoFormDeRhamEnergy v = 0 :=
    (twoFormHodgeForm_smooth hRic (v : SmoothH1TwoForm o)).symm.trans hE
  exact ⟨v, (smoothTwoFormDeRhamEnergy_eq_zero_iff v).mp henergy, he⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time Hodge heat outputs have smooth global representatives.
A finite partition of unity assembles the local test-pairing identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_smooth_representative (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (input : TwoFormL2 o) :
    ∃ v : smoothTwoForms o, twoFormH1ToL2 (twoFormHeatLift hRic t ht input) = smoothTwoFormToL2 (v : SmoothL2TwoForm o) := by
  choose O v hO hx he using twoFormHeat_local_smooth hRic t ht input
  have hcover : (univ : Set M) ⊆ ⋃ x : M, O x := by
    intro x _
    exact mem_iUnion_of_mem x (hx x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  let ι := {x : M // x ∈ s}
  let : Fintype ι := Finset.Subtype.fintype s
  have hfinite : (univ : Set M) ⊆ ⋃ i : ι, O i.val := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨y, hy⟩ hxy
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := I4) (s := (univ : Set M)) isClosed_univ (fun i : ι => O i.val)
      (fun i => hO i.val) hfinite
  let R : ι → SmoothScalar (M := M) := fun i => ⟨ρ i, (ρ i).contMDiff⟩
  have hR (x : M) : ∑ i : ι, (R i).val x = 1 := by
    simpa only [R, finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  let V : smoothTwoForms o := ∑ i : ι, smoothTwoFormProduct (R i) (v i.val)
  refine ⟨V, twoFormL2_eq_of_smooth_pairings _ _ ?_⟩
  intro w
  have hpart := smoothTwoForm_partition_weights R hR (w : smoothTwoForms o)
  have hsum : smoothTwoFormToL2 w = ∑ i : ι,
      smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o) := by
    have heq := congrArg (fun a : smoothTwoForms o => smoothTwoFormToL2 (a : SmoothL2TwoForm o)) hpart
    exact heq.symm.trans (map_sum smoothTwoFormToL2 _ _)
  calc
    inner ℝ (twoFormH1ToL2 (twoFormHeatLift hRic t ht input)) (smoothTwoFormToL2 w) =
        ∑ i : ι, inner ℝ (twoFormH1ToL2 (twoFormHeatLift hRic t ht input))
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      rw [hsum, inner_sum]
    _ = ∑ i : ι, inner ℝ (smoothTwoFormToL2 (v i.val : SmoothL2TwoForm o))
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply he i.val
      exact (tsupport_smul_subset_left (R i).val (w : smoothTwoForms o).val).trans (hρ i)
    _ = ∑ i : ι, inner ℝ
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (v i.val) : SmoothL2TwoForm o))
          (smoothTwoFormToL2 w) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (smoothTwoForm_product_inner (R i) (v i.val) (w : smoothTwoForms o)).symm
    _ = inner ℝ (smoothTwoFormToL2 (V : SmoothL2TwoForm o)) (smoothTwoFormToL2 w) := by
      rw [← sum_inner]
      congr 1
      exact (map_sum smoothTwoFormToL2 _ _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth Hodge-Poisson solvability for an actual smooth source
orthogonal to the smooth harmonic space. Both weak solvability and
regularity are proved, with no extra analytic premise. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_smoothHodgePoisson (hRic : RicciThree g) (f : smoothTwoForms o)
    (hf : ∀ h ∈ smoothHarmonicTwoForms (o := o), smoothTwoFormL2Inner f h = 0) :
    ∃ u : smoothTwoForms o, ∀ v : TwoFormH1 o,
      twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) v =
        inner ℝ (smoothTwoFormToL2 (f : SmoothL2TwoForm o)) (twoFormH1ToL2 v) := by
  have hfweak : ∀ v ∈ twoFormWeitzenbockKernel (o := o),
      inner ℝ (smoothTwoFormToL2 (f : SmoothL2TwoForm o)) (twoFormH1ToL2 v) = 0 := by
    intro v hv
    obtain ⟨h, hh, he⟩ := twoFormHarmonic_smooth_H1 hRic v hv
    have hJ : twoFormH1ToL2 v = smoothTwoFormToL2 (h : SmoothL2TwoForm o) :=
      (congrArg twoFormH1ToL2 he).trans (twoFormH1ToL2_smooth (h : SmoothH1TwoForm o))
    exact (congrArg (fun t : TwoFormL2 o =>
      inner ℝ (smoothTwoFormToL2 (f : SmoothL2TwoForm o)) t) hJ).trans
        ((smoothTwoFormToL2.inner_map_map _ _).trans (hf h hh))
  obtain ⟨u, _, hu⟩ := exists_weakHodgePoisson hRic
    (smoothTwoFormToL2 (f : SmoothL2TwoForm o)) hfweak
  have hrough : u = twoFormRoughSolution
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (f : SmoothL2TwoForm o)) := by
    have h := (twoFormHodgeEquation_rough_iff u (smoothTwoFormToL2 (f : SmoothL2TwoForm o))).mp hu
    simpa only [add_comm] using h
  obtain ⟨v, hv⟩ := twoFormPoisson_smooth_representative u f hrough
  have he : u = smoothTwoFormToH1 (v : SmoothH1TwoForm o) :=
    twoFormH1ToL2_injective hRic (hv.trans (twoFormH1ToL2_smooth (v : SmoothH1TwoForm o)).symm)
  refine ⟨v, ?_⟩
  intro w
  exact (congrArg (fun a : TwoFormH1 o => twoFormHodgeForm a w) he).symm.trans (hu w)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Pointwise Hodge-Poisson solvability and the kernel of the actual
smooth Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_smoothHodgePoisson_pointwise (hRic : RicciThree g)
    (f : smoothTwoForms o)
    (hf : ∀ h ∈ smoothHarmonicTwoForms (o := o), smoothTwoFormL2Inner f h = 0) :
    ∃ u : smoothTwoForms o, smoothHodgeLaplacian hRic u = f := by
  obtain ⟨u, hu⟩ := exists_smoothHodgePoisson hRic f hf
  refine ⟨u, smoothTwoForm_eq_of_pairings _ _ (fun v => ?_)⟩
  have hj : twoFormH1ToL2 (smoothTwoFormToH1 (v : SmoothH1TwoForm o)) =
      smoothTwoFormToL2 (v : SmoothL2TwoForm o) :=
    twoFormH1ToL2_smooth (v : SmoothH1TwoForm o)
  exact (smoothHodgeLaplacian_pairing hRic u v).trans ((hu _).trans
    ((congrArg (fun t : TwoFormL2 o =>
      inner ℝ (smoothTwoFormToL2 (f : SmoothL2TwoForm o)) t) hj).trans
        (smoothTwoFormToL2.inner_map_map _ _)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth Hodge eigenforms are total in the two-form H1 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigenform_L2 (hRic : RicciThree g) (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormEigenvector hRic i = smoothTwoFormToL2 (twoFormEigenform hRic i : SmoothL2TwoForm o) :=
  (twoFormEigenvector_smooth hRic i).choose_spec.1

theorem twoFormEigenform_laplacian (hRic : RicciThree g) (i : TwoFormEigenIndex (o := o) hRic) :
    smoothHodgeLaplacian hRic (twoFormEigenform hRic i) =
      (i.1.val⁻¹ - 1) • twoFormEigenform hRic i :=
  (twoFormEigenvector_smooth hRic i).choose_spec.2

theorem twoFormShiftedSolution_eigen_smooth (hRic : RicciThree g)
    (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormShiftedSolution hRic (twoFormEigenvector hRic i) =
      i.1.val • smoothTwoFormToH1 (twoFormEigenform hRic i : SmoothH1TwoForm o) := by
  apply twoFormH1ToL2_injective hRic
  have hJ := twoFormH1ToL2_smooth (twoFormEigenform hRic i : SmoothH1TwoForm o)
  calc
    _ = i.1.val • twoFormEigenvector hRic i :=
      Module.End.mem_eigenspace_iff.mp (twoFormEigenvector_hasEigenvector hRic i).1
    _ = i.1.val • twoFormH1ToL2
        (smoothTwoFormToH1 (twoFormEigenform hRic i : SmoothH1TwoForm o)) :=
      congrArg (i.1.val • ·) ((twoFormEigenform_L2 hRic i).trans hJ.symm)
    _ = _ := (twoFormH1ToL2.map_smul i.1.val
      (smoothTwoFormToH1 (twoFormEigenform hRic i : SmoothH1TwoForm o))).symm

theorem twoFormH1_eigenforms_total (hRic : RicciThree g) :
    (Submodule.span ℝ (range (fun i : TwoFormEigenIndex (o := o) hRic =>
      smoothTwoFormToH1 (twoFormEigenform hRic i : SmoothH1TwoForm o)))).topologicalClosure = ⊤ := by
  have he := dense_span_continuousLinearMap_image (twoFormEigenvector (o := o) hRic)
    (by rw [twoFormEigenvector_span, twoFormSpectral_total hRic])
    (twoFormShiftedSolution hRic) (twoFormShiftedSolution_dense hRic)
  have hs : Submodule.span ℝ (range (fun i =>
      twoFormShiftedSolution hRic (twoFormEigenvector hRic i))) ≤
      Submodule.span ℝ (range (fun i : TwoFormEigenIndex (o := o) hRic =>
        smoothTwoFormToH1 (twoFormEigenform hRic i : SmoothH1TwoForm o))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change twoFormShiftedSolution hRic (twoFormEigenvector hRic i) ∈ _
    rw [twoFormShiftedSolution_eigen_smooth]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  apply top_unique
  rw [← he]
  exact Submodule.topologicalClosure_mono hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual local heat operators have compact support and square-summable
images of the orthonormal eigenbasis. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap NNReal BoundedContinuousFunction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
  (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
  {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
  (hs : tsupport a ⊆ V) (r : Fin 6)

theorem twoFormHeatChartContinuous_smooth (input : TwoFormL2 o) (w : smoothTwoForms o)
    (hw : twoFormH1ToL2 (twoFormHeatLift hRic t ht input) = smoothTwoFormToL2 (w : SmoothL2TwoForm o))
    (z : FourSpace) :
    twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r input z =
      (a z * twoFormChartValue o w.val c S hS z r : ℂ) := by
  have hu : twoFormHeatLift hRic t ht input = smoothTwoFormToH1 (w : SmoothH1TwoForm o) :=
    twoFormH1ToL2_injective hRic (hw.trans (twoFormH1ToL2_smooth _).symm)
  let q := twoFormGramCutoffC1 c S hKt a ha hc (hs.trans hVK) (twoFormComponentIndex r)
    (w : SmoothH1TwoForm o)
  have hA : (twoFormHeatChartL2 hRic t ht c S hK hKt hVK a ha hc hs r input : FourSpace → ℂ) =ᵐ[volume]
      fun x => (q.val x : ℂ) := by
    have heq : twoFormHeatChartL2 hRic t ht c S hK hKt hVK a ha hc hs r input =
        scalarComplexL2 (ScalarEuclideanSobolev.valueL2 q) :=
      congrArg scalarComplexL2 ((congrArg (twoFormGramValueL2 c S hK hKt a ha hc
        (hs.trans hVK) (twoFormComponentIndex r)) hu).trans
          (twoFormGramValueL2_smooth c S hK hKt a ha hc (hs.trans hVK)
            (twoFormComponentIndex r) (w : SmoothH1TwoForm o)))
    rw [heq]
    filter_upwards [scalarComplexL2_coe (ScalarEuclideanSobolev.valueL2 q),
      ScalarEuclideanSobolev.valueL2_coe q] with x hC hq
    exact hC.trans (congrArg Complex.ofReal hq)
  have he : (twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r input :
      FourSpace → ℂ) = fun x => (q.val x : ℂ) := by
    apply MeasureTheory.Measure.eq_of_ae_eq
      ((twoFormHeatChartContinuous_ae hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r input).symm.trans hA)
    · exact (twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r input).continuous
    · exact Complex.continuous_ofReal.comp q.property.1.continuous
  rw [congrFun he z]
  rw [← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  exact (twoFormGramCutoffC1_value c S hS hKt a ha hc (hs.trans hVK)
    (twoFormComponentIndex r) (w : SmoothH1TwoForm o) z).trans
      (congrArg (a z * ·) (twoFormTensor_component _ r))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual smooth sections representing positive-time heat output. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHeatSection (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (f : TwoFormL2 o) :
    smoothTwoForms o := (twoFormHeat_smooth_representative hRic t ht f).choose

theorem twoFormHeatSection_H1 (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (f : TwoFormL2 o) :
    twoFormH1ToL2 (twoFormHeatLift hRic t ht f) =
      smoothTwoFormToL2 (twoFormHeatSection hRic t ht f : SmoothL2TwoForm o) :=
  (twoFormHeat_smooth_representative hRic t ht f).choose_spec

theorem twoFormHeatSection_L2 (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (f : TwoFormL2 o) :
    smoothTwoFormToL2 (twoFormHeatSection hRic t ht f : SmoothL2TwoForm o) =
      twoFormHeat hRic t f :=
  (twoFormHeatSection_H1 hRic t ht f).symm.trans (twoFormHeatLift_value hRic t ht f)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual coclosed one-forms are codifferentials of smooth two-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothHodgeLaplacian_eq_dDelta_of_closed (hRic : RicciThree g)
    (u : smoothTwoForms o) (hu : smoothTwoFormExterior (smoothHodgeLaplacian hRic u) = 0) :
    smoothHodgeLaplacian hRic u = smoothTwoFormDDelta u := by
  let b := smoothTwoFormCodifferentialField (smoothTwoFormHodge o u)
  let w := smoothTwoFormHodge o (smoothOneFormExterior b)
  have he : smoothHodgeLaplacian hRic u = smoothTwoFormDDelta u + w :=
    smoothHodgeLaplacian_dDelta_hodge hRic u
  have hf := smoothOneForm_coexact_orthogonal_closed hRic b _ hu
  have ha := smoothOneForm_coexact_orthogonal_closed hRic b (smoothTwoFormDDelta u)
    (smoothTwoFormDDelta_closed hRic u)
  change smoothTwoFormL2Inner w (smoothHodgeLaplacian hRic u) = 0 at hf
  change smoothTwoFormL2Inner w (smoothTwoFormDDelta u) = 0 at ha
  rw [he, smoothTwoFormL2Inner_add_right, ha, zero_add] at hf
  have hw : w = 0 := smoothTwoFormL2Inner_definite w hf
  rwa [hw, add_zero] at he

theorem exists_smoothCoexact_of_divergence_eq_zero (hRic : RicciThree g)
    (v : smoothCovariantFields M 1) (hv : smoothOneFormDivergence g v = 0) :
    ∃ u : smoothTwoForms o, v = smoothTwoFormCodifferentialField u := by
  obtain ⟨u, hu⟩ := exists_smoothHodgePoisson_pointwise hRic
    (smoothOneFormExterior (o := o) v)
    (fun h hh => smoothHarmonic_orthogonal_exact hRic v h hh)
  have hclosed : smoothTwoFormExterior (smoothHodgeLaplacian hRic u) = 0 := by
    rw [hu]
    exact smoothOneFormExterior_closed hRic v
  have hd : smoothOneFormExterior (smoothTwoFormCodifferentialField u) =
      smoothOneFormExterior (o := o) v :=
    (smoothHodgeLaplacian_eq_dDelta_of_closed hRic u hclosed).symm.trans hu
  let w := v - smoothTwoFormCodifferentialField u
  have hwd : smoothOneFormExterior (o := o) w = 0 := by
    change smoothOneFormExteriorLinear (v - smoothTwoFormCodifferentialField u) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hd.symm
  have hwdiv : smoothOneFormDivergence g w = 0 := by
    change smoothOneFormDivergence g (v - smoothTwoFormCodifferentialField u) = 0
    rw [map_sub, hv, smoothTwoFormCodifferential_divergence hRic, sub_self]
  have hwt (e : FrameBundle g) :
      (∑ i, covariantFieldFramed g (covariantFieldDerivative g w.val) e ![i,i]) = 0 := by
    rw [← oneFormDivergence_eq_frame]
    exact congrArg (fun f : SmoothScalar (M := M) => f.val e.base) hwdiv
  have hw : w = 0 := oneForm_harmonic_eq_zero hRic w hwd hwt
  exact ⟨u, sub_eq_zero.mp hw⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual local heat operators have compact support and square-summable
images of the orthonormal eigenbasis. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap NNReal BoundedContinuousFunction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
  (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
  {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
  (hs : tsupport a ⊆ V)

theorem twoFormHeat_local_diagonal (s : Finset (TwoFormEigenIndex (o := o) hRic))
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (ha1 : a z = 1) :
    (∑ i ∈ s, ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val
      ((chartAt FourSpace c).symm z)‖ ^ 2) ≤
      ∑ r : Fin 6, 2 * ‖twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r‖ ^ 2 := by
  let A := fun r : Fin 6 =>
    twoFormHeatChartContinuous hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp a ha hc hs r
  have he (i : TwoFormEigenIndex (o := o) hRic) (r : Fin 6) :
      ‖A r (twoFormEigenvector hRic i) z‖ =
        ‖twoFormChartValue o (twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val c S hS z r‖ := by
    rw [show A r (twoFormEigenvector hRic i) z = _ from
      twoFormHeatChartContinuous_smooth hRic t ht c S hS hK hKt hV hVK U hU hUt hKU hp
        a ha hc hs r _ _ (twoFormHeatSection_H1 hRic t ht _) z]
    rw [ha1, Complex.ofReal_one, one_mul, Complex.norm_real]
  calc
    _ = ∑ i ∈ s, ∑ r : Fin 6, ‖A r (twoFormEigenvector hRic i) z‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← twoFormChartValue_norm o _ c S hS z hz, EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl (fun r _ => congrArg (fun x : ℝ => x ^ 2) (he i r).symm)
    _ = ∑ r : Fin 6, ∑ i ∈ s, ‖A r (twoFormEigenvector hRic i) z‖ ^ 2 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun r _ =>
      scalarBoundedOperator_bessel (twoFormEigenvector_orthonormal hRic) (A r) s z)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every smooth one-form has its actual exact plus coexact decomposition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_smoothOneForm_Hodge_decomposition (hRic : RicciThree g)
    (v : smoothCovariantFields M 1) :
    ∃ f : SmoothScalar (M := M), ∃ u : smoothTwoForms o,
      v = smoothScalarDifferential g f + smoothTwoFormCodifferentialField u := by
  obtain ⟨f, hf, hlap⟩ := actual_petersen_poisson g o hRic
    (oneFormDivergence g v) (oneFormDivergence_smooth v)
  let F : SmoothScalar (M := M) := ⟨f, hf⟩
  let w := v - smoothScalarDifferential g F
  have hw : smoothOneFormDivergence g w = 0 := by
    apply Subtype.ext
    funext x
    let e := frameAt g x
    have hb : e.base = x := rfl
    have he := hlap e
    rw [oneFormDivergence_mean_zero (o := o) hRic v, sub_zero] at he
    have hd := congrArg (fun a : SmoothScalar (M := M) => a.val x)
      (map_sub (smoothOneFormDivergence g) v (smoothScalarDifferential g F))
    change oneFormDivergence g w x =
      oneFormDivergence g v x - oneFormDivergence g (smoothScalarDifferential g F) x at hd
    change oneFormDivergence g w x = 0
    rw [hd, ← hb, oneFormDivergence_differential]
    exact sub_eq_zero.mpr he.symm
  obtain ⟨u, hu⟩ := exists_smoothCoexact_of_divergence_eq_zero (o := o) hRic w hw
  refine ⟨F, u, ?_⟩
  have h := sub_eq_iff_eq_add.mp hu
  exact h.trans (add_comm _ _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A finite chart cover gives a uniform diagonal bound for the actual
positive-time two-form heat operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric
open scoped BigOperators Manifold ContDiff NNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_local_diagonal_bound (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (x : M) :
    ∃ (O : Set M) (C : ℝ), IsOpen O ∧ x ∈ O ∧ 0 ≤ C ∧
      ∀ (s : Finset (TwoFormEigenIndex (o := o) hRic)) (y : M), y ∈ O →
        (∑ i ∈ s, ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val y‖ ^ 2) ≤ C := by
  let z₀ : ChartTarget x := ⟨chartAt FourSpace x x, mem_chart_target FourSpace x⟩
  obtain ⟨S, hS, U, hU, hUt, hp, χ, hχ, hcχ, hχU, hnear⟩ :=
    twoForm_regularity_cutoff o x z₀
  let K := tsupport χ
  have hKt : K ⊆ (chartAt FourSpace x).target := hχU.trans hUt
  obtain ⟨V, hVKχ, hV, hzV⟩ := _root_.mem_nhds_iff.mp hnear
  have hVK : V ⊆ K := fun z hz => (hVKχ hz).1
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let a : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have haV : tsupport (a : FourSpace → ℝ) ⊆ V := by rw [a.tsupport_eq]; exact hdV
  let A := fun r : Fin 6 => twoFormHeatChartContinuous hRic t ht x S hS hcχ hKt
    hV hVK U hU hUt hχU hp a a.contDiff a.hasCompactSupport haV r
  let C := ∑ r : Fin 6, 2 * ‖A r‖ ^ 2
  let O := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' ball z₀.val (d / 2)
  refine ⟨O, C, (chartAt FourSpace x).isOpen_inter_preimage isOpen_ball,
    ⟨mem_chart_source FourSpace x, mem_ball_self (half_pos hd)⟩,
    Finset.sum_nonneg (fun r _ => mul_nonneg (by norm_num) (sq_nonneg _)), ?_⟩
  intro s y hy
  have hz : chartAt FourSpace x y ∈ (chartAt FourSpace x).target :=
    (chartAt FourSpace x).mapsTo hy.1
  have hone : a (chartAt FourSpace x y) = 1 := a.one_of_mem_closedBall (ball_subset_closedBall hy.2)
  have h := twoFormHeat_local_diagonal hRic t ht x S hS hcχ hKt hV hVK U hU hUt hχU hp
    a a.contDiff a.hasCompactSupport haV s (chartAt FourSpace x y) hz hone
  rw [(chartAt FourSpace x).left_inv hy.1] at h
  exact h

theorem twoFormHeat_diagonal_bound (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset (TwoFormEigenIndex (o := o) hRic)) (y : M),
      (∑ i ∈ s, ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val y‖ ^ 2) ≤ C := by
  classical
  choose O C hO hx hC hb using twoFormHeat_local_diagonal_bound (o := o) hRic t ht
  have hcover : (univ : Set M) ⊆ ⋃ x : M, O x := by
    intro x _
    exact mem_iUnion_of_mem x (hx x)
  obtain ⟨q, hq⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  refine ⟨∑ x ∈ q, C x, Finset.sum_nonneg (fun x _ => hC x), ?_⟩
  intro s y
  obtain ⟨x, hxq, hy⟩ := mem_iUnion₂.mp (hq (mem_univ y))
  exact (hb x s y hy).trans (Finset.single_le_sum (fun z _ => hC z) hxq)

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_14
theorem oneFormDerivedFamily_total (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    (Submodule.span ℝ (range (oneFormDerivedFamily hRic d))).topologicalClosure = ⊤ := by
  let S := (Submodule.span ℝ (range (oneFormDerivedFamily hRic d))).topologicalClosure
  have hS : IsClosed (S : Set (OneFormL2 o)) := Submodule.isClosed_topologicalClosure _
  have hD (u : scalarH1 d) : scalarH1Differential d u ∈ S := by
    apply continuousLinearMap_mem_closed_of_total _ (scalarH1_eigenfunctions_total g o d)
      (scalarH1Differential d) S hS _ u
    intro i
    rw [scalarH1Differential_smooth]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
  have hδ (u : TwoFormH1 o) : twoFormH1Codifferential hRic u ∈ S := by
    apply continuousLinearMap_mem_closed_of_total _ (twoFormH1_eigenforms_total hRic)
      (twoFormH1Codifferential hRic) S hS _ u
    intro i
    exact (congrArg (fun z : OneFormL2 o => z ∈ S)
      (twoFormH1Codifferential_smooth hRic
        (twoFormEigenform hRic i : SmoothH1TwoForm o))).mpr
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
  have hsmooth (u : SmoothL2OneForm o) : smoothOneFormToL2 u ∈ S := by
    obtain ⟨a, b, hab⟩ := exists_smoothOneForm_Hodge_decomposition (o := o) hRic u.toSmooth
    have he : u = (⟨smoothScalarDifferential g a⟩ : SmoothL2OneForm o) +
        ⟨smoothTwoFormCodifferentialField b⟩ := by
      apply (smoothL2OneFormEquiv o).injective
      exact hab
    rw [he, map_add]
    have ha := hD (smoothScalarToH1 d a)
    have hb := hδ (smoothTwoFormToH1 (b : SmoothH1TwoForm o))
    rw [scalarH1Differential_smooth] at ha
    have hb' := (congrArg (fun z : OneFormL2 o => z ∈ S)
      (twoFormH1Codifferential_smooth hRic (b : SmoothH1TwoForm o))).mp hb
    exact S.add_mem ha hb'
  apply top_unique
  intro u _
  apply hS.closure_subset_iff.mpr (show range (smoothOneFormToL2 (o := o)) ⊆ S from ?_)
    (smoothOneFormToL2_dense u)
  rintro _ ⟨v, rfl⟩
  exact hsmooth v

end
end PositiveEinsteinFour.Geometry
end


section

/-! Summability of the actual positive-time Hodge heat eigenvalues.
The proof integrates the geometric diagonal bound against normalized volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatSection_eigen_integral (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (i : TwoFormEigenIndex (o := o) hRic) :
    (∫ x, ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val x‖ ^ 2
      ∂normalizedVolume g) = twoFormHeatWeight hRic t i.1 ^ 2 := by
  calc
    _ = ‖smoothTwoFormToL2
        (twoFormHeatSection hRic t ht (twoFormEigenvector hRic i) : SmoothL2TwoForm o)‖ ^ 2 :=
      (smoothTwoFormToL2_norm_sq _).symm
    _ = ‖twoFormHeat hRic t (twoFormEigenvector hRic i)‖ ^ 2 :=
      congrArg (fun f : TwoFormL2 o => ‖f‖ ^ 2) (twoFormHeatSection_L2 hRic t ht _)
    _ = _ := by
      rw [twoFormHeat_eigenvector, norm_smul, Real.norm_eq_abs,
        (twoFormEigenvector_orthonormal hRic).1 i, mul_one, sq_abs]

theorem twoFormHeat_weight_square_summable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i : TwoFormEigenIndex (o := o) hRic => twoFormHeatWeight hRic t i.1 ^ 2) := by
  have := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  obtain ⟨C, _, hC⟩ := twoFormHeat_diagonal_bound (o := o) hRic t ht
  apply summable_of_sum_le (fun _ => sq_nonneg _) (c := C)
  intro s
  have hi (i : TwoFormEigenIndex (o := o) hRic) : Integrable
      (fun x => ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val x‖ ^ 2)
      (normalizedVolume g) :=
    ((smoothTwoForm_norm_continuous _).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ x, ∑ i ∈ s, ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val x‖ ^ 2
        ∂normalizedVolume g := by
      rw [integral_finsetSum s (fun i _ => hi i)]
      exact Finset.sum_congr rfl (fun i _ => (twoFormHeatSection_eigen_integral hRic t ht i).symm)
    _ ≤ ∫ _x, C ∂normalizedVolume g := integral_mono
      (integrable_finsetSum s (fun i _ => hi i)) (integrable_const C) (hC s)
    _ = C := by simp

theorem twoFormHeat_weight_summable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i : TwoFormEigenIndex (o := o) hRic => twoFormHeatWeight hRic t i.1) := by
  have hs := twoFormHeat_weight_square_summable (o := o) hRic (t / 2) (half_pos ht)
  apply hs.congr
  intro i
  simp only [twoFormHeatWeight, pow_two, ← Real.exp_add, NNReal.coe_div, NNReal.coe_ofNat]
  congr 1
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth Hodge eigenspace is linearly equivalent to its
finite-dimensional resolvent eigenspace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormSmoothEigenL2_surjective (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    Function.Surjective (twoFormSmoothEigenL2 hRic μ) := by
  intro f
  by_cases hf : f.val = 0
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    change smoothTwoFormToL2 (0 : SmoothL2TwoForm o) = f.val
    rw [map_zero, hf]
  · obtain ⟨w, hw, he⟩ := twoFormResolvent_eigenvector_smooth hRic ⟨f.property, hf⟩
    exact ⟨⟨w, Module.End.mem_eigenspace_iff.mpr he⟩, Subtype.ext hw.symm⟩

def twoFormSmoothEigenEquiv (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    TwoFormSmoothEigenSpace hRic μ ≃ₗ[ℝ] TwoFormSpectralSpace hRic μ :=
  LinearEquiv.ofBijective (twoFormSmoothEigenL2 hRic μ)
    ⟨twoFormSmoothEigenL2_injective hRic μ, twoFormSmoothEigenL2_surjective hRic μ⟩

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

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_15
theorem scalarEigen_differential_zero (i : ScalarBaseEigenIndex g o d)
    (hi : scalarBaseHeatRate g o d i = 0) :
    smoothOneFormL2Linear (o := o)
      (smoothScalarDifferential g (scalarBaseEigenfunction g o d i)) = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [scalarEigen_differential_inner, hi, zero_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normalized exterior derivatives of the coexact one-form modes.
They give actual orthonormal two-form lifts, not arbitrary spectral preimages. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g)

def oneFormCoexactEigensection (i : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothCovariantFields M 1 :=
  smoothTwoFormCodifferentialField (oneFormCoexactEigenvector_smooth hRic i).choose

theorem oneFormCoexactEigensection_L2 (i : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothOneFormL2Linear (o := o) (oneFormCoexactEigensection hRic i) =
      oneFormCoexactEigenvector hRic i :=
  (oneFormCoexactEigenvector_smooth hRic i).choose_spec.1.symm

theorem oneFormCoexactEigensection_eigen (i : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothOneFormHodgeLaplacian (o := o) (oneFormCoexactEigensection hRic i) =
      (i.1.val⁻¹ - 1) • oneFormCoexactEigensection hRic i :=
  (oneFormCoexactEigenvector_smooth hRic i).choose_spec.2

theorem oneFormCoexactEigensection_divergence (i : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothOneFormDivergence g (oneFormCoexactEigensection hRic i) = 0 :=
  smoothTwoFormCodifferential_divergence hRic _

theorem oneFormCoexactEigensection_codiff_exterior
    (i : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothTwoFormCodifferentialField (smoothOneFormExterior (o := o) (oneFormCoexactEigensection hRic i)) =
      (i.1.val⁻¹ - 1) • oneFormCoexactEigensection hRic i := by
  have he := oneFormCoexactEigensection_eigen hRic i
  rw [smoothOneFormHodgeLaplacian_apply, oneFormCoexactEigensection_divergence hRic,
    show smoothScalarDifferential g 0 = 0 from (smoothScalarDifferentialLinear g).map_zero,
    sub_zero] at he
  exact he

def oneFormCoexactLift (i : OneFormCoexactEigenIndex (o := o) hRic) : smoothTwoForms o :=
  (Real.sqrt (i.1.val⁻¹ - 1))⁻¹ •
    smoothOneFormExterior (o := o) (oneFormCoexactEigensection hRic i)

def oneFormCoexactLiftL2 (i : OneFormCoexactEigenIndex (o := o) hRic) : TwoFormL2 o :=
  smoothTwoFormToL2 (oneFormCoexactLift hRic i : SmoothL2TwoForm o)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A complete orthonormal one-form eigenfamily, obtained from the actual
scalar and two-form spectra and the proved geometric Hodge decomposition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem oneFormEigenvector_total :
    (Submodule.span ℝ (range (oneFormEigenvector hRic d))).topologicalClosure = ⊤ := by
  let K := Submodule.span ℝ (range (oneFormEigenvector hRic d))
  have hco : Submodule.span ℝ (range (oneFormCoexactEigenvector (o := o) hRic)) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Sum.inr i, rfl⟩
  have hsub : Submodule.span ℝ (range (oneFormDerivedFamily hRic d)) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl i =>
      change smoothOneFormL2Linear (o := o)
        (smoothScalarDifferential g (scalarBaseEigenfunction g o d i)) ∈ K
      by_cases hi : 0 < scalarBaseHeatRate g o d i
      · have hs : Real.sqrt (scalarBaseHeatRate g o d i) ≠ 0 := (Real.sqrt_pos.mpr hi).ne'
        have he : Real.sqrt (scalarBaseHeatRate g o d i) •
            oneFormExactEigenvector g o d ⟨i, hi⟩ =
            smoothOneFormL2Linear (o := o)
              (smoothScalarDifferential g (scalarBaseEigenfunction g o d i)) :=
          smul_inv_smul₀ hs _
        rw [← he]
        exact K.smul_mem _ (Submodule.subset_span ⟨Sum.inl ⟨i, hi⟩, rfl⟩)
      · have hz : scalarBaseHeatRate g o d i = 0 :=
          le_antisymm (le_of_not_gt hi) (scalarBaseHeatRate_nonneg g o d i)
        rw [scalarEigen_differential_zero g o d i hz]
        exact K.zero_mem
    | inr i =>
      let u : TwoFormSmoothEigenSpace hRic i.1 := ⟨twoFormEigenform hRic i,
        Module.End.mem_eigenspace_iff.mpr (twoFormEigenform_laplacian hRic i)⟩
      have hu : smoothOneFormL2Linear (o := o)
          (smoothTwoFormCodifferentialField (twoFormEigenform hRic i)) ∈
          OneFormCoexactSpectralSpace hRic i.1 := ⟨u, rfl⟩
      exact hco (oneFormCoexact_mem_span hRic i.1 ⟨_, hu⟩)
  apply top_unique
  rw [← oneFormDerivedFamily_total hRic d]
  exact Submodule.topologicalClosure_mono hsub

def oneFormEigenbasis : HilbertBasis (OneFormEigenIndex hRic d) ℝ (OneFormL2 o) :=
  HilbertBasis.mk (oneFormEigenvector_orthonormal hRic d) (oneFormEigenvector_total hRic d).ge

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded spectral lifts from actual one-forms to their scalar and
closed two-form potentials. The lifts preserve the spectral parameter. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff lp

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g)

def oneFormCoexactSynthesis : ℓ²(OneFormCoexactEigenIndex (o := o) hRic, ℝ) →ₗᵢ[ℝ] OneFormL2 o :=
  modeSynthesis _ (oneFormCoexactEigenvector_orthonormal hRic)

variable [SecondCountableTopology M]
variable (d : ParallelMetricData g (canonicalFrameMeasure g o))

def oneFormExactSynthesis : ℓ²(OneFormExactEigenIndex g o d, ℝ) →ₗᵢ[ℝ] OneFormL2 o :=
  modeSynthesis _ (oneFormExactEigenvector_orthonormal g o d)

def scalarPositiveSynthesis : ℓ²(OneFormExactEigenIndex g o d, ℝ) →ₗᵢ[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  modeSynthesis (fun i => scalarBaseEigenvector g o d i.val)
    ((scalarBaseEigenvector_orthonormal g o d).comp (fun i : OneFormExactEigenIndex g o d => i.val) Subtype.val_injective)

def oneFormExactSpectralLift : OneFormL2 o →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  (scalarPositiveSynthesis d).toContinuousLinearMap.comp
    (oneFormExactSynthesis d).toContinuousLinearMap.adjoint

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded spectral multipliers on the actual one-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def oneFormSpectralEquiv := (oneFormEigenbasis hRic d).repr


def oneFormSpectralMultiplier
    (a : OneFormEigenIndex hRic d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) : OneFormL2 o →L[ℝ] OneFormL2 o :=
  (oneFormSpectralEquiv hRic d).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lp.mapCLM 2
      (fun μ => a μ • ContinuousLinearMap.id ℝ (ℝ))
      hC (fun μ => by
        calc
          ‖a μ • ContinuousLinearMap.id ℝ (ℝ)‖ ≤ |a μ| := by
            apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
            intro v
            change ‖a μ • v‖ ≤ |a μ| * ‖v‖
            rw [norm_smul, Real.norm_eq_abs]
          _ ≤ C := ha μ)).comp
      (oneFormSpectralEquiv hRic d).toContinuousLinearEquiv.toContinuousLinearMap)

theorem oneFormSpectralMultiplier_coordinate
    (a : OneFormEigenIndex hRic d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f : OneFormL2 o) (μ : OneFormEigenIndex hRic d) :
    (oneFormSpectralEquiv hRic d (oneFormSpectralMultiplier hRic d a C hC ha f)) μ =
      a μ • (oneFormSpectralEquiv hRic d f) μ := by
  change ((oneFormSpectralEquiv hRic d)
    ((oneFormSpectralEquiv hRic d).symm _)) μ = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem oneFormSpectralMultiplier_norm
    (a : OneFormEigenIndex hRic d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f : OneFormL2 o) :
    ‖oneFormSpectralMultiplier hRic d a C hC ha f‖ ≤ C * ‖f‖ := by
  rw [← (oneFormSpectralEquiv hRic d).norm_map (oneFormSpectralMultiplier hRic d a C hC ha f),
    ← (oneFormSpectralEquiv hRic d).norm_map f]
  calc
    _ ≤ ‖C • oneFormSpectralEquiv hRic d f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro μ
      rw [oneFormSpectralMultiplier_coordinate, norm_smul, Real.norm_eq_abs]
      change |a μ| * ‖(oneFormSpectralEquiv hRic d f) μ‖ ≤
        ‖C • (oneFormSpectralEquiv hRic d f) μ‖
      change |a μ| * |(oneFormSpectralEquiv hRic d f) μ| ≤
        |C * (oneFormSpectralEquiv hRic d f) μ|
      rw [abs_mul, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha μ) (abs_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]

theorem oneFormSpectralMultiplier_inner
    (a : OneFormEigenIndex hRic d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f h : OneFormL2 o) :
    inner ℝ (oneFormSpectralMultiplier hRic d a C hC ha f) h =
      ∑' μ, a μ * inner ℝ ((oneFormSpectralEquiv hRic d f) μ)
        ((oneFormSpectralEquiv hRic d h) μ) := by
  rw [← (oneFormSpectralEquiv hRic d).inner_map_map, lp.inner_eq_tsum]
  apply tsum_congr
  intro μ
  rw [oneFormSpectralMultiplier_coordinate, real_inner_smul_left]

theorem oneFormSpectralMultiplier_selfAdjoint
    (a : OneFormEigenIndex hRic d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f h : OneFormL2 o) :
    inner ℝ (oneFormSpectralMultiplier hRic d a C hC ha f) h =
      inner ℝ f (oneFormSpectralMultiplier hRic d a C hC ha h) := by
  calc
    _ = ∑' μ, a μ * inner ℝ ((oneFormSpectralEquiv hRic d f) μ)
        ((oneFormSpectralEquiv hRic d h) μ) := oneFormSpectralMultiplier_inner hRic d a C hC ha f h
    _ = ∑' μ, a μ * inner ℝ ((oneFormSpectralEquiv hRic d h) μ)
        ((oneFormSpectralEquiv hRic d f) μ) := by
      apply tsum_congr
      intro μ
      rw [real_inner_comm]
    _ = inner ℝ (oneFormSpectralMultiplier hRic d a C hC ha h) f :=
      (oneFormSpectralMultiplier_inner hRic d a C hC ha h f).symm
    _ = _ := real_inner_comm _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form heat semigroup, defined from the complete smooth
Hodge eigenbasis. Positivity of the spectrum comes from positive Ricci curvature. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def oneFormHeat (t : ℝ≥0) : OneFormL2 o →L[ℝ] OneFormL2 o :=
  oneFormSpectralMultiplier hRic d (oneFormHeatWeight hRic d t) 1 zero_le_one
    (oneFormHeatWeight_bound hRic d t)

theorem oneFormHeat_coordinate (t : ℝ≥0) (f : OneFormL2 o)
    (μ : OneFormEigenIndex hRic d) :
    (oneFormSpectralEquiv hRic d (oneFormHeat hRic d t f)) μ =
      oneFormHeatWeight hRic d t μ • (oneFormSpectralEquiv hRic d f) μ :=
  oneFormSpectralMultiplier_coordinate hRic d _ _ _ _ f μ

theorem oneFormHeat_contraction (t : ℝ≥0) (f : OneFormL2 o) :
    ‖oneFormHeat hRic d t f‖ ≤ ‖f‖ := by
  simpa only [oneFormHeat, one_mul] using oneFormSpectralMultiplier_norm hRic d
    (oneFormHeatWeight hRic d t) 1 zero_le_one (oneFormHeatWeight_bound hRic d t) f

theorem oneFormHeat_selfAdjoint (t : ℝ≥0) (f h : OneFormL2 o) :
    inner ℝ (oneFormHeat hRic d t f) h = inner ℝ f (oneFormHeat hRic d t h) :=
  oneFormSpectralMultiplier_selfAdjoint hRic d _ _ _ _ f h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Dominated spectral convergence for the actual one-form heat space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem oneFormSpectralMultiplier_sub_norm_sq
    (a b : OneFormEigenIndex hRic d → ℝ)
    (ha : ∀ μ, |a μ| ≤ 1) (hb : ∀ μ, |b μ| ≤ 1) (f : OneFormL2 o) :
    ‖oneFormSpectralMultiplier hRic d a 1 zero_le_one ha f -
      oneFormSpectralMultiplier hRic d b 1 zero_le_one hb f‖ ^ 2 =
      ∑' μ, (a μ - b μ) ^ 2 * ‖(oneFormSpectralEquiv hRic d f) μ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← (oneFormSpectralEquiv hRic d).inner_map_map,
    map_sub, lp.inner_eq_tsum]
  apply tsum_congr
  intro μ
  change inner ℝ
    ((oneFormSpectralEquiv hRic d (oneFormSpectralMultiplier hRic d a 1 zero_le_one ha f)) μ -
      (oneFormSpectralEquiv hRic d (oneFormSpectralMultiplier hRic d b 1 zero_le_one hb f)) μ)
    ((oneFormSpectralEquiv hRic d (oneFormSpectralMultiplier hRic d a 1 zero_le_one ha f)) μ -
      (oneFormSpectralEquiv hRic d (oneFormSpectralMultiplier hRic d b 1 zero_le_one hb f)) μ) = _
  rw [oneFormSpectralMultiplier_coordinate, oneFormSpectralMultiplier_coordinate,
    ← sub_smul, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

theorem oneFormSpectralMultiplier_tendsto {α : Type*} {l : Filter α}
    (a : α → OneFormEigenIndex hRic d → ℝ)
    (b : OneFormEigenIndex hRic d → ℝ)
    (ha : ∀ x μ, |a x μ| ≤ 1) (hb : ∀ μ, |b μ| ≤ 1)
    (hab : ∀ μ, Tendsto (fun x => a x μ) l (𝓝 (b μ))) (f : OneFormL2 o) :
    Tendsto (fun x => oneFormSpectralMultiplier hRic d (a x) 1 zero_le_one (ha x) f) l
      (𝓝 (oneFormSpectralMultiplier hRic d b 1 zero_le_one hb f)) := by
  have hsum : Summable (fun μ : OneFormEigenIndex hRic d =>
      4 * ‖(oneFormSpectralEquiv hRic d f) μ‖ ^ 2) := by
    have hs := lp.summable_inner (𝕜 := ℝ)
      (oneFormSpectralEquiv hRic d f) (oneFormSpectralEquiv hRic d f)
    simp only [real_inner_self_eq_norm_sq] at hs
    exact hs.mul_left 4
  have hbound (x : α) (μ : OneFormEigenIndex hRic d) :
      ‖(a x μ - b μ) ^ 2 * ‖(oneFormSpectralEquiv hRic d f) μ‖ ^ 2‖ ≤
        4 * ‖(oneFormSpectralEquiv hRic d f) μ‖ ^ 2 := by
    have hdiff : |a x μ - b μ| ≤ 2 :=
      (abs_sub (a x μ) (b μ)).trans (by linarith only [ha x μ, hb μ])
    have hsq : (a x μ - b μ) ^ 2 ≤ 4 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hdiff)
        (add_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (abs_nonneg (a x μ - b μ)))
      nlinarith only [hprod, sq_abs (a x μ - b μ)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hpoint (μ : OneFormEigenIndex hRic d) :
      Tendsto (fun x => (a x μ - b μ) ^ 2 * ‖(oneFormSpectralEquiv hRic d f) μ‖ ^ 2)
        l (𝓝 (0 : ℝ)) := by
    convert (((hab μ).sub_const (b μ)).pow 2).mul_const
      (‖(oneFormSpectralEquiv hRic d f) μ‖ ^ 2) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have ht := tendsto_tsum_of_dominated_convergence hsum hpoint
    (Eventually.of_forall hbound)
  simp only [tsum_zero] at ht
  have hn : Tendsto (fun x => ‖oneFormSpectralMultiplier hRic d (a x) 1 zero_le_one (ha x) f -
      oneFormSpectralMultiplier hRic d b 1 zero_le_one hb f‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    simpa only [oneFormSpectralMultiplier_sub_norm_sq] using ht
  have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  convert hs using 1
  · funext x
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · exact congrArg nhds Real.sqrt_zero.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strong continuity, eigenmode evolution and decay of the actual
degree-one heat semigroup. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem oneFormHeat_eigenvector (t : ℝ≥0) (i : OneFormEigenIndex hRic d) :
    oneFormHeat hRic d t (oneFormEigenvector hRic d i) =
      oneFormHeatWeight hRic d t i • oneFormEigenvector hRic d i := by
  classical
  apply (oneFormSpectralEquiv hRic d).injective
  apply lp.ext
  funext j
  rw [oneFormHeat_coordinate, map_smul]
  have hbi : oneFormEigenbasis hRic d i = oneFormEigenvector hRic d i := by
    simp only [oneFormEigenbasis, HilbertBasis.coe_mk]
  have hb : oneFormSpectralEquiv hRic d (oneFormEigenvector hRic d i) = lp.single 2 i (1 : ℝ) := by
    change (oneFormEigenbasis hRic d).repr _ = _
    simpa only [hbi] using (oneFormEigenbasis hRic d).repr_self i
  rw [hb]
  by_cases h : j = i
  · subst j
    simp
  · simp [lp.single_apply, h]

theorem oneFormHeat_continuous (f : OneFormL2 o) :
    Continuous (fun t : ℝ≥0 => oneFormHeat hRic d t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply oneFormSpectralMultiplier_tendsto hRic d
    (oneFormHeatWeight hRic d) (oneFormHeatWeight hRic d t)
    (oneFormHeatWeight_bound hRic d) (oneFormHeatWeight_bound hRic d t)
  intro i
  have hc : Continuous (fun s : ℝ≥0 => oneFormHeatWeight hRic d s i) := by
    unfold oneFormHeatWeight
    fun_prop
  exact hc.tendsto t

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time summability of the actual one-form heat spectrum,
using the scalar spectrum and the finite coexact images of two-form eigenspaces. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormCoexact_finrank_le (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ) ≤
      Module.finrank ℝ (TwoFormSpectralSpace hRic μ) := by
  have h := LinearMap.finrank_range_le (oneFormCodiffEigenMap (o := o) hRic μ)
  exact h.trans_eq (twoFormSmoothEigenEquiv hRic μ).finrank_eq

def oneFormCoexactToTwoFormIndex (hRic : RicciThree g)
    (i : OneFormCoexactEigenIndex (o := o) hRic) : TwoFormEigenIndex (o := o) hRic :=
  ⟨i.1, Fin.castLE (oneFormCoexact_finrank_le hRic i.1) i.2⟩

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormCoexactToTwoFormIndex_injective (hRic : RicciThree g) :
    Function.Injective (oneFormCoexactToTwoFormIndex (o := o) hRic) := by
  rintro ⟨μ, i⟩ ⟨ν, j⟩ h
  have hμ : μ = ν := congrArg Sigma.fst h
  subst ν
  have hi : i.val = j.val := congrArg (fun k : TwoFormEigenIndex (o := o) hRic => k.2.val) h
  exact congrArg (Sigma.mk μ) (Fin.ext hi)

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

omit [PreconnectedSpace M] in
theorem oneFormHeat_weight_summable (t : ℝ≥0) (ht : 0 < t) :
    Summable (oneFormHeatWeight hRic d t) := by
  have h₀ := (scalarHeat_weight_summable g o d t ht).comp_injective
    (i := fun i : OneFormExactEigenIndex g o d => i.val) Subtype.val_injective
  have h₂ := (twoFormHeat_weight_summable (o := o) hRic t ht).comp_injective
    (i := oneFormCoexactToTwoFormIndex (o := o) hRic)
    (oneFormCoexactToTwoFormIndex_injective hRic)
  change Summable (fun i : OneFormExactEigenIndex g o d =>
    oneFormHeatWeight hRic d t (Sum.inl i)) at h₀
  change Summable (fun i : OneFormCoexactEigenIndex (o := o) hRic =>
    oneFormHeatWeight hRic d t (Sum.inr i)) at h₂
  exact Summable.sum _ h₀ h₂

end
end PositiveEinsteinFour.Geometry
end


section

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter
open scoped Manifold ContDiff _root_.Topology NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem oneFormHeat_joint_continuous (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    Continuous (fun tf : ℝ≥0 × OneFormL2 o => oneFormHeat hRic d tf.1 tf.2) := by
  apply continuous_iff_continuousAt.mpr
  intro tf
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have htime := Metric.continuousAt_iff.mp
    ((oneFormHeat_continuous hRic d tf.2).continuousAt (x := tf.1))
    (ε / 2) (half_pos hε)
  obtain ⟨δ, hδ, htime⟩ := htime
  refine ⟨min δ (ε / 2), lt_min hδ (half_pos hε), ?_⟩
  intro sf hsf
  have hst : dist sf.1 tf.1 < δ := by
    calc
      dist sf.1 tf.1 ≤ dist sf tf := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ < δ := lt_of_lt_of_le hsf (min_le_left _ _)
  have hsu : dist sf.2 tf.2 < ε / 2 := by
    calc
      dist sf.2 tf.2 ≤ dist sf tf := by rw [Prod.dist_eq]; exact le_max_right _ _
      _ < ε / 2 := lt_of_lt_of_le hsf (min_le_right _ _)
  calc
    dist (oneFormHeat hRic d sf.1 sf.2) (oneFormHeat hRic d tf.1 tf.2) ≤
        dist (oneFormHeat hRic d sf.1 sf.2) (oneFormHeat hRic d sf.1 tf.2) +
        dist (oneFormHeat hRic d sf.1 tf.2) (oneFormHeat hRic d tf.1 tf.2) := dist_triangle _ _ _
    _ ≤ dist sf.2 tf.2 + dist (oneFormHeat hRic d sf.1 tf.2) (oneFormHeat hRic d tf.1 tf.2) := by
      apply add_le_add_left
      rw [dist_eq_norm, ← map_sub, dist_eq_norm]
      exact oneFormHeat_contraction hRic d sf.1 (sf.2 - tf.2)
    _ < ε / 2 + ε / 2 := add_lt_add hsu (htime hst)
    _ = ε := add_halves ε

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual positive one-form heat spectrum stays away from zero.
Trace summability leaves only finitely many modes in a bounded interval. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem oneFormHeatRate_lower_bound :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i : OneFormEigenIndex hRic d, ε ≤ oneFormHeatRate hRic d i := by
  classical
  have hs := (oneFormHeat_weight_summable hRic d 1 zero_lt_one).tendsto_cofinite_zero
  have hev : ∀ᶠ i in cofinite, oneFormHeatWeight hRic d 1 i < Real.exp (-1) :=
    hs.eventually (gt_mem_nhds (Real.exp_pos (-1)))
  have hfinite : {i : OneFormEigenIndex hRic d | ¬oneFormHeatWeight hRic d 1 i < Real.exp (-1)}.Finite :=
    (mem_cofinite.mp hev)
  obtain ⟨ε, hε, hbound⟩ := finite_positive_lower_bound_p1 hfinite.toFinset
    (oneFormHeatRate hRic d) (fun i _ => oneFormHeatRate_pos hRic d i)
  refine ⟨min ε 1, lt_min hε zero_lt_one, fun i => ?_⟩
  by_cases hi : i ∈ hfinite.toFinset
  · exact (min_le_left _ _).trans (hbound i hi)
  · have hweight : oneFormHeatWeight hRic d 1 i < Real.exp (-1) := by
      simpa only [Finite.mem_toFinset, mem_ofPred_eq, not_not] using hi
    have hr : 1 < oneFormHeatRate hRic d i := by
      change Real.exp (-(1 : ℝ≥0) * oneFormHeatRate hRic d i) < Real.exp (-1) at hweight
      have he := Real.exp_lt_exp.mp hweight
      norm_num at he
      linarith
    exact (min_le_right _ _).trans hr.le

theorem oneFormHeatRate_inv_sqrt_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ i : OneFormEigenIndex hRic d,
      |(Real.sqrt (oneFormHeatRate hRic d i))⁻¹| ≤ C := by
  obtain ⟨ε, hε, hb⟩ := oneFormHeatRate_lower_bound hRic d
  refine ⟨(Real.sqrt ε)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hε), fun i => ?_⟩
  rw [abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (oneFormHeatRate_pos hRic d i)))]
  exact inv_anti₀ (Real.sqrt_pos.mpr hε) (Real.sqrt_le_sqrt (hb i))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Bochner heat convolution, its eigenmode pairing and its
quadratic norm bound for a linearly vanishing residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M] {g : SmoothMetric M} {o : FrameOrientation g}

def oneFormHeatConvolution (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) (R : ℝ → OneFormL2 o) (t : ℝ) : OneFormL2 o :=
  ∫ s in (0 : ℝ)..t, oneFormHeat hRic d (t - s).toNNReal (R s)

theorem oneFormHeatConvolution_integrable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (R : ℝ → OneFormL2 o) (t : ℝ) (ht : 0 ≤ t) (hR : ContinuousOn R (Icc 0 t)) :
    IntervalIntegrable (fun s => oneFormHeat hRic d (t - s).toNNReal (R s)) volume 0 t := by
  have htime : Continuous (fun s : ℝ => (t - s).toNNReal) :=
    continuous_real_toNNReal.comp (continuous_const.sub continuous_id)
  exact ((oneFormHeat_joint_continuous hRic d).comp_continuousOn
    (htime.continuousOn.prodMk hR)).intervalIntegrable_of_Icc ht

theorem oneFormHeatConvolution_eigen (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (R : ℝ → OneFormL2 o) (t : ℝ) (ht : 0 ≤ t) (hR : ContinuousOn R (Icc 0 t))
    (i : OneFormEigenIndex hRic d) :
    inner ℝ (oneFormHeatConvolution hRic d R t) (oneFormEigenvector hRic d i) =
      ∫ s in (0 : ℝ)..t, Real.exp (-oneFormHeatRate hRic d i * (t - s)) *
        inner ℝ (R s) (oneFormEigenvector hRic d i) := by
  have hi := oneFormHeatConvolution_integrable hRic d R t ht hR
  have hp := (innerSL ℝ (oneFormEigenvector hRic d i)).intervalIntegral_comp_comm hi
  change (∫ s in (0 : ℝ)..t,
    inner ℝ (oneFormEigenvector hRic d i) (oneFormHeat hRic d (t - s).toNNReal (R s))) =
      inner ℝ (oneFormEigenvector hRic d i) (oneFormHeatConvolution hRic d R t) at hp
  rw [real_inner_comm, ← hp]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc 0 t := by simpa only [uIcc_of_le ht] using hs
  change inner ℝ (oneFormEigenvector hRic d i) (oneFormHeat hRic d (t - s).toNNReal (R s)) =
    Real.exp (-oneFormHeatRate hRic d i * (t - s)) * inner ℝ (R s) (oneFormEigenvector hRic d i)
  rw [real_inner_comm, oneFormHeat_selfAdjoint, oneFormHeat_eigenvector, real_inner_smul_right]
  unfold oneFormHeatWeight
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr hs'.2)]
  ring_nf

end
end PositiveEinsteinFour.Geometry
end


section

/-! A bounded inverse square root on the strictly positive degree-one spectrum. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def oneFormInverseSquareRoot : OneFormL2 o →L[ℝ] OneFormL2 o :=
  oneFormSpectralMultiplier hRic d (fun i => (Real.sqrt (oneFormHeatRate hRic d i))⁻¹)
    (oneFormHeatRate_inv_sqrt_bound hRic d).choose
    (oneFormHeatRate_inv_sqrt_bound hRic d).choose_spec.1.le
    (oneFormHeatRate_inv_sqrt_bound hRic d).choose_spec.2

def oneFormScalarPotential : OneFormL2 o →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  (oneFormExactSpectralLift d).comp (oneFormInverseSquareRoot hRic d)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form diagonal heat density and its frame-column realization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance instCompactSpaceFrameBundle_27_ra4f0fb_1 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
def oneFormHeatDiagonal (t : ℝ≥0) (x : M) : ℝ :=
  ∑' i, oneFormHeatWeight hRic d t i * covariantFieldNormSq g (oneFormEigenSection hRic d i).val x

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


