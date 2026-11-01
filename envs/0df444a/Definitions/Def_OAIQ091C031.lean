-- Prove2me | Definitions.Def_OAIQ091C031
-- name    : OAIQ091C031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:58:01.090117+00:00
-- url     : https://prove2.me/theorems/bf3e7c30-cb01-4f38-a79b-18e148039321
-- title:
--   Definitions bundle OAIQ091C031 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 182 declarations of OpenAI's Lean: 14 definitions, 2 instances and 166 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.oneFormCoexactHeatTrace`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeatTrace`, `OAI.PositiveEinsteinFour.Geometry.scalarH1BaseLp`, `OAI.PositiveEinsteinFour.Geometry.scalarH1LocalizedCoordinate`, `OAI.PositiveEinsteinFour.Geometry.scalarWeightedBaseLp`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicToWeak`, `OAI.PositiveEinsteinFour.Geometry.twoFormEigenSection`, `OAI.PositiveEinsteinFour.Geometry.twoFormEigenspaceHodge`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatFrameCoefficient`, `OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenDDelta`, `OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenHodge`, `OAI.PositiveEinsteinFour.Geometry.twoFormWeakHarmonicResolventEquiv`, `OAI.PositiveEinsteinFour.Geometry.twoFormWeakHarmonicToResolvent`, `OAI.PositiveEinsteinFour.Geometry.unitFormPositiveAddGroup`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_GeodesicGeometry06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry06.lean), [`EinsteinFour_GeodesicGeometry12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry12.lean), [`EinsteinFour_GeodesicGeometry13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry13.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory09.lean), [`EinsteinFour_HodgeTheory11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory11.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates07.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C044`, `OAIQ091C028` and `OAIQ091C029` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C032`, `OAIQ091C050`, `OAIQ091C051` and `OAIQ091C053`; the statements `OAI_PositiveEinsteinFour_Bianchi_weightPlusPart_norm`, `OAI_PositiveEinsteinFour_HighestHessian_rightDerivativeSlotForm_sector` and `OAI_PositiveEinsteinFour_HighestHessian_traceComponent_pairing_hessian`; the proofs of `OAI_PositiveEinsteinFour_Bianchi_weightPlusPart_norm`, `OAI.PositiveEinsteinFour.Geometry.actual_frameExponential_injOn_sqrt_three` and `OAI_PositiveEinsteinFour_HighestHessian_rightDerivativeSlotForm_sector`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C044
import Definitions.Def_OAIQ091C028
import Definitions.Def_OAIQ091C029

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

/-! Short paths cannot leave a normal-coordinate ball. This supplies the
distance lower bound needed for locally minimizing radial geodesics. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Filter Set MeasureTheory Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

/-- The constructed radial geodesics minimize distance near their initial point. -/
theorem frameExponential_locally_minimizing (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∀ v : FourSpace, ‖v‖ < r →
      metricEDistance g e.base (frameExponential g o e v) = ENNReal.ofReal ‖v‖ := by
  obtain ⟨R, C, hR, hsource, hC, hI⟩ := frameExponential_normal_ball g o e
  refine ⟨R / 2, half_pos hR, fun v hv => le_antisymm (frameExponential_distance g o e v) ?_⟩
  apply frameExponential_normal_ball_distance_lower g o hRic e he C hC hI (R / 2)
    (half_pos hR) _ v hv
  rw [hsource]
  exact closedBall_subset_ball (by linarith)

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

theorem frameMinimizingTimes_has_positive (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) :
    ∃ t ∈ frameMinimizingTimes g e, 0 < t := by
  obtain ⟨r, hr, hmin⟩ := frameExponential_locally_minimizing g o hRic e he
  let t := r / 2
  have ht : 0 < t := half_pos hr
  have hc : ‖(coordinateVector 0 : FourSpace)‖ = 1 := firstDirection.property
  have hn : ‖t • (coordinateVector 0 : FourSpace)‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hc, mul_one]
  have hsmall : ‖t • (coordinateVector 0 : FourSpace)‖ < r := by rw [hn]; dsimp [t]; linarith
  have hm := hmin (t • coordinateVector 0) hsmall
  rw [frameExponential_first_ray g o e he t ht, hn] at hm
  exact ⟨t, ⟨ht.le, hm⟩, ht⟩

variable [PreconnectedSpace M]

theorem actualCutTime_pos (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) :
    0 < actualCutTime g e := by
  obtain ⟨t, ht, hpos⟩ := frameMinimizingTimes_has_positive g o hRic e he
  exact hpos.trans_le (le_csSup (frameMinimizingTimes_bddAbove g e) ht)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Polar coordinates for the actual minimizing-domain Jacobian integral.
The radial cutoff is the proved cut time, not a supplied geometric domain. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

variable [PreconnectedSpace M]

theorem minimizing_exponential_integral_polar (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    (∫⁻ v in actualMinimizingTangentDomain g o e,
      ENNReal.ofReal (frameExponentialJacobian g o e v)) =
    ∫⁻ p : Directions × Ioi (0 : ℝ),
      (if p.2.val ≤ actualCutTime g
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1))) then
        ENNReal.ofReal |((actualJacobiSolution g hRic
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1)))).J p.2.val).det /
            p.2.val ^ 3| else 0)
      ∂((polarAngularMass • sphereMeasure).prod (Measure.volumeIoiPow 3)) := by
  classical
  let S := actualMinimizingTangentDomain g o e
  let J := fun v => ENNReal.ofReal (frameExponentialJacobian g o e v)
  have hS : MeasurableSet S := (actualMinimizingTangentDomain_closed g o e).measurableSet
  have hJ : Measurable J := (ENNReal.continuous_ofReal.comp
    (frameExponentialJacobian_continuous g o e)).measurable
  have h := euclideanPolarReconstruction_measurePreserving.lintegral_comp (hJ.indicator hS)
  calc
    _ = ∫⁻ v, S.indicator J v := (lintegral_indicator hS J).symm
    _ = ∫⁻ p : Directions × Ioi (0 : ℝ), S.indicator J (euclideanPolarReconstruction p)
        ∂((polarAngularMass • sphereMeasure).prod (Measure.volumeIoiPow 3)) := h.symm
    _ = _ := by
      apply lintegral_congr
      intro p
      have hiff := actualMinimizingTangentDomain_ray_iff g o e he p.1 p.2.val p.2.property.le
      by_cases hc : p.2.val ≤ actualCutTime g
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1)))
      · have hm : euclideanPolarReconstruction p ∈ S := hiff.mpr hc
        rw [ite_eq_left hc, Set.indicator_of_mem hm]
        exact congrArg ENNReal.ofReal (frameExponentialJacobian_direction g o hRic e he
          p.1 p.2.val p.2.property)
      · have hm : euclideanPolarReconstruction p ∉ S := fun hh => hc (hiff.mp hh)
        rw [ite_eq_right hc, Set.indicator_of_notMem hm]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_first _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Canceling the radial cubic measure against the actual exponential
Jacobian leaves the determinant of the normal Jacobi tensor itself. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem minimizing_exponential_integral_radial (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    (∫⁻ v in actualMinimizingTangentDomain g o e,
      ENNReal.ofReal (frameExponentialJacobian g o e v)) =
    polarAngularMass * ∫⁻ q : Directions, ∫⁻ r : Ioi (0 : ℝ),
      (if r.val ≤ actualCutTime g
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) then
        ENNReal.ofReal |((actualJacobiSolution g hRic
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det|
        else 0) ∂((volume : Measure ℝ).comap Subtype.val) ∂sphereMeasure := by
  classical
  let F : Directions × Ioi (0 : ℝ) → ℝ≥0∞ := fun p =>
    if p.2.val ≤ actualCutTime g
        (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1))) then
      ENNReal.ofReal |((actualJacobiSolution g hRic
        (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1)))).J p.2.val).det /
          p.2.val ^ 3| else 0
  have hF : Measurable F := by
    let S := actualMinimizingTangentDomain g o e
    let J := fun v => ENNReal.ofReal (frameExponentialJacobian g o e v)
    have hS : MeasurableSet S := (actualMinimizingTangentDomain_closed g o e).measurableSet
    have hJ : Measurable J := (ENNReal.continuous_ofReal.comp
      (frameExponentialJacobian_continuous g o e)).measurable
    have hf := (hJ.indicator hS).comp
      euclideanPolarReconstruction_measurePreserving.measurable
    convert hf using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    have hiff := actualMinimizingTangentDomain_ray_iff g o e he p.1 p.2.val p.2.property.le
    by_cases hc : p.2.val ≤ actualCutTime g
        (e.rotate (orientedToOrthogonal (directionOrientedMatrix p.1)))
    · have hm : euclideanPolarReconstruction p ∈ S := hiff.mpr hc
      simp only [F, ite_eq_left hc, Function.comp_apply, Set.indicator_of_mem hm, J]
      exact (congrArg ENNReal.ofReal (frameExponentialJacobian_direction g o hRic e he
        p.1 p.2.val p.2.property)).symm
    · have hm : euclideanPolarReconstruction p ∉ S := fun hh => hc (hiff.mp hh)
      simp only [F, ite_eq_right hc, Function.comp_apply, Set.indicator_of_notMem hm]
  rw [minimizing_exponential_integral_polar g o hRic e he]
  change (∫⁻ p, F p ∂((polarAngularMass • sphereMeasure).prod (Measure.volumeIoiPow 3))) = _
  rw [lintegral_prod _ hF.aemeasurable, lintegral_smul_measure]
  congr 1
  apply lintegral_congr
  intro q
  have hrmeas : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.val ^ 3)) := by
    fun_prop
  rw [Measure.volumeIoiPow,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hrmeas
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply lintegral_congr
  intro r
  dsimp [F]
  split_ifs with hc
  · exact radial_cubic_cancel _ r.val r.property
  · exact mul_zero _

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.heatSignedTraceENorm
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Bounded localization of the intrinsic scalar H¹ space into Euclidean
L⁴. The construction uses the actual chart representative and its four
weak derivatives, with a compact smooth cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped Manifold ContDiff ENNReal

noncomputable section

local instance instFactLeENNRealOfNat_solutions_3_rc90d1f_1 : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.localSobolev_frameCompact
theorem scalarCutoffChartL4_bound (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) :
    ∃ C : ℝ, ∀ a : SmoothScalar (M := M),
      ‖scalarCutoffChartL4 c hKt χ hχ hc hs a‖ ≤ C * ‖smoothScalarH1Map o d a‖ := by
  refine ⟨(ScalarEuclideanSobolev.constant : ℝ) *
    ∑ i : Fin 4, ‖scalarH1CutoffDerivative g o d c hK hKt χ hχ hc hs i‖, fun a => ?_⟩
  have h := ScalarEuclideanSobolev.toL4_bound_partials (scalarCutoffChartC1 c hKt χ hχ hc hs a)
  calc
    _ ≤ (ScalarEuclideanSobolev.constant : ℝ) *
        ∑ i : Fin 4, ‖ScalarEuclideanSobolev.partialL2 (scalarCutoffChartC1 c hKt χ hχ hc hs a) i‖ := h
    _ ≤ (ScalarEuclideanSobolev.constant : ℝ) *
        ∑ i : Fin 4, ‖scalarH1CutoffDerivative g o d c hK hKt χ hχ hc hs i‖ *
          ‖smoothScalarH1Map o d a‖ := by
      apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
      apply Finset.sum_le_sum
      intro i _
      rw [← scalarH1CutoffDerivative_smooth]
      exact ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.cutoffH2_compact
theorem scalarH1CutoffDerivative_distribution (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (u : scalarH1 d) (i : Fin 4) :
    scalarCoordinateDerivative i
      (scalarComplexL2 (scalarH1CutoffValueL2 g o d c hK hKt χ hχ hc hs u) :
        𝓢'(FourSpace, ℂ)) =
      (scalarComplexL2 (scalarH1CutoffDerivative g o d c hK hKt χ hχ hc hs i u) :
        𝓢'(FourSpace, ℂ)) := by
  exact scalarLocalL2_complex_derivative hK.isClosed.measurableSet
    (scalarH1ChartValue g o d c hK hKt u)
    (scalarH1ChartDerivative g o d c hK hKt i u) i
    (fun q hq hqc hqs => scalarH1Chart_weak_derivative_integral
      g o d c hK hKt u q hq hqc hqs i) χ hχ hc hs

theorem scalarH1CutoffDerivative_memLp_four (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (u : scalarH1 d)
    (hH2 : MemSobolev 2 2
      (scalarComplexL2 (scalarH1CutoffValueL2 g o d c hK hKt χ hχ hc hs u) :
        𝓢'(FourSpace, ℂ))) (i : Fin 4) :
    MemLp (scalarH1CutoffDerivative g o d c hK hKt χ hχ hc hs i u : FourSpace → ℝ)
      4 volume := by
  obtain ⟨v, hv, hv4⟩ := scalar_H2_first_L4 _ hH2 i
  rw [scalarH1CutoffDerivative_distribution] at hv
  have he := scalarL2_distribution_injective hv
  rw [he] at hv4
  have hr : MemLp (fun x : FourSpace =>
      (scalarComplexL2 (scalarH1CutoffDerivative g o d c hK hKt χ hχ hc hs i u) x).re)
      4 volume := (memLp_re_im_iff.mpr hv4).1
  apply (memLp_congr_ae ?_).mp hr
  filter_upwards [scalarComplexL2_coe
    (scalarH1CutoffDerivative g o d c hK hKt χ hχ hc hs i u)] with x hx
  exact congrArg Complex.re hx

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.manifoldSobolev_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.manifoldSobolev_probability
theorem smoothScalarPieceL4_bound (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (c : M) (ρ : SmoothScalar (M := M))
    (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : SmoothScalar (M := M),
      ‖smoothScalarBaseL4 g (smoothScalarProduct ρ a)‖ ≤ C * ‖smoothScalarH1Map o d a‖ := by
  let K := scalarChartSupport c ρ
  have hK : IsCompact K := scalarChartSupport_compact c ρ hs
  have hKt : K ⊆ (chartAt FourSpace c).target := scalarChartSupport_subset c ρ hs
  let χ := scalarChartCutoff c ρ
  have hχ : ContDiff ℝ ∞ χ := scalarChartCutoff_smooth c ρ hs
  have hc : HasCompactSupport χ := scalarChartCutoff_compact c ρ hs
  have hχK : tsupport χ ⊆ K := scalarChartCutoff_support c ρ hs
  obtain ⟨D, hD, hDb⟩ := scalarChart_reverse_eLpNorm_bound g c hK hKt
  obtain ⟨B, hBb⟩ := scalarCutoffChartL4_bound g o d c hK hKt χ hχ hc hχK
  let A := D ^ ((1 / (4 : ℝ≥0∞)).toReal)
  have hA : A ≠ (∞ : ℝ≥0∞) := ENNReal.rpow_ne_top_of_nonneg (by positivity) hD
  refine ⟨A.toReal * max B 0, mul_nonneg ENNReal.toReal_nonneg (le_max_right _ _), fun a => ?_⟩
  have hsupport : Function.support (smoothScalarProduct ρ a).val ⊆
      (chartAt FourSpace c).symm '' K := by
    intro x hx
    have hxρ : x ∈ tsupport ρ.val := subset_tsupport _ (left_ne_zero_of_mul hx)
    exact ⟨chartAt FourSpace c x, ⟨x, hxρ, rfl⟩, (chartAt FourSpace c).left_inv (hs hxρ)⟩
  have hlocal : (fun z => (smoothScalarProduct ρ a).val ((chartAt FourSpace c).symm z))
      =ᵐ[volume.restrict K] (scalarCutoffChartC1 c hKt χ hχ hc hχK a).val := by
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
    change ρ.val ((chartAt FourSpace c).symm z) * a.val ((chartAt FourSpace c).symm z) =
      χ z * a.val ((chartAt FourSpace c).symm z)
    change _ = scalarChartCutoff c ρ z * _
    rw [scalarChartCutoff, indicator_of_mem (hKt hz)]
  have hb := hDb 4 (smoothScalarProduct ρ a).val hsupport
  have hLp := ScalarEuclideanSobolev.toL4_coe (scalarCutoffChartC1 c hKt χ hχ hc hχK a)
  have he : eLpNorm (smoothScalarBaseL4 g (smoothScalarProduct ρ a)) 4 (normalizedVolume g) ≤
      A * eLpNorm (scalarCutoffChartL4 c hKt χ hχ hc hχK a) 4 volume := by
    rw [eLpNorm_congr_ae (smoothScalarBaseL4_coe g (smoothScalarProduct ρ a))]
    calc
      _ ≤ A * eLpNorm (fun z => (smoothScalarProduct ρ a).val ((chartAt FourSpace c).symm z))
          4 (volume.restrict K) := hb
      _ = A * eLpNorm (scalarCutoffChartC1 c hKt χ hχ hc hχK a).val 4
          (volume.restrict K) := by rw [eLpNorm_congr_ae hlocal]
      _ ≤ A * eLpNorm (scalarCutoffChartC1 c hKt χ hχ hc hχK a).val 4 volume :=
        mul_le_mul' le_rfl (eLpNorm_mono_measure _ Measure.restrict_le_self)
      _ = _ := by rw [← eLpNorm_congr_ae hLp]; rfl
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hA (Lp.eLpNorm_ne_top _)) he
  have hn : ‖smoothScalarBaseL4 g (smoothScalarProduct ρ a)‖ ≤
      A.toReal * ‖scalarCutoffChartL4 c hKt χ hχ hc hχK a‖ := by
    simpa only [Lp.norm_def, ENNReal.toReal_mul] using hr
  calc
    _ ≤ A.toReal * (B * ‖smoothScalarH1Map o d a‖) :=
      hn.trans (mul_le_mul_of_nonneg_left (hBb a) ENNReal.toReal_nonneg)
    _ ≤ A.toReal * (max B 0 * ‖smoothScalarH1Map o d a‖) := by
      gcongr
      exact le_max_left _ _
    _ = _ := by ring

theorem smoothScalarBaseL4_bound (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : SmoothScalar (M := M),
      ‖smoothScalarBaseL4 g a‖ ≤ C * ‖smoothScalarH1Map o d a‖ := by
  obtain ⟨P⟩ := scalarPartition_exists (M := M)
  have hpiece (i : P.ι) := smoothScalarPieceL4_bound g o d (P.center i)
    (scalarPartitionFunction P i) (scalarPartitionFunction_support P i)
  choose C hC hCb using hpiece
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun a => ?_⟩
  calc
    _ = ‖∑ i : P.ι, smoothScalarBaseL4 g (smoothScalarProduct (scalarPartitionFunction P i) a)‖ := by
      rw [← map_sum, smoothScalar_partition]
    _ ≤ ∑ i : P.ι, ‖smoothScalarBaseL4 g (smoothScalarProduct (scalarPartitionFunction P i) a)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : P.ι, C i * ‖smoothScalarH1Map o d a‖ := Finset.sum_le_sum (fun i _ => hCb i a)
    _ = _ := (Finset.sum_mul ..).symm

theorem scalarH1BaseL4_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (a : SmoothScalar (M := M)) :
    scalarH1BaseL4 g o d (smoothScalarToH1 d a) = smoothScalarBaseL4 g a := by
  obtain ⟨C, _, hC⟩ := smoothScalarBaseL4_bound g o d
  exact LinearMap.extendOfNorm_eq (smoothScalarH1Map_dense o d) ⟨C, hC⟩ a

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.cutoffH2Realization_compact
theorem scalarH1CutoffValue_H2_of_rep (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (u : scalarH1 d)
    (v : Lp ℂ 2 (volume : Measure FourSpace))
    (hv2 : MemSobolev 2 2 (v : 𝓢'(FourSpace, ℂ)))
    (hv : (v : FourSpace → ℂ) =ᵐ[volume] fun z =>
      (χ z * scalarH1BaseValue g o d u ((chartAt FourSpace c).symm z) : ℝ)) :
    MemSobolev 2 2
      (scalarComplexL2 (scalarH1CutoffValueL2 g o d c hK hKt χ hχ hc hs u) :
        𝓢'(FourSpace, ℂ)) := by
  have hchart := scalarH1ChartValue_coe g o d c hK hKt u
    (scalarH1BaseValue g o d u) (scalarH1BaseValue_spec g o d u)
  have hcut := (scalarLocalL2ProductCLM_coe hK.isClosed.measurableSet χ hχ.continuous hc hs
    (scalarH1ChartValue g o d c hK hKt u)).trans
    (scalarLocalL2Product_ae_congr hK.isClosed.measurableSet χ hs hchart)
  have heq : scalarComplexL2 (scalarH1CutoffValueL2 g o d c hK hKt χ hχ hc hs u) = v := by
    apply Lp.ext
    filter_upwards [scalarComplexL2_coe (scalarH1CutoffValueL2 g o d c hK hKt χ hχ hc hs u),
      hcut, hv] with z hcomplex hreal hrep
    exact hcomplex.trans ((congrArg Complex.ofReal hreal).trans hrep.symm)
  rwa [heq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The L⁴ Sobolev representative is the same actual base function as its L² representative of the intrinsic first-jet completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_7
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.sobolevRepresentative_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.sobolevRepresentative_probability
theorem scalarH1BaseL4_toL2 (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (u : scalarH1 d) :
    scalarL4ToL2 (normalizedVolume g) (scalarH1BaseL4 g o d u) = scalarH1BaseValue g o d u := by
  have he : (scalarL4ToL2 (normalizedVolume g)).comp (scalarH1BaseL4 g o d) =
      scalarH1BaseValue g o d := by
    apply DFunLike.ext'
    apply ((scalarL4ToL2 (normalizedVolume g)).comp (scalarH1BaseL4 g o d)).continuous.ext_on
      (smoothScalarH1Map_dense o d) (scalarH1BaseValue g o d).continuous
    rintro _ ⟨a, rfl⟩
    change scalarL4ToL2 (normalizedVolume g) (scalarH1BaseL4 g o d (smoothScalarToH1 d a)) =
      scalarH1BaseValue g o d (smoothScalarToH1 d a)
    rw [scalarH1BaseL4_smooth, scalarH1BaseValue_smooth]
    apply Lp.ext
    exact (scalarL4ToL2_coe (normalizedVolume g) _).trans
      ((smoothScalarBaseL4_coe g a).trans
        (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
          (smoothScalarContinuous a)).symm)
  exact congrArg (fun T : scalarH1 d →L[ℝ] Lp ℝ 2 (normalizedVolume g) => T u) he

theorem scalarH1BaseL4_coe (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (u : scalarH1 d) :
    scalarH1BaseL4 g o d u =ᵐ[normalizedVolume g] scalarH1BaseValue g o d u := by
  rw [← scalarH1BaseL4_toL2 g o d u]
  exact (scalarL4ToL2_coe (normalizedVolume g) _).symm

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

theorem scalarChartValue_memLp_four (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (b : Lp ℝ 2 (normalizedVolume g)) (hb : MemLp (b : M → ℝ) 4 (normalizedVolume g)) :
    MemLp (scalarChartValue g c hK hKt b : FourSpace → ℝ) 4 (volume.restrict K) := by
  have hexp : (4 : ℝ≥0∞) / 2 = 2 := by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
    exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  have hb2 : MemLp (fun x => ‖b x‖ ^ (2 : ℕ)) 2 (normalizedVolume g) := by
    simpa only [hexp, ENNReal.toReal_ofNat, Real.rpow_ofNat] using hb.norm_rpow_div 2
  obtain ⟨C, hC, hc⟩ := scalarChart_eLpNorm_bound g c hK hKt
  have hl2 : MemLp (fun z => ‖b ((chartAt FourSpace c).symm z)‖ ^ (2 : ℕ))
      2 (volume.restrict K) :=
    ⟨((((Lp.stronglyMeasurable b).norm.pow 2).measurable).comp_aemeasurable
        (((chartAt FourSpace c).continuousOn_symm.mono hKt).aemeasurable
          hK.isClosed.measurableSet)).aestronglyMeasurable,
      (hc (fun x => ‖b x‖ ^ (2 : ℕ))).trans_lt
        (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) hb2.2)⟩
  have hv2 : MemLp (fun z => ‖scalarChartValue g c hK hKt b z‖ ^ (2 : ℕ))
      2 (volume.restrict K) := by
    apply (memLp_congr_ae ?_).mp hl2
    filter_upwards [scalarChartValue_coe g c hK hKt b] with z hz
    rw [hz]
  apply (memLp_norm_rpow_iff (p := 4) (q := 2)
    (Lp.aestronglyMeasurable (scalarChartValue g c hK hKt b))
    (by norm_num) (by norm_num)).mp
  simpa only [hexp, ENNReal.toReal_ofNat, Real.rpow_ofNat] using hv2

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.chartValueL4_compact
theorem scalarH1ChartValue_memLp_four (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (u : scalarH1 d) :
    MemLp (scalarH1ChartValue g o d c hK hKt u : FourSpace → ℝ) 4 (volume.restrict K) := by
  apply scalarChartValue_memLp_four g c hK hKt
  exact (memLp_congr_ae (scalarH1BaseL4_coe g o d u)).mp (Lp.memLp _)

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.frameLocalization_compact
/-- The localized weak coordinate derivative, reconstructed in the base volume. -/
def scalarH1LocalizedCoordinate (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    (ρ : SmoothScalar (M := M)) (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source)
    (i : Fin 4) : scalarH1 d →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  (scalarChartReconstruction g c (scalarChartSupport_compact c ρ hs)
      (scalarChartSupport_subset c ρ hs)).comp
    ((scalarLocalL2ProductCLM (scalarChartSupport_compact c ρ hs).isClosed.measurableSet
      (scalarChartCutoff c ρ) (scalarChartCutoff_smooth c ρ hs).continuous
      (scalarChartCutoff_compact c ρ hs) (scalarChartCutoff_support c ρ hs)).comp
      (scalarH1ChartDerivative g o d c (scalarChartSupport_compact c ρ hs)
        (scalarChartSupport_subset c ρ hs) i))

theorem scalarH1LocalizedCoordinate_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    (ρ : SmoothScalar (M := M)) (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source)
    (i : Fin 4) (a : SmoothScalar (M := M)) :
    scalarH1LocalizedCoordinate g o d c ρ hs i (smoothScalarToH1 d a) =ᵐ[normalizedVolume g]
      fun x => ρ.val x * partialDeriv (fun z => a.val ((chartAt FourSpace c).symm z)) i
        (chartAt FourSpace c x) := by
  let K := scalarChartSupport c ρ
  let χ := scalarChartCutoff c ρ
  let D := scalarLocalL2ProductCLM (scalarChartSupport_compact c ρ hs).isClosed.measurableSet
    χ (scalarChartCutoff_smooth c ρ hs).continuous (scalarChartCutoff_compact c ρ hs)
    (scalarChartCutoff_support c ρ hs)
  have he : D (scalarH1ChartDerivative g o d c (scalarChartSupport_compact c ρ hs)
      (scalarChartSupport_subset c ρ hs) i (smoothScalarToH1 d a)) =ᵐ[volume]
      (fun z => χ z * partialDeriv (fun y => a.val ((chartAt FourSpace c).symm y)) i z) := by
    rw [scalarH1ChartDerivative_smooth]
    exact (scalarLocalL2ProductCLM_coe ..).trans
      (scalarLocalL2Product_ae_congr (scalarChartSupport_compact c ρ hs).isClosed.measurableSet
        χ (scalarChartCutoff_support c ρ hs)
        (MemLp.coeFn_toLp (scalarCoordinate_gradient_memLp g c
          (scalarChartSupport_compact c ρ hs) (scalarChartSupport_subset c ρ hs) a i)))
  have hr := scalarChartReconstructionFun_ae g c (scalarChartSupport_compact c ρ hs)
    (scalarChartSupport_subset c ρ hs) he
  have hc := scalarChartReconstruction_coe g c (scalarChartSupport_compact c ρ hs)
    (scalarChartSupport_subset c ρ hs)
    (D (scalarH1ChartDerivative g o d c (scalarChartSupport_compact c ρ hs)
      (scalarChartSupport_subset c ρ hs) i (smoothScalarToH1 d a)))
  filter_upwards [hc, hr] with x hx hx'
  rw [show scalarH1LocalizedCoordinate g o d c ρ hs i (smoothScalarToH1 d a) x =
    scalarChartReconstructionFun c K
      (fun z => χ z * partialDeriv (fun y => a.val ((chartAt FourSpace c).symm y)) i z) x
    from hx.trans hx']
  by_cases hxK : x ∈ (chartAt FourSpace c).symm '' K
  · obtain ⟨z, hz, rfl⟩ := hxK
    rw [scalarChartReconstructionFun_chart c (scalarChartSupport_subset c ρ hs) _ hz,
      (chartAt FourSpace c).right_inv (scalarChartSupport_subset c ρ hs hz)]
    congr 1
    exact indicator_of_mem (scalarChartSupport_subset c ρ hs hz) _
  · have hρ : ρ.val x = 0 := by
      by_contra hn
      have hxt := hs (subset_tsupport ρ.val hn)
      apply hxK
      exact ⟨chartAt FourSpace c x, ⟨x, subset_tsupport ρ.val hn, rfl⟩,
        (chartAt FourSpace c).left_inv hxt⟩
    simp only [scalarChartReconstructionFun, indicator_of_notMem hxK, hρ, zero_mul]

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.frameControl_compact
theorem scalarH1_local_frame_control (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    (ρ : SmoothScalar (M := M)) (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source)
    {B : ℝ} (hB : ∀ x, |ρ.val x| ≤ B) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ z ∈ scalarChartSupport c ρ, ∀ j k, |chartGramMatrix g c 1 z j k| ≤ C)
    (u : scalarH1 d) (i : Fin 4) :
    |scalarH1LocalizedFrame g o d ρ hB i u| ≤
      (4 * C) • ∑ j : Fin 4, |scalarBasePullback g o
        (scalarH1LocalizedCoordinate g o d c ρ hs j u)| := by
  let A := scalarH1LocalizedFrame g o d ρ hB i
  let D := fun j => (scalarBasePullback g o).toContinuousLinearMap.comp
    (scalarH1LocalizedCoordinate g o d c ρ hs j)
  apply scalarL2_closed_domination A D (4 * C) (smoothScalarH1Map o d)
    (smoothScalarH1Map_dense o d) _ u
  intro a
  apply (Lp.coeFn_le _ _).mp
  have hD (j : Fin 4) : D j (smoothScalarToH1 d a) =ᵐ[canonicalFrameMeasure g o]
      fun e => ρ.val e.base * partialDeriv (fun z => a.val ((chartAt FourSpace c).symm z)) j
        (chartAt FourSpace c e.base) := by
    have ht := (canonicalFrameMeasure_base g o).quasiMeasurePreserving.ae
      (scalarH1LocalizedCoordinate_smooth g o d c ρ hs j a)
    exact (Lp.coeFn_compMeasurePreserving
      (scalarH1LocalizedCoordinate g o d c ρ hs j (smoothScalarToH1 d a))
      (canonicalFrameMeasure_base g o)).trans ht
  have hDa : ∀ᵐ e ∂canonicalFrameMeasure g o, ∀ j : Fin 4,
      |D j (smoothScalarToH1 d a)| e =
        |ρ.val e.base * partialDeriv (fun z => a.val ((chartAt FourSpace c).symm z)) j
          (chartAt FourSpace c e.base)| := by
    apply eventually_all.mpr
    intro j
    exact (Lp.coeFn_abs _).trans ((hD j).mono fun e he => congrArg abs he)
  filter_upwards [scalarH1LocalizedFrame_smooth g o d ρ hB i a,
    Lp.coeFn_abs (A (smoothScalarToH1 d a)), hDa,
    Lp.coeFn_smul (4 * C) (∑ j : Fin 4, |D j (smoothScalarToH1 d a)|),
    Lp.coeFn_finsetSum Finset.univ (fun j : Fin 4 => |D j (smoothScalarToH1 d a)|)]
      with e hA habs hDall hsm hsum
  change |A (smoothScalarToH1 d a)| e ≤
    ((4 * C) • ∑ j : Fin 4, |D j (smoothScalarToH1 d a)|) e
  rw [habs, hA, hsm]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  change |ρ.val e.base * scalarGradient g a.val e i| ≤
    4 * C * ∑ j, |D j (smoothScalarToH1 d a)| e
  simp_rw [hDall]
  by_cases hρ : ρ.val e.base = 0
  · simp only [hρ, zero_mul, abs_zero, Finset.sum_const_zero, mul_zero, le_refl]
  · have hxs := hs (subset_tsupport ρ.val hρ)
    have hzK : chartAt FourSpace c e.base ∈ scalarChartSupport c ρ :=
      ⟨e.base, subset_tsupport ρ.val hρ, rfl⟩
    let z : ChartTarget c := ⟨chartAt FourSpace c e.base, (chartAt FourSpace c).map_source hxs⟩
    have he : e.base = (chartAt FourSpace c).symm z :=
      ((chartAt FourSpace c).left_inv hxs).symm
    have hb := scalar_frame_gradient_abs_le_chart g a c z e he C hC (hE _ hzK) i
    calc
      _ = |ρ.val e.base| * |scalarGradient g a.val e i| := abs_mul _ _
      _ ≤ |ρ.val e.base| * (4 * C * ∑ j,
          |partialDeriv (fun y => a.val ((chartAt FourSpace c).symm y)) j z|) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = _ := by
        simp_rw [abs_mul]
        rw [← Finset.mul_sum]
        ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rescaled forcing is H1 whenever its intrinsic source is H1. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped Manifold ContDiff SchwartzMap ENNReal

noncomputable section

local notation "V" => FourSpace
local notation "T" => 𝓢'(V, ℂ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.h1Source_compact
theorem scalarChartSourceL2_memSobolev_one (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    (f : scalarH1 d) (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (ht : tsupport χ ⊆ (chartAt FourSpace c).target) :
    MemSobolev 1 2 (scalarComplexL2
      (scalarChartSourceL2 g c (scalarH1BaseValue g o d f) χ hχ hc ht) : T) := by
  have heq : scalarChartSourceL2 g c (scalarH1BaseValue g o d f) χ hχ hc ht =
      scalarWeightedChartL2 g o d c hc ht f χ hχ hc (Subset.refl _) := by
    apply Lp.ext
    exact (scalarChartSourceL2_coe g c (scalarH1BaseValue g o d f) χ hχ hc ht).trans
      (scalarWeightedChartL2_coe g o d c hc ht f χ hχ hc (Subset.refl _)).symm
  rw [heq]
  exact scalarWeightedChartL2_memSobolev_one g o d c hc ht f χ hχ hc (Subset.refl _)

theorem scalarRescaledSourceL2_memSobolev_one (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    (f : scalarH1 d) (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (ht : tsupport χ ⊆ (chartAt FourSpace c).target)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) :
    MemSobolev 1 2 (scalarComplexL2
      (scalarRescaledSourceL2 g c (scalarH1BaseValue g o d f) χ hχ hc ht z₀ r hr) : T) := by
  rw [scalarRescaledSourceL2, scalarComplexL2_real_smul_distribution]
  have h := scalarAffinePullbackL2_memSobolev_one
    (scalarRescalingLinearEquiv g c z₀ r hr) z₀
    (scalarChartSourceL2 g c (scalarH1BaseValue g o d f) χ hχ hc ht)
    (scalarChartSourceL2_memSobolev_one g o d c f χ hχ hc ht)
  exact h.smul ((r ^ 2 : ℝ) : ℂ)

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

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.localL2Regularity_frameCompact
theorem scalar_local_weighted_H2 (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : Lp ℝ 2 (normalizedVolume g)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (scalarBasePullback g o f)
          (scalarH1Value d v))) (c : M) (z₀ : ChartTarget c) :
    ∃ r : ℝ, 0 < r ∧
      (∀ y ∈ closedBall (0 : V) 1,
        scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target) ∧
      ∃ w : Lp ℝ 2 (volume : Measure V),
        (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
          scalarH1BaseValue g o d u
            ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
              volume.restrict (ball (0 : V) 1)] w ∧
        ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
          tsupport (φ : V → ℂ) ⊆ closedBall 0 (1 / 2) →
          MemSobolev 2 2 (smulLeftCLM ℂ φ (scalarComplexL2 w : T)) := by
  obtain ⟨χ, hχ, hc, ht, η₁, hη₁, hchart⟩ := exists_scalar_chart_cutoff g c z₀
  obtain ⟨η₂, hη₂, hcoeff⟩ := scalarRescaledAdjointSchwartz_small g c z₀
    scalarCoefficientBump scalarCoefficientBump.contDiff scalarCoefficientBump.hasCompactSupport
  let r := min η₁ η₂ / 2
  have hr : 0 < r := half_pos (lt_min hη₁ hη₂)
  have hr₁ : |r| < η₁ := by
    rw [abs_of_pos hr]
    exact (half_lt_self (lt_min hη₁ hη₂)).trans_le (min_le_left _ _)
  have hr₂ : |r| < η₂ := by
    rw [abs_of_pos hr]
    exact (half_lt_self (lt_min hη₁ hη₂)).trans_le (min_le_right _ _)
  obtain ⟨a, b, ha, hb, ha₀, ha₁, ha₂, hb₀, hb₁⟩ := hcoeff r hr₂
  let A := scalarRescalingLinearEquiv g c z₀ r hr.ne'
  let w₀ := scalarWeightedChartL2 g o d c hc ht u χ hχ hc (Subset.refl _)
  let w := scalarAffinePullbackL2 A z₀ w₀
  have hW : MemSobolev 1 2 (scalarComplexL2 w : T) :=
    scalarAffinePullbackL2_memSobolev_one A z₀ w₀
      (scalarWeightedChartL2_memSobolev_one g o d c hc ht u χ hχ hc (Subset.refl _))
  have htarget (y : V) (hy : y ∈ ball (0 : V) 1) :
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target :=
    (hchart r hr₁ y (ball_subset_closedBall hy)).1
  have hA (y : V) (hy : y ∈ ball (0 : V) 1) (i j : Fin 4) : a i j y =
      ((-((2 * Real.pi) ^ 2)⁻¹ *
        (scalarRescaledPrincipal g c z₀ r y i j - (1 : Mat4) i j) : ℝ) : ℂ) := by
    have h := ha i j y
    simpa only [scalarCutoffPrincipal, scalarCoefficientBump_one (ball_subset_closedBall hy),
      one_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg] using h
  have hB (y : V) (hy : y ∈ ball (0 : V) 1) (i : Fin 4) : b i y =
      ((-((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledDrift g c z₀ r y i : ℝ) : ℂ) := by
    have h := hb i y
    simpa only [scalarCutoffDrift, scalarCoefficientBump_one (ball_subset_closedBall hy),
      one_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg] using h
  let F := scalarRescaledSourceL2 g c f χ hχ hc ht z₀ r hr.ne'
  have hreal (ψ : V → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
      (hψs : tsupport ψ ⊆ ball (0 : V) 1) :
      (∫ y, w y * scalarRescaledOperator g c z₀ r ψ y) = ∫ y, F y * ψ y := by
    rw [scalarRescaled_L2_test_equation g o d f u hw c hc ht χ hχ hc (Subset.refl _)
      z₀ r hr.ne' ψ hψ hψc (fun y hy => htarget y (hψs hy))
      (fun y hy => (hchart r hr₁ y (ball_subset_closedBall (hψs hy))).2)]
    exact (scalarRescaledSourceL2_pairing g c f χ hχ hc ht z₀ r hr.ne' ψ
      (fun y hy => (hchart r hr₁ y (ball_subset_closedBall (hψs hy))).2)).symm
  have htests (φ : S) (hφc : HasCompactSupport (φ : V → ℂ))
      (hφs : tsupport (φ : V → ℂ) ⊆ ball 0 1) :
      (scalarPerturbedOperator a (scalarAdjointDrift a b) (scalarComplexL2 w : T) -
          (scalarComplexL2 w : T) - smulLeftCLM ℂ (-scalarAdjointPotential a b : S)
            (scalarComplexL2 w : T)) φ =
        ∫ y, φ y * ((-((2 * Real.pi) ^ 2)⁻¹ * F y : ℝ) : ℂ) := by
    rw [scalarFormalAdjointOperator_remainder]
    exact scalar_normalized_adjoint_test_equation_of_integrable g c z₀ r F w a b
      (ball 0 1) hA hB hreal φ hφc hφs (scalar_real_L2_test_integrable F φ _)
  refine ⟨r, hr, fun y hy => (hchart r hr₁ y hy).1, w, ?_, ?_⟩
  ·
    have hmp : Measure.QuasiMeasurePreserving (fun y : V => A y + z₀) volume volume := by
      refine ⟨by fun_prop, ?_⟩
      rw [scalarAffine_map_volume]
      exact Measure.smul_absolutelyContinuous
    have hbase := hmp.ae_eq_comp (scalarWeightedChartL2_coe g o d c hc ht u χ hχ hc (Subset.refl _))
    have hwr := scalarAffinePullbackL2_coe A z₀ w₀
    filter_upwards [ae_restrict_of_ae hbase, ae_restrict_of_ae hwr,
      ae_restrict_mem isOpen_ball.measurableSet] with y hbq hwq hy
    have hy₁ : y ∈ closedBall (0 : V) 1 := ball_subset_closedBall hy
    have hp := scalarRescalingLinearEquiv_apply g c z₀ r hr.ne' y
    dsimp only [Function.comp_apply] at hbq
    change w₀ (A y + z₀) = _ at hbq
    rw [hp, (hchart r hr₁ y hy₁).2, one_mul] at hbq
    change w y = w₀ (A y + z₀) at hwq
    rw [hp] at hwq
    exact (hwq.trans hbq).symm
  · intro φ hφc hφs
    exact scalar_ball_L2_forcing_gain a (scalarAdjointDrift a b)
      scalarEllipticSmallSize scalarEllipticSmallSize_pos.le ha₀ ha₁ ha₂ hb₀ hb₁
      scalarEllipticSmallSize_small (-scalarAdjointPotential a b)
      (scalarComplexL2 w : T) (fun y => ((-((2 * Real.pi) ^ 2)⁻¹ * F y : ℝ) : ℂ))
      (((Lp.memLp F).const_mul _).ofReal) hW htests
      (1 / 2) (by norm_num) (by norm_num) φ hφc hφs

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual Lp representatives and convergence in the subcritical range.
The inclusion uses the same almost-everywhere function; the convergence
statement combines small L² norm with a bounded L⁴ norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_13
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.subcriticalEmbedding_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.subcriticalEmbedding_probability
def scalarH1BaseLp (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≤ 4) :
    scalarH1 d →L[ℝ] Lp ℝ p (normalizedVolume g) :=
  (scalarL4ToLp (normalizedVolume g) p hp).comp (scalarH1BaseL4 g o d)

theorem scalarH1BaseLp_coe (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≤ 4) (u : scalarH1 d) :
    scalarH1BaseLp g o d p hp u =ᵐ[normalizedVolume g] scalarH1BaseValue g o d u :=
  scalarH1BaseL4_coe g o d u

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.l4Transfer_compact
theorem scalarH1LocalizedFrame_memLp_four (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    (ρ : SmoothScalar (M := M)) (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source)
    {B : ℝ} (hB : ∀ x, |ρ.val x| ≤ B) (u : scalarH1 d)
    (hD : ∀ j, MemLp (scalarH1LocalizedCoordinate g o d c ρ hs j u : M → ℝ)
      4 (normalizedVolume g)) (i : Fin 4) :
    MemLp (scalarH1LocalizedFrame g o d ρ hB i u : FrameBundle g → ℝ)
      4 (canonicalFrameMeasure g o) := by
  obtain ⟨C, hC, hE⟩ := scalar_chart_gram_bounded g c
    (scalarChartSupport_compact c ρ hs) (scalarChartSupport_subset c ρ hs)
  exact scalarL2_memLp_four_of_domination _ _ (4 * C)
    (scalarH1_local_frame_control g o d c ρ hs hB C hC hE u i)
    (fun j => scalarBasePullback_memLp_four g o _ (hD j))

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

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.localH1Regularity_frameCompact
theorem scalar_local_weighted_H3 (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : scalarH1 d) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (scalarH1Value d f)
          (scalarH1Value d v))) (c : M) (z₀ : ChartTarget c) :
    ∃ r : ℝ, 0 < r ∧
      (∀ y ∈ closedBall (0 : V) 1,
        scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target) ∧
      ∃ w : Lp ℝ 2 (volume : Measure V),
        (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
          scalarH1BaseValue g o d u
            ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
              volume.restrict (ball (0 : V) 1)] w ∧
        ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
          tsupport (φ : V → ℂ) ⊆ closedBall 0 (1 / 2) →
          MemSobolev 3 2 (smulLeftCLM ℂ φ (scalarComplexL2 w : T)) := by
  obtain ⟨χ, hχ, hc, ht, η₁, hη₁, hchart⟩ := exists_scalar_chart_cutoff g c z₀
  obtain ⟨η₂, hη₂, hcoeff⟩ := scalarRescaledAdjointSchwartz_small g c z₀
    scalarCoefficientBump scalarCoefficientBump.contDiff scalarCoefficientBump.hasCompactSupport
  let r := min η₁ η₂ / 2
  have hr : 0 < r := half_pos (lt_min hη₁ hη₂)
  have hr₁ : |r| < η₁ := by
    rw [abs_of_pos hr]
    exact (half_lt_self (lt_min hη₁ hη₂)).trans_le (min_le_left _ _)
  have hr₂ : |r| < η₂ := by
    rw [abs_of_pos hr]
    exact (half_lt_self (lt_min hη₁ hη₂)).trans_le (min_le_right _ _)
  obtain ⟨a, b, ha, hb, ha₀, ha₁, ha₂, hb₀, hb₁⟩ := hcoeff r hr₂
  let A := scalarRescalingLinearEquiv g c z₀ r hr.ne'
  let w₀ := scalarWeightedChartL2 g o d c hc ht u χ hχ hc (Subset.refl _)
  let w := scalarAffinePullbackL2 A z₀ w₀
  have hW : MemSobolev 1 2 (scalarComplexL2 w : T) :=
    scalarAffinePullbackL2_memSobolev_one A z₀ w₀
      (scalarWeightedChartL2_memSobolev_one g o d c hc ht u χ hχ hc (Subset.refl _))
  have htarget (y : V) (hy : y ∈ ball (0 : V) 1) :
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target :=
    (hchart r hr₁ y (ball_subset_closedBall hy)).1
  have hA (y : V) (hy : y ∈ ball (0 : V) 1) (i j : Fin 4) : a i j y =
      ((-((2 * Real.pi) ^ 2)⁻¹ *
        (scalarRescaledPrincipal g c z₀ r y i j - (1 : Mat4) i j) : ℝ) : ℂ) := by
    have h := ha i j y
    simpa only [scalarCutoffPrincipal, scalarCoefficientBump_one (ball_subset_closedBall hy),
      one_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg] using h
  have hB (y : V) (hy : y ∈ ball (0 : V) 1) (i : Fin 4) : b i y =
      ((-((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledDrift g c z₀ r y i : ℝ) : ℂ) := by
    have h := hb i y
    simpa only [scalarCutoffDrift, scalarCoefficientBump_one (ball_subset_closedBall hy),
      one_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg] using h
  let F := scalarRescaledSourceL2 g c (scalarH1BaseValue g o d f) χ hχ hc ht z₀ r hr.ne'
  have hreal (ψ : V → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
      (hψs : tsupport ψ ⊆ ball (0 : V) 1) :
      (∫ y, w y * scalarRescaledOperator g c z₀ r ψ y) = ∫ y, F y * ψ y := by
    rw [scalarRescaled_L2_test_equation g o d (scalarH1BaseValue g o d f) u
      (by simpa only [scalarH1BaseValue_spec] using hw) c hc ht χ hχ hc (Subset.refl _)
      z₀ r hr.ne' ψ hψ hψc (fun y hy => htarget y (hψs hy))
      (fun y hy => (hchart r hr₁ y (ball_subset_closedBall (hψs hy))).2)]
    exact (scalarRescaledSourceL2_pairing g c (scalarH1BaseValue g o d f) χ hχ hc ht z₀ r hr.ne' ψ
      (fun y hy => (hchart r hr₁ y (ball_subset_closedBall (hψs hy))).2)).symm
  let κ : ℝ := -((2 * Real.pi) ^ 2)⁻¹
  let Ft := scalarComplexL2 (κ • F)
  have hFt : MemSobolev 1 2 (Ft : T) := by
    rw [show (Ft : T) = (κ : ℂ) • (scalarComplexL2 F : T) from
      scalarComplexL2_real_smul_distribution κ F]
    exact (scalarRescaledSourceL2_memSobolev_one g o d c f χ hχ hc ht z₀ r hr.ne').smul (κ : ℂ)
  have hpair (φ : S) : (Ft : T) φ = ∫ y, φ y * ((κ * F y : ℝ) : ℂ) := by
    rw [Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [scalarComplexL2_coe (κ • F), Lp.coeFn_smul κ F] with y hc hs
    rw [hc, hs]
    rfl
  have htests (φ : S) (hφc : HasCompactSupport (φ : V → ℂ))
      (hφs : tsupport (φ : V → ℂ) ⊆ ball 0 1) :
      (scalarPerturbedOperator a (scalarAdjointDrift a b) (scalarComplexL2 w : T) -
          (scalarComplexL2 w : T) - smulLeftCLM ℂ (-scalarAdjointPotential a b : S)
            (scalarComplexL2 w : T)) φ =
        (Ft : T) φ := by
    rw [scalarFormalAdjointOperator_remainder]
    exact (scalar_normalized_adjoint_test_equation_of_integrable g c z₀ r F w a b
      (ball 0 1) hA hB hreal φ hφc hφs (scalar_real_L2_test_integrable F φ _)).trans
      (hpair φ).symm
  refine ⟨r, hr, fun y hy => (hchart r hr₁ y hy).1, w, ?_, ?_⟩
  ·
    have hmp : Measure.QuasiMeasurePreserving (fun y : V => A y + z₀) volume volume := by
      refine ⟨by fun_prop, ?_⟩
      rw [scalarAffine_map_volume]
      exact Measure.smul_absolutelyContinuous
    have hbase := hmp.ae_eq_comp (scalarWeightedChartL2_coe g o d c hc ht u χ hχ hc (Subset.refl _))
    have hwr := scalarAffinePullbackL2_coe A z₀ w₀
    filter_upwards [ae_restrict_of_ae hbase, ae_restrict_of_ae hwr,
      ae_restrict_mem isOpen_ball.measurableSet] with y hbq hwq hy
    have hy₁ : y ∈ closedBall (0 : V) 1 := ball_subset_closedBall hy
    have hp := scalarRescalingLinearEquiv_apply g c z₀ r hr.ne' y
    dsimp only [Function.comp_apply] at hbq
    change w₀ (A y + z₀) = _ at hbq
    rw [hp, (hchart r hr₁ y hy₁).2, one_mul] at hbq
    change w y = w₀ (A y + z₀) at hwq
    rw [hp] at hwq
    exact (hwq.trans hbq).symm
  · intro φ hφc hφs
    exact scalar_ball_H1_forcing_gain a (scalarAdjointDrift a b)
      scalarEllipticSmallSize scalarEllipticSmallSize_pos.le ha₀ ha₁ ha₂ hb₀ hb₁
      scalarEllipticSmallSize_small (-scalarAdjointPotential a b)
      (scalarComplexL2 w : T) (Ft : T) hFt hW htests
      (1 / 2) (by norm_num) (by norm_num) φ hφc hφs

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.subcriticalCompactness_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.subcriticalCompactness_probability
/-- Every bounded intrinsic H¹ sequence has a strongly convergent actual
base Lp subsequence for 2 < p < 4. -/
theorem scalarH1_subcritical_subsequence (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (u : ℕ → scalarH1 d) {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ v : Lp ℝ (ENNReal.ofReal p) (normalizedVolume g),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => scalarH1BaseLp g o d (ENNReal.ofReal p)
          (by exact_mod_cast hp4.le) (u (φ n))) atTop (𝓝 v) := by
  have hK := (scalarH1BaseValue_compact g o d).isCompact_closure_image_of_isVonNBounded
    (NormedSpace.isVonNBounded_closedBall ℝ (scalarH1 d) R)
  obtain ⟨v2, _, φ, hφ, hlim⟩ := hK.tendsto_subseq (fun n =>
    subset_closure ⟨u n, by simpa only [Metric.mem_closedBall, dist_zero_right] using hu n, rfl⟩)
  let f : ℕ → Lp ℝ 4 (normalizedVolume g) :=
    fun n => scalarH1BaseL4 g o d (u (φ n))
  have hf : ∀ n, ‖f n‖ ≤ ‖scalarH1BaseL4 g o d‖ * R := fun n =>
    ((scalarH1BaseL4 g o d).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hu (φ n)) (norm_nonneg (scalarH1BaseL4 g o d)))
  have he (n : ℕ) : scalarL4ToLp (normalizedVolume g) 2 (by norm_num) (f n) =
      scalarH1BaseValue g o d (u (φ n)) := by
    apply Lp.ext
    exact scalarH1BaseL4_coe g o d (u (φ n))
  have h2 : CauchySeq (fun n => scalarL4ToLp (normalizedVolume g) 2 (by norm_num) (f n)) := by
    simp_rw [he]
    exact hlim.cauchySeq
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete
    (scalar_subcritical_cauchy_of_L2 (normalizedVolume g) hp hp4 f hf h2)
  exact ⟨v, φ, hφ, hv⟩

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.chartGradientL4_compact
theorem scalarH1_cutoff_coordinate_memLp_four (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (u : scalarH1 d)
    (hH2 : MemSobolev 2 2
      (scalarComplexL2 (scalarH1CutoffValueL2 g o d c hK hKt χ hχ hc hs u) :
        𝓢'(FourSpace, ℂ))) (i : Fin 4) :
    MemLp ((scalarLocalL2ProductCLM hK.isClosed.measurableSet χ hχ.continuous hc hs
      (scalarH1ChartDerivative g o d c hK hKt i u)) : FourSpace → ℝ) 4 volume := by
  let v := scalarH1ChartValue g o d c hK hKt u
  let D := scalarLocalL2ProductCLM hK.isClosed.measurableSet χ hχ.continuous hc hs
    (scalarH1ChartDerivative g o d c hK hKt i u)
  let P := scalarLocalL2PartialProduct hK.isClosed.measurableSet χ hχ hc hs v i
  have hP : MemLp (P : FourSpace → ℝ) 4 volume :=
    scalarLocalL2Product_memLp_four hK.isClosed.measurableSet (partialDeriv χ i)
      (((hχ.fderiv_right (m := ∞) (by simp)).clm_apply
        (contDiff_const (c := coordinateVector i))).continuous)
      (hc.fderiv_apply ℝ (coordinateVector i))
      ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hs) v
      (scalarH1ChartValue_memLp_four g o d c hK hKt u)
  have hsum : scalarH1CutoffDerivative g o d c hK hKt χ hχ hc hs i u = D + P := rfl
  have hfull := scalarH1CutoffDerivative_memLp_four g o d c hK hKt χ hχ hc hs u hH2 i
  rw [hsum] at hfull
  have hd : MemLp (fun x => (D + P) x - P x) 4 volume := hfull.sub hP
  apply (memLp_congr_ae ?_).mp hd
  filter_upwards [Lp.coeFn_add D P] with x hx
  simp only [hx, Pi.add_apply, add_sub_cancel_right, D]

theorem scalarH1LocalizedCoordinate_memLp_four_of_H2
    (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    (ρ : SmoothScalar (M := M)) (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source)
    (u : scalarH1 d)
    (hH2 : MemSobolev 2 2
      (scalarComplexL2 (scalarH1CutoffValueL2 g o d c
        (scalarChartSupport_compact c ρ hs) (scalarChartSupport_subset c ρ hs)
        (scalarChartCutoff c ρ) (scalarChartCutoff_smooth c ρ hs)
        (scalarChartCutoff_compact c ρ hs) (scalarChartCutoff_support c ρ hs) u) :
          𝓢'(FourSpace, ℂ))) (i : Fin 4) :
    MemLp (scalarH1LocalizedCoordinate g o d c ρ hs i u : M → ℝ)
      4 (normalizedVolume g) := by
  apply scalarChartReconstruction_memLp_four g c
    (scalarChartSupport_compact c ρ hs) (scalarChartSupport_subset c ρ hs)
  exact scalarH1_cutoff_coordinate_memLp_four g o d c
    (scalarChartSupport_compact c ρ hs) (scalarChartSupport_subset c ρ hs)
    (scalarChartCutoff c ρ) (scalarChartCutoff_smooth c ρ hs)
    (scalarChartCutoff_compact c ρ hs) (scalarChartCutoff_support c ρ hs) u hH2 i

end
end PositiveEinsteinFour.Geometry
end


section

/-! The subcritical Sobolev operator on the Hilbert space whose squared
norm is the exact normalized energy in the manuscript. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.sobolevExtremal_frameCompact
local instance sobolevExtremal_probability_rc90d1f_1 (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
def scalarWeightedBaseLp (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≤ 4) :
    scalarWeightedH1 d →L[ℝ] Lp ℝ p (normalizedVolume g) :=
  (scalarH1BaseLp g o d p hp).comp (scalarWeightedH1ToH1 d)

theorem scalarWeightedBaseLp_coe (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≤ 4) (u : scalarWeightedH1 d) :
    scalarWeightedBaseLp g o d p hp u =ᵐ[normalizedVolume g]
      scalarH1BaseValue g o d (scalarWeightedH1ToH1 d u) :=
  scalarH1BaseLp_coe g o d p hp _

theorem scalarWeighted_subcritical_subsequence (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (u : ℕ → scalarWeightedH1 d) {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ v : Lp ℝ (ENNReal.ofReal p) (normalizedVolume g),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => scalarWeightedBaseLp g o d (ENNReal.ofReal p)
          (by exact_mod_cast hp4.le) (u (φ n))) atTop (𝓝 v) := by
  have hbound : ∀ n, ‖scalarWeightedH1ToH1 d (u n)‖ ≤ ‖scalarWeightedH1ToH1 d‖ * R :=
    fun n => ((scalarWeightedH1ToH1 d).le_opNorm (u n)).trans
      (mul_le_mul_of_nonneg_left (hu n) (norm_nonneg (scalarWeightedH1ToH1 d)))
  exact scalarH1_subcritical_subsequence g o d hp hp4
    (fun n => scalarWeightedH1ToH1 d (u n)) hbound

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.variationalMinimum_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.variationalMinimum_probability
theorem scalarWeightedBaseLp_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≤ 4) (a : SmoothScalar (M := M)) :
    scalarWeightedBaseLp g o d p hp (smoothScalarToWeightedH1 d a) =ᵐ[normalizedVolume g]
      a.val := by
  have h := scalarWeightedBaseLp_coe g o d p hp (smoothScalarToWeightedH1 d a)
  rw [scalarWeightedH1ToH1_smooth, scalarH1BaseValue_smooth] at h
  exact h.trans (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
    (⟨a.val, a.property.continuous⟩ : C(M, ℝ)))

theorem scalarWeightedBaseLp_ne_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≤ 4) :
    scalarWeightedBaseLp g o d p hp ≠ 0 := by
  intro hz
  have h := scalarWeightedBaseLp_smooth g o d p hp (smoothScalarConst 1)
  rw [hz, zero_apply] at h
  have he := (Lp.coeFn_zero ℝ p (normalizedVolume g)).symm.trans h
  obtain ⟨x, hx⟩ := he.exists
  exact zero_ne_one hx

/-- The actual subcritical Sobolev operator attains its norm. -/
theorem scalarWeighted_subcritical_extremal (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4) :
    ∃ u : scalarWeightedH1 d, ‖u‖ = 1 ∧
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) u‖ =
        ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le)‖ := by
  let T := scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le)
  have hT : 0 < ‖T‖ := by
    by_contra h
    have hn : ‖T‖ ≤ 0 := le_of_not_gt h
    apply scalarWeightedBaseLp_ne_zero g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le)
    apply ContinuousLinearMap.ext
    intro v
    change T v = 0
    apply norm_eq_zero.mp
    exact le_antisymm ((T.le_opNorm v).trans
      (mul_nonpos_of_nonpos_of_nonneg hn (norm_nonneg v))) (norm_nonneg _)
  have hx (n : ℕ) : ∃ x : scalarWeightedH1 d,
      ‖x‖ < 1 ∧ ‖T‖ - 1 / ((n : ℝ) + 1) < ‖T x‖ :=
    T.exists_lt_apply_of_lt_opNorm (sub_lt_self _ (by positivity))
  choose u hu hTu using hx
  have hnorm : Tendsto (fun n => ‖T (u n)‖) atTop (𝓝 ‖T‖) := by
    have hlo : Tendsto (fun n : ℕ => ‖T‖ - 1 / ((n : ℝ) + 1)) atTop (𝓝 ‖T‖) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
      (fun n => (hTu n).le) (fun n => T.unit_le_opNorm _ (hu n).le)
  obtain ⟨y, φ, hφ, hlim⟩ := scalarWeighted_subcritical_subsequence g o d hp hp4 u
    (fun n => (hu n).le)
  have hy : ‖y‖ = ‖T‖ := tendsto_nhds_unique hlim.norm (hnorm.comp hφ.tendsto_atTop)
  have hc := scalar_extremizing_sequence_cauchy T hT (u ∘ φ)
    (fun n => (hu (φ n)).le) y hlim hy
  obtain ⟨x, hxlim⟩ := cauchySeq_tendsto_of_complete hc
  have hxle : ‖x‖ ≤ 1 := le_of_tendsto hxlim.norm (Eventually.of_forall (fun n => (hu (φ n)).le))
  have hTx : T x = y := tendsto_nhds_unique (T.continuous.tendsto x |>.comp hxlim) hlim
  refine ⟨x, le_antisymm hxle ?_, by rw [hTx, hy]⟩
  have hbound := T.le_opNorm x
  rw [hTx, hy] at hbound
  nlinarith

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normalizedMinimum_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normalizedMinimum_probability
theorem scalarWeightedBaseLp_one (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≤ 4) :
    scalarWeightedBaseLp g o d p hp (smoothScalarToWeightedH1 d (smoothScalarConst 1)) =
      Lp.const p (normalizedVolume g) (1 : ℝ) := by
  apply Lp.ext
  exact (scalarWeightedBaseLp_smooth g o d p hp (smoothScalarConst 1)).trans
    (Lp.coeFn_const p (normalizedVolume g) (1 : ℝ)).symm

/-- The normalized actual subcritical minimum is positive, at most one, and
bounds the homogeneous energy of every completed scalar first jet. -/
theorem scalar_subcritical_normalized_minimum (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4) :
    ∃ w : scalarWeightedH1 d,
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1 ∧
      0 < ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ 1 ∧
      ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
        ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2
          ≤ ‖v‖ ^ 2 := by
  let T := scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le)
  have hT : 0 < ‖T‖ := by
    by_contra h
    have hn : ‖T‖ ≤ 0 := le_of_not_gt h
    apply scalarWeightedBaseLp_ne_zero g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le)
    apply ContinuousLinearMap.ext
    intro v
    change T v = 0
    apply norm_eq_zero.mp
    exact le_antisymm ((T.le_opNorm v).trans
      (mul_nonpos_of_nonpos_of_nonneg hn (norm_nonneg v))) (norm_nonneg _)
  obtain ⟨x, hx, hTx⟩ := scalarWeighted_subcritical_extremal g o d hp hp4
  obtain ⟨w, hw, hwpos, hmin⟩ := scalar_normalize_extremal T hT x hx hTx
  refine ⟨w, hw, hwpos, ?_, hmin⟩
  have h := hmin (smoothScalarToWeightedH1 d (smoothScalarConst 1))
  have hnorm : ‖T (smoothScalarToWeightedH1 d (smoothScalarConst 1))‖ = 1 := by
    rw [show T (smoothScalarToWeightedH1 d (smoothScalarConst 1)) =
      Lp.const (ENNReal.ofReal p) (normalizedVolume g) (1 : ℝ) from
        scalarWeightedBaseLp_one g o d _ _]
    rw [Lp.norm_const _ _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith)))]
    simp only [norm_one, probReal_univ, Real.one_rpow, mul_one]
  simpa only [hnorm, one_pow, mul_one, smoothScalarToWeightedH1_one_norm_sq g o d] using h

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

theorem scalarBaseHeat_add (t s : ℝ≥0) (f : Lp ℝ 2 (normalizedVolume g)) :
    scalarBaseHeat g o d (t + s) f = scalarBaseHeat g o d t (scalarBaseHeat g o d s f) := by
  apply (scalarBaseSpectralEquiv g o d).injective
  apply lp.ext
  funext μ
  rw [scalarBaseHeat_coordinate, scalarBaseHeat_coordinate, scalarBaseHeat_coordinate, smul_smul]
  congr 1
  simp only [scalarBaseHeatWeight, NNReal.coe_add]
  rw [← Real.exp_add]
  congr 1
  ring

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarLpAbs_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarLpAbs_probability
theorem scalarWeightedBaseLp_absRegularized_error (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hp : p ≤ 4) (a : SmoothScalar (M := M)) (ε : ℝ) (hε : 0 < ε) :
    ‖scalarWeightedBaseLp g o d p hp
        (smoothScalarToWeightedH1 d (smoothScalarAbsRegularized a ε hε)) -
      scalarLpAbs (scalarWeightedBaseLp g o d p hp (smoothScalarToWeightedH1 d a))‖ ≤ ε := by
  let T := scalarWeightedBaseLp g o d p hp
  have hb : ‖T (smoothScalarToWeightedH1 d (smoothScalarAbsRegularized a ε hε)) -
      scalarLpAbs (T (smoothScalarToWeightedH1 d a))‖ ≤
        ‖Lp.const p (normalizedVolume g) ε‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub
      (T (smoothScalarToWeightedH1 d (smoothScalarAbsRegularized a ε hε)))
      (scalarLpAbs (T (smoothScalarToWeightedH1 d a))),
      scalarWeightedBaseLp_smooth g o d p hp (smoothScalarAbsRegularized a ε hε),
      scalarLpAbs_coe (T (smoothScalarToWeightedH1 d a)),
      scalarWeightedBaseLp_smooth g o d p hp a,
      Lp.coeFn_const p (normalizedVolume g) ε] with x hsub hreg habs ha hc
    simp only [Pi.sub_apply] at hsub
    rw [hsub, hreg, habs, ha, hc]
    simpa only [Real.norm_eq_abs, Function.const_apply, abs_of_pos hε] using
      smoothScalarAbsRegularized_error a ε hε x
  have hn : ‖Lp.const p (normalizedVolume g) ε‖ = ε := by
    rw [Lp.norm_const _ _ _ (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p)))]
    simp only [Real.norm_eq_abs, abs_of_pos hε, probReal_univ, Real.one_rpow, mul_one]
  exact hb.trans_eq hn

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarEuler_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarEuler_probability
/-- The actual weak Euler equation for a normalized subcritical minimum,
against every smooth scalar test function. -/
theorem scalar_subcritical_minimum_weak_euler (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (a : SmoothScalar (M := M)) :
    inner ℝ w (smoothScalarToWeightedH1 d a) = ‖w‖ ^ 2 *
      ∫ x, |scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x| ^
        (p - 2) * scalarWeightedBaseLp g o d (ENNReal.ofReal p)
          (by exact_mod_cast hp4.le) w x * a.val x ∂normalizedVolume g := by
  let T := scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le)
  have hvar := scalarLpNormSq_hasDerivAt_continuous hp (T w)
    (T (smoothScalarToWeightedH1 d a)) hw
    (⟨a.val, a.property.continuous⟩ : C(M, ℝ)) (scalarWeightedBaseLp_smooth g o d _ _ a)
  apply scalar_energy_minimum_euler T w (smoothScalarToWeightedH1 d a) hw hmin
  simpa only [T, map_add, map_smul, ContinuousMap.coe_mk] using hvar

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.katoTesting_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.katoTesting_probability
/-- Admissibility and the exact nonlinear Euler identity for a rational
test of an actual homogeneous minimum. -/
theorem scalar_minimum_kato_test (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hmin : ∀ z : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) z‖ ^ 2 ≤ ‖z‖ ^ 2)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ v : scalarH1 d,
      scalarH1BaseValue g o d v =ᵐ[normalizedVolume g]
        (fun x => scalarKatoTest lam
          (scalarH1BaseValue g o d (scalarWeightedH1ToH1 d w) x)) ∧
      (∀ i : Fin 4, scalarH1Gradient d i v =ᵐ[canonicalFrameMeasure g o]
        fun e => scalarKatoTestRate lam (scalarH1Value d (scalarWeightedH1ToH1 d w) e) *
          scalarH1Gradient d i (scalarWeightedH1ToH1 d w) e) ∧
      inner ℝ w (scalarWeightedH1Equiv d v) = ‖w‖ ^ 2 *
        ∫ x, |scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x| ^
          (p - 2) * scalarWeightedBaseLp g o d (ENNReal.ofReal p)
            (by exact_mod_cast hp4.le) w x *
          scalarKatoTest lam (scalarWeightedBaseLp g o d (ENNReal.ofReal p)
            (by exact_mod_cast hp4.le) w x) ∂normalizedVolume g := by
  let T := scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le)
  let u := scalarWeightedH1ToH1 d w
  obtain ⟨v, hv, hgrad⟩ := scalarH1_katoTest_base_exists g o d hlam u
  have hvalue : (T (scalarWeightedH1Equiv d v) : M → ℝ) =ᵐ[normalizedVolume g]
      fun x => scalarKatoTest lam (T w x) := by
    have hz := scalarWeightedBaseLp_coe g o d (ENNReal.ofReal p)
      (by exact_mod_cast hp4.le) (scalarWeightedH1Equiv d v)
    simp only [scalarWeightedH1ToH1_equiv] at hz
    have hu := scalarWeightedBaseLp_coe g o d (ENNReal.ofReal p)
      (by exact_mod_cast hp4.le) w
    filter_upwards [hz, hu, hv] with x hx hy hvx
    exact hx.trans (hvx.trans (congrArg (scalarKatoTest lam) hy.symm))
  have hb : ∀ᵐ x ∂normalizedVolume g,
      |T (scalarWeightedH1Equiv d v) x| ≤ lam⁻¹ * |T w x| := by
    filter_upwards [hvalue] with x hx
    rw [hx]
    exact scalarKatoTest_abs_le hlam _
  have hvar := scalarLpRelativeNormSq_hasDerivAt hp (T w)
    (T (scalarWeightedH1Equiv d v)) hw (inv_nonneg.mpr hlam.le) hb
  have he := scalar_energy_minimum_euler T w (scalarWeightedH1Equiv d v) hw hmin _
    (by simpa only [map_add, map_smul] using hvar)
  refine ⟨v, hv, hgrad, ?_⟩
  rw [he]
  congr 1
  apply integral_congr_ae
  filter_upwards [hvalue] with x hx
  rw [hx]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The absolute value of a subcritical extremizer belongs to the actual
energy space and has the same minimum energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped Manifold ContDiff NNReal ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarNonnegative_frameCompact
local instance scalarNonnegative_probability_rc90d1f_1 (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
theorem scalar_subcritical_minimum_absolute (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2) :
    ∃ v : scalarWeightedH1 d,
      scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v =
        scalarLpAbs (scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w) ∧
      ‖v‖ ^ 2 = ‖w‖ ^ 2 := by
  let T := scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le)
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp ((smoothScalarToWeightedH1_dense d) w)
  choose a ha using hu
  have halim : Tendsto (fun n => smoothScalarToWeightedH1 d (a n)) atTop (𝓝 w) := by
    simpa only [ha] using hlim
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let v (n : ℕ) := smoothScalarToWeightedH1 d (smoothScalarAbsRegularized (a n) (ε n) (hε n))
  let y := scalarLpAbs (T w)
  have hy : ‖y‖ = 1 := (scalarLpAbs_norm (T w)).trans hw
  have habslim : Tendsto (fun n => scalarLpAbs (T (smoothScalarToWeightedH1 d (a n))))
      atTop (𝓝 y) := scalarLpAbs_continuous.continuousAt.tendsto.comp
        (T.continuous.continuousAt.tendsto.comp halim)
  have herr : Tendsto (fun n => T (v n) - scalarLpAbs (T (smoothScalarToWeightedH1 d (a n))))
      atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => scalarWeightedBaseLp_absRegularized_error
      g o d _ _ (a n) (ε n) (hε n)) hεlim
  have hvlim : Tendsto (fun n => T (v n)) atTop (𝓝 y) := by
    simpa only [sub_add_cancel, zero_add] using herr.add habslim
  have hlo : Tendsto (fun n => ‖w‖ ^ 2 * ‖T (v n)‖ ^ 2) atTop (𝓝 (‖w‖ ^ 2)) := by
    simpa only [hy, one_pow, mul_one] using (hvlim.norm.pow 2).const_mul (‖w‖ ^ 2)
  have hup : Tendsto (fun n => ‖smoothScalarToWeightedH1 d (a n)‖ ^ 2 + (ε n) ^ 2)
      atTop (𝓝 (‖w‖ ^ 2)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      (halim.norm.pow 2).add (hεlim.pow 2)
  have henergy : Tendsto (fun n => ‖v n‖ ^ 2) atTop (𝓝 (‖w‖ ^ 2)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hup (fun n => hmin (v n))
      (fun n => smoothScalarAbsRegularized_energy_le o d (a n) (ε n) (hε n))
  obtain ⟨z, hz, hznorm, _⟩ := scalar_energy_minimizing_sequence_limit
    T (‖w‖ ^ 2) hmin v y hy hvlim henergy
  exact ⟨z, hz, hznorm⟩

/-- There is a nonnegative normalized weak Euler minimizer in the actual
completed scalar Sobolev space, with positive energy at most one. -/
theorem scalar_subcritical_nonnegative_minimum (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4) :
    ∃ w : scalarWeightedH1 d,
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1 ∧
      0 < ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ 1 ∧
      (∀ᵐ x ∂normalizedVolume g,
        0 ≤ scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x) ∧
      (∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
        ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2) := by
  obtain ⟨u, hu, hu0, hu1, hmin⟩ := scalar_subcritical_normalized_minimum g o d hp hp4
  obtain ⟨w, hw, hnorm⟩ := scalar_subcritical_minimum_absolute g o d hp4 u hu hmin
  refine ⟨w, ?_, hnorm ▸ hu0, hnorm ▸ hu1, ?_, ?_⟩
  · rw [hw, scalarLpAbs_norm]
    exact hu
  · rw [hw]
    exact scalarLpAbs_nonneg _
  · simpa only [hnorm] using hmin

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarSmoothRep_frameCompact
local instance scalarSmoothRep_probability_rc90d1f_1 (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
theorem scalarWeightedBaseLp_injective (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hp : p ≤ 4) : Function.Injective (scalarWeightedBaseLp g o d p hp) := by
  intro u v huv
  have hu := scalarWeightedBaseLp_coe g o d p hp u
  have hv := scalarWeightedBaseLp_coe g o d p hp v
  rw [huv] at hu
  have hb := Lp.ext (hu.symm.trans hv)
  apply (scalarWeightedH1Equiv d).symm.injective
  apply scalarH1Value_injective d
  change scalarH1Value d (scalarWeightedH1ToH1 d u) =
    scalarH1Value d (scalarWeightedH1ToH1 d v)
  rw [← scalarH1BaseValue_spec g o d (scalarWeightedH1ToH1 d u),
    ← scalarH1BaseValue_spec g o d (scalarWeightedH1ToH1 d v), hb]

theorem scalarWeightedH1_eq_smooth_of_Lp_representative (g : SmoothMetric M)
    (o : FrameOrientation g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≤ 4)
    (u : scalarWeightedH1 d) (a : SmoothScalar (M := M))
    (hrep : scalarWeightedBaseLp g o d p hp u =ᵐ[normalizedVolume g] a.val) :
    u = smoothScalarToWeightedH1 d a := by
  apply scalarWeightedBaseLp_injective g o d p hp
  exact Lp.ext (hrep.trans (scalarWeightedBaseLp_smooth g o d p hp a).symm)

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

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarFixed_frameCompact
theorem scalarBaseResolvent_fixed_smooth (f : Lp ℝ 2 (normalizedVolume g))
    (hf : scalarBaseResolvent g o d f = f) :
    ∃ F : SmoothScalar (M := M), f = smoothScalarBaseL2 g F ∧ smoothScalarLaplacian g F = 0 := by
  let u := scalarBaseShiftedSolution g o d f
  have hu : scalarH1BaseValue g o d u = f := hf
  have hw (v : scalarH1 d) :
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        (0 : ℝ) * inner ℝ (scalarH1BaseValue g o d u) (scalarH1BaseValue g o d v) := by
    have he := scalarBaseShiftedSolution_weak g o d f v
    rw [scalarH1_inner_base, hu] at he
    change inner ℝ f (scalarH1BaseValue g o d v) + _ = _ at he
    simpa only [zero_mul] using (add_left_cancel (a := inner ℝ f
      (scalarH1BaseValue g o d v)) (show inner ℝ f (scalarH1BaseValue g o d v) +
        (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        inner ℝ f (scalarH1BaseValue g o d v) + 0 by simpa only [add_zero] using he))
  obtain ⟨F, hF, hL⟩ := scalar_weak_eigen_smooth g o d u 0 hw
  refine ⟨F, ?_, ?_⟩
  · rw [← hu, hF, scalarH1BaseValue_smooth]
  · simpa only [neg_zero, zero_smul] using hL

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


attribute [local instance] OAI.PositiveEinsteinFour.Geometry.katoEnergy_four
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.katoEnergy_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.katoEnergy_probability
/-- The rational square has controlled actual first-jet energy. -/
theorem scalar_minimum_kato_energy (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ z : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) z‖ ^ 2 ≤ ‖z‖ ^ 2)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ z : scalarH1 d,
      scalarH1BaseValue g o d z =ᵐ[normalizedVolume g]
        (fun x => scalarKatoSquare lam
          (scalarH1BaseValue g o d (scalarWeightedH1ToH1 d w) x)) ∧
      ‖z‖ ^ 2 ≤
        (∫ x, scalarH1BaseValue g o d (scalarWeightedH1ToH1 d w) x ^ 4 ∂normalizedVolume g) +
        4 * ∫ x, |scalarH1BaseValue g o d (scalarWeightedH1ToH1 d w) x| ^ (p - 2) *
          scalarKatoSquare lam (scalarH1BaseValue g o d (scalarWeightedH1ToH1 d w) x) ^ 2
          ∂normalizedVolume g := by
  let u := scalarWeightedH1ToH1 d w
  let f := scalarH1BaseValue g o d u
  let T := scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le)
  obtain ⟨v, hv, hvg, he⟩ := scalar_minimum_kato_test g o d hp hp4 w hw hmin hlam
  obtain ⟨z, hz, hzg⟩ := scalarH1_katoSquare_base_exists g o d hlam u
  refine ⟨z, hz, ?_⟩
  have hT : (T w : M → ℝ) =ᵐ[normalizedVolume g] f :=
    scalarWeightedBaseLp_coe g o d _ _ w
  let R := ∫ x, |f x| ^ (p - 2) * scalarKatoSquare lam (f x) ^ 2 ∂normalizedVolume g
  have hR : 0 ≤ R := integral_nonneg fun x => mul_nonneg
    (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)
  have he' : inner ℝ w (scalarWeightedH1Equiv d v) = ‖w‖ ^ 2 * R := by
    rw [he]
    congr 1
    apply integral_congr_ae
    filter_upwards [hT] with x hx
    rw [hx, mul_assoc, scalarKato_test_square hlam]
  have hinner : inner ℝ (scalarH1Value d u) (scalarH1Value d v) ≥ 0 := by
    rw [← scalarH1BaseValue_spec g o d u, ← scalarH1BaseValue_spec g o d v,
      (scalarBasePullback g o).inner_map_map, kato_real_inner]
    apply integral_nonneg_of_ae
    filter_upwards [hv] with x hx
    rw [hx, scalarKato_test_square hlam]
    exact sq_nonneg _
  have hwback : scalarWeightedH1Equiv d u = w :=
    (scalarWeightedH1Equiv d).apply_symm_apply w
  have hei : inner ℝ w (scalarWeightedH1Equiv d v) =
      inner ℝ (scalarH1Value d u) (scalarH1Value d v) + (1 / 2 : ℝ) *
        ∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v) := by
    conv_lhs => rw [← hwback]
    exact scalarWeightedH1_inner d u v
  rw [hei] at he'
  have hgrad : (∑ i : Fin 4, ‖scalarH1Gradient d i z‖ ^ 2) ≤
      2 * ∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => kato_gradient_le hlam (scalarH1Value d u)
      (scalarH1Gradient d i u) (scalarH1Gradient d i v) (scalarH1Gradient d i z)
      (hvg i) (hzg i)
  have hg : (∑ i : Fin 4, ‖scalarH1Gradient d i z‖ ^ 2) ≤ 4 * R := by
    have hmR := mul_le_mul_of_nonneg_right hm hR
    nlinarith
  have hf4 : MemLp (fun x => f x) 4 (normalizedVolume g) :=
    (memLp_congr_ae (scalarH1BaseL4_coe g o d u)).mp (Lp.memLp (scalarH1BaseL4 g o d u))
  have hval : ‖scalarH1Value d z‖ ^ 2 ≤ ∫ x, f x ^ 4 ∂normalizedVolume g := by
    rw [← scalarH1BaseValue_spec g o d z, (scalarBasePullback g o).norm_map, scalarL2_norm_sq]
    have hi4 : Integrable (fun x => f x ^ 4) (normalizedVolume g) := by
      have h := hf4.integrable_norm_pow (by decide : (4 : ℕ) ≠ 0)
      have hh : (fun x => ‖f x‖ ^ 4) = (fun x => f x ^ 4) := by
        funext x
        rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (show 0 ≤ f x ^ 4 by positivity)]
      rwa [hh] at h
    apply integral_mono_ae (Lp.memLp (scalarH1BaseValue g o d z)).integrable_sq hi4
    filter_upwards [hz] with x hx
    rw [hx]
    exact scalarKatoSquare_sq_le hlam (f x)
  rw [scalarH1_norm_sq]
  change ‖scalarH1Value d z‖ ^ 2 + (∑ i : Fin 4, ‖scalarH1Gradient d i z‖ ^ 2) ≤
    (∫ x, f x ^ 4 ∂normalizedVolume g) + 4 * R
  exact add_le_add hval hg

/-- The actual normalized homogeneous minimum has an L⁸ base value. -/
theorem scalar_minimum_memLp_eight (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ z : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) z‖ ^ 2 ≤ ‖z‖ ^ 2) :
    MemLp (scalarH1BaseValue g o d (scalarWeightedH1ToH1 d w)) 8 (normalizedVolume g) := by
  let u := scalarWeightedH1ToH1 d w
  let f := scalarH1BaseValue g o d u
  let E := scalarH1BaseL4 g o d
  have hf : MemLp (fun x => f x) 4 (normalizedVolume g) :=
    (memLp_congr_ae (scalarH1BaseL4_coe g o d u)).mp (Lp.memLp (E u))
  let C := ‖E‖ ^ 2 + 1
  apply scalarKato_memLp_eight_of_energy hf (scalarKato_potential_memLp hf hp hp4)
    (C := C) (by dsimp [C]; positivity)
  · intro lam hlam
    obtain ⟨z, hz, _⟩ := scalar_minimum_kato_energy g o d hp hp4 w hw hm hmin hlam
    exact (memLp_congr_ae ((scalarH1BaseL4_coe g o d z).trans hz)).mp (Lp.memLp (E z))
  · intro lam hlam
    obtain ⟨z, hz, henergy⟩ := scalar_minimum_kato_energy g o d hp hp4 w hw hm hmin hlam
    have he : (E z : M → ℝ) =ᵐ[normalizedVolume g]
        fun x => scalarKatoSquare lam (f x) := (scalarH1BaseL4_coe g o d z).trans hz
    have hmoment : Real.sqrt (∫ x, scalarKatoSquare lam (f x) ^ 4 ∂normalizedVolume g) = ‖E z‖ ^ 2 := by
      rw [scalarLp_four_norm_sq]
      congr 1
      exact (integral_congr_ae (he.fun_comp fun r : ℝ => r ^ 4)).symm
    rw [hmoment]
    have hnorm := E.le_opNorm z
    have hsq : ‖E z‖ ^ 2 ≤ C * ‖z‖ ^ 2 :=
      kato_square_bound (norm_nonneg (E z)) (norm_nonneg E) (norm_nonneg z) hnorm
    exact hsq.trans (mul_le_mul_of_nonneg_left henergy (by dsimp [C]; positivity))

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarWeakEulerL2_frameCompact
local instance scalarWeakEulerL2_probability_rc90d1f_1 (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
theorem scalar_minimum_euler_all_H1_of_L2_source
    (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (F : Lp ℝ 2 (normalizedVolume g))
    (hF : F =ᵐ[normalizedVolume g] fun x =>
      |scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x| ^ (p - 2) *
        scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x)
    (v : scalarWeightedH1 d) :
    inner ℝ w v = ‖w‖ ^ 2 * inner ℝ (scalarBasePullback g o F)
      (scalarH1Value d (scalarWeightedH1ToH1 d v)) := by
  refine (smoothScalarToWeightedH1_dense d).induction_on
    (p := fun v => inner ℝ w v = ‖w‖ ^ 2 * inner ℝ (scalarBasePullback g o F)
      (scalarH1Value d (scalarWeightedH1ToH1 d v))) v ?_ ?_
  · exact isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.mul (continuous_const.inner
        ((scalarH1Value d).continuous.comp (scalarWeightedH1ToH1 d).continuous)))
  · intro a
    rw [scalarWeightedH1ToH1_smooth, scalarH1Value_smooth]
    rw [← scalarBasePullback_smooth g o a, (scalarBasePullback g o).inner_map_map,
      smoothScalarBaseL2_inner_right]
    rw [scalar_subcritical_minimum_weak_euler g o d hp hp4 w hw hmin a]
    congr 1
    apply integral_congr_ae
    filter_upwards [hF] with x hx
    rw [hx]

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

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarSmoothEuler_frameCompact
local instance scalarSmoothEuler_probability_rc90d1f_1 (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
theorem scalar_subcritical_pointwise_euler_of_positive_representative
    (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (a : SmoothScalar (M := M)) (hpos : ∀ x, 0 < a.val x)
    (hrep : scalarWeightedBaseLp g o d (ENNReal.ofReal p)
      (by exact_mod_cast hp4.le) w =ᵐ[normalizedVolume g] a.val) :
    (∫ x, a.val x ^ p ∂normalizedVolume g) = 1 ∧
      ∀ e : FrameBundle g, -scalarLaplacian g a.val e + 2 * a.val e.base =
        2 * ‖w‖ ^ 2 * a.val e.base ^ (p - 1) := by
  let T := scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le)
  have heq := scalarWeightedH1_eq_smooth_of_Lp_representative g o d _ _ w a hrep
  have hnorm : (∫ x, a.val x ^ p ∂normalizedVolume g) = 1 := by
    have h := scalarLp_moment_eq_norm_rpow (by linarith : 0 < p) (T w)
    rw [hw, Real.one_rpow] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards [hrep] with x hx
    rw [hx, abs_of_pos (hpos x)]
  refine ⟨hnorm, ?_⟩
  let μ := canonicalFrameMeasure g o
  let F := smoothScalarPositivePower a hpos (p - 1)
  have hvalue (b : SmoothScalar (M := M)) :
      inner ℝ (smoothScalarValueL2 g μ a) (smoothScalarValueL2 g μ b) =
        ∫ x, a.val x * b.val x ∂normalizedVolume g := by
    rw [← scalarBasePullback_smooth g o a, ← scalarBasePullback_smooth g o b,
      (scalarBasePullback g o).inner_map_map, smoothScalarBaseL2_inner]
  have hsource (b : SmoothScalar (M := M)) :
      (∫ x, |T w x| ^ (p - 2) * T w x * b.val x ∂normalizedVolume g) =
        inner ℝ (smoothScalarValueL2 g μ F) (smoothScalarValueL2 g μ b) := by
    rw [← scalarBasePullback_smooth g o F, ← scalarBasePullback_smooth g o b,
      (scalarBasePullback g o).inner_map_map, smoothScalarBaseL2_inner]
    apply integral_congr_ae
    filter_upwards [hrep] with x hx
    change T w x = a.val x at hx
    rw [hx, abs_of_pos (hpos x)]
    change a.val x ^ (p - 2) * a.val x * b.val x = a.val x ^ (p - 1) * b.val x
    rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add (hpos x), Real.rpow_one]
  let r := -(smoothScalarLaplacian g a) + (2 : ℝ) • a - (2 * ‖w‖ ^ 2) • F
  have hr : smoothScalarValueL2 g μ r = -smoothScalarLaplacianL2 (μ := μ) a +
      (2 : ℝ) • smoothScalarValueL2 g μ a -
      (2 * ‖w‖ ^ 2) • smoothScalarValueL2 g μ F := by
    dsimp only [r]
    rw [map_sub, map_add, map_neg, map_smul, map_smul, smoothScalarLaplacian_valueL2]
  have ht (b : SmoothScalar (M := M)) :
      inner ℝ (smoothScalarValueL2 g μ r) (smoothScalarValueL2 g μ b) = 0 := by
    have h := scalar_subcritical_minimum_weak_euler g o d hp hp4 w hw hmin b
    rw [hsource b] at h
    conv_lhs at h => rw [heq, smoothScalarToWeightedH1_inner g o d]
    have hgreen : smoothScalarDirichlet d a b =
        -(inner ℝ (smoothScalarLaplacianL2 (μ := μ) a) (smoothScalarValueL2 g μ b)) := by
      rw [smoothScalarDirichlet_symm, smoothScalarDirichlet_laplacian_pairing,
        real_inner_comm]
    rw [hgreen, ← hvalue b] at h
    rw [hr, inner_sub_left, inner_add_left, inner_neg_left,
      real_inner_smul_left, real_inner_smul_left]
    linarith
  have hz : smoothScalarValueL2 g μ r = 0 := inner_self_eq_zero.mp (ht r)
  have hrzero : r = 0 := smoothScalarValueL2_injective g o (by simpa only [map_zero] using hz)
  intro e
  have h := congrArg (fun b : SmoothScalar (M := M) => b.val e.base) hrzero
  change -scalarLaplacianBase g a.val e.base + 2 * a.val e.base -
    (2 * ‖w‖ ^ 2) * a.val e.base ^ (p - 1) = 0 at h
  rw [scalarLaplacian_eq_base]
  linarith

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarMinimumSource_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarMinimumSource_probability
theorem scalar_minimum_L2_source_of_memLp_eight
    (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (h8 : MemLp (scalarWeightedBaseLp g o d (ENNReal.ofReal p)
      (by exact_mod_cast hp4.le) w : M → ℝ) 8 (normalizedVolume g)) :
    ∃ F : Lp ℝ 2 (normalizedVolume g),
      F =ᵐ[normalizedVolume g] (fun x =>
        |scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x| ^ (p - 2) *
          scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x) ∧
      ∀ v : scalarH1 d,
        (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i (scalarWeightedH1ToH1 d w))
          (scalarH1Gradient d i v)) =
          -(inner ℝ ((2 : ℝ) • scalarH1Value d (scalarWeightedH1ToH1 d w) -
            (2 * ‖w‖ ^ 2) • scalarBasePullback g o F) (scalarH1Value d v)) := by
  let f := scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w
  have hF := scalar_nonlinear_memLp_two_of_eight h8 hp hp4
  let F := hF.toLp (fun x => |f x| ^ (p - 2) * f x)
  have hrep : F =ᵐ[normalizedVolume g] (fun x => |f x| ^ (p - 2) * f x) :=
    MemLp.coeFn_toLp hF
  refine ⟨F, hrep, ?_⟩
  intro v
  apply scalar_weighted_euler_to_weak_poisson g o d w (scalarBasePullback g o F) (‖w‖ ^ 2)
  intro z
  exact scalar_minimum_euler_all_H1_of_L2_source g o d hp hp4 w hw hmin F hrep z

/-- The actual normalized minimum has an L2 nonlinear source, with no
regularity premise on its representative. -/
theorem scalar_minimum_L2_source
    (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2) :
    ∃ F : Lp ℝ 2 (normalizedVolume g),
      F =ᵐ[normalizedVolume g] (fun x =>
        |scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x| ^ (p - 2) *
          scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x) ∧
      ∀ v : scalarH1 d,
        (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i (scalarWeightedH1ToH1 d w))
          (scalarH1Gradient d i v)) =
          -(inner ℝ ((2 : ℝ) • scalarH1Value d (scalarWeightedH1ToH1 d w) -
            (2 * ‖w‖ ^ 2) • scalarBasePullback g o F) (scalarH1Value d v)) := by
  apply scalar_minimum_L2_source_of_memLp_eight g o d hp hp4 w hw hmin
  exact (memLp_congr_ae (scalarWeightedBaseLp_coe g o d (ENNReal.ofReal p)
    (by exact_mod_cast hp4.le) w)).mpr
    (scalar_minimum_memLp_eight g o d hp hp4 w hw hm hmin)

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.continuousMinimum_frameCompact
local instance continuousMinimum_probability_rc90d1f_1 (g : SmoothMetric M) : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
theorem scalar_subcritical_minimum_positive_of_continuous
    (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (hn : ∀ᵐ x ∂normalizedVolume g,
      0 ≤ scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x)
    (f : M → ℝ) (hf : Continuous f)
    (hrep : scalarWeightedBaseLp g o d (ENNReal.ofReal p)
      (by exact_mod_cast hp4.le) w =ᵐ[normalizedVolume g] f) : ∀ x, 0 < f x := by
  let u := scalarWeightedH1ToH1 d w
  let T := scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le)
  have hbase : scalarH1BaseValue g o d u =ᵐ[normalizedVolume g] f :=
    (scalarWeightedBaseLp_coe g o d (ENNReal.ofReal p)
      (by exact_mod_cast hp4.le) w).symm.trans hrep
  have hV : scalarH1Value d u =ᵐ[canonicalFrameMeasure g o] fun e => f e.base := by
    rw [← scalarH1BaseValue_spec g o d u]
    have hh := (canonicalFrameMeasure_base g o).quasiMeasurePreserving.ae hbase
    filter_upwards [Lp.coeFn_compMeasurePreserving (scalarH1BaseValue g o d u)
      (canonicalFrameMeasure_base g o), hh] with e he hh
    exact he.trans hh
  have hnonneg : ∀ x, 0 ≤ f x := by
    have hb : ∀ᵐ x ∂normalizedVolume g, 0 ≤ f x := by
      filter_upwards [hn, hrep] with x hx he
      rwa [he] at hx
    exact scalar_continuous_base_nonneg_of_frame_ae g o f hf
      ((canonicalFrameMeasure_base g o).quasiMeasurePreserving.ae hb)
  obtain ⟨F, hF, heq⟩ := scalar_minimum_L2_source g o d hp hp4 w hw hm hmin
  let Z := scalarBasePullback g o F
  let S := (2 : ℝ) • scalarH1Value d u - (2 * ‖w‖ ^ 2) • Z
  have hZ : Z =ᵐ[canonicalFrameMeasure g o]
      fun e => |f e.base| ^ (p - 2) * f e.base := by
    have hFb := (canonicalFrameMeasure_base g o).quasiMeasurePreserving.ae hF
    have hrb := (canonicalFrameMeasure_base g o).quasiMeasurePreserving.ae hrep
    filter_upwards [Lp.coeFn_compMeasurePreserving F (canonicalFrameMeasure_base g o),
      hFb, hrb] with e he hFe hre
    change Lp.compMeasurePreserving FrameBundle.base (canonicalFrameMeasure_base g o) F e = _
    rw [he]
    change F e.base = _
    rw [hFe, hre]
  have hsource : ∀ᵐ e ∂canonicalFrameMeasure g o, S e ≤ 2 * f e.base := by
    filter_upwards [Lp.coeFn_sub ((2 : ℝ) • scalarH1Value d u) ((2 * ‖w‖ ^ 2) • Z),
      Lp.coeFn_smul (2 : ℝ) (scalarH1Value d u), Lp.coeFn_smul (2 * ‖w‖ ^ 2) Z,
      hV, hZ] with e hs h₁ h₂ hv hz
    simp only [Pi.sub_apply] at hs
    simp only [Pi.smul_apply, smul_eq_mul] at h₁ h₂
    change ((2 : ℝ) • scalarH1Value d u - (2 * ‖w‖ ^ 2) • Z) e ≤ _
    rw [hs, h₁, h₂, hv, hz]
    exact sub_le_self _ (mul_nonneg (by positivity)
      (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hnonneg _)))
  have hne : ∃ x, 0 < f x := by
    by_contra hnot
    have hfzero : ∀ x, f x = 0 := fun x =>
      le_antisymm (le_of_not_gt (fun hx => hnot ⟨x, hx⟩)) (hnonneg x)
    have hTzero : T w = 0 := by
      apply Lp.ext
      filter_upwards [hrep, Lp.coeFn_zero ℝ (ENNReal.ofReal p) (normalizedVolume g)] with x hx hz
      exact hx.trans ((hfzero x).trans hz.symm)
    have hnorm : ‖T w‖ = 1 := hw
    rw [hTzero, norm_zero] at hnorm
    norm_num at hnorm
  exact scalarH1_continuous_strong_minimum g o d u S heq f hf hV
    hnonneg hsource hne

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.minimumH2_frameCompact
local instance minimumH2_probability_rc90d1f_1 (g : SmoothMetric M) : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
theorem scalar_subcritical_minimum_local_H2
    (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (c : M) (z₀ : ChartTarget c) :
    ∃ r : ℝ, 0 < r ∧
      (∀ y ∈ closedBall (0 : FourSpace) 1,
        scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target) ∧
      ∃ v : Lp ℝ 2 (volume : Measure FourSpace),
        (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
          scalarH1BaseValue g o d (scalarWeightedH1ToH1 d w)
            ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
              volume.restrict (ball (0 : FourSpace) 1)] v ∧
        ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
          tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
          MemSobolev 2 2 (smulLeftCLM ℂ φ (scalarComplexL2 v : 𝓢'(FourSpace, ℂ))) := by
  obtain ⟨F, _, hF⟩ := scalar_minimum_L2_source g o d hp hp4 w hw hm hmin
  let u := scalarWeightedH1ToH1 d w
  let S := (2 : ℝ) • scalarH1BaseValue g o d u - (2 * ‖w‖ ^ 2) • F
  apply scalar_local_weighted_H2 g o d S u _ c z₀
  intro v
  have he : scalarBasePullback g o S = (2 : ℝ) • scalarH1Value d u -
      (2 * ‖w‖ ^ 2) • scalarBasePullback g o F := by
    simp only [S, map_sub, map_smul, scalarH1BaseValue_spec]
  rw [he]
  exact hF v

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

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.positiveEulerAllOrders_frameCompact
theorem scalar_positive_Euler_local_all_orders (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : Lp ℝ 2 (normalizedVolume g)) (u : scalarH1 d)
    (v : M → ℝ) (hv : Continuous v) (hpos : ∀ x, 0 < v x)
    (hurep : (scalarH1BaseValue g o d u : M → ℝ) =ᵐ[normalizedVolume g] v)
    (α β q : ℝ)
    (hf : (f : M → ℝ) =ᵐ[normalizedVolume g] fun x => α * v x + β * (v x) ^ q)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (scalarBasePullback g o f)
          (scalarH1Value d v))) (c : M) (z₀ : ChartTarget c) :
    ∃ r : ℝ, 0 < r ∧
      (∀ y ∈ closedBall (0 : V) 1,
        scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target) ∧
      ∃ w : Lp ℝ 2 (volume : Measure V),
        (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
          v ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
              volume.restrict (ball (0 : V) 1)] w ∧
        ∀ n : ℕ, ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
          tsupport (φ : V → ℂ) ⊆ ball 0 (1 / 2) →
          MemSobolev (n : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2 w : T)) := by
  obtain ⟨χ, hχ, hc, ht, η₁, hη₁, hchart⟩ := exists_scalar_chart_cutoff g c z₀
  obtain ⟨η₂, hη₂, hcoeff⟩ := scalarRescaledAdjointSchwartz_small g c z₀
    scalarCoefficientBump scalarCoefficientBump.contDiff scalarCoefficientBump.hasCompactSupport
  let r := min η₁ η₂ / 2
  have hr : 0 < r := half_pos (lt_min hη₁ hη₂)
  have hr₁ : |r| < η₁ := by
    rw [abs_of_pos hr]
    exact (half_lt_self (lt_min hη₁ hη₂)).trans_le (min_le_left _ _)
  have hr₂ : |r| < η₂ := by
    rw [abs_of_pos hr]
    exact (half_lt_self (lt_min hη₁ hη₂)).trans_le (min_le_right _ _)
  obtain ⟨a, b, ha, hb, ha₀, ha₁, ha₂, hb₀, hb₁⟩ := hcoeff r hr₂
  let A := scalarRescalingLinearEquiv g c z₀ r hr.ne'
  let w₀ := scalarWeightedChartL2 g o d c hc ht u χ hχ hc (Subset.refl _)
  let w := scalarAffinePullbackL2 A z₀ w₀
  have hW : MemSobolev 1 2 (scalarComplexL2 w : T) :=
    scalarAffinePullbackL2_memSobolev_one A z₀ w₀
      (scalarWeightedChartL2_memSobolev_one g o d c hc ht u χ hχ hc (Subset.refl _))
  have htarget (y : V) (hy : y ∈ ball (0 : V) 1) :
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target :=
    (hchart r hr₁ y (ball_subset_closedBall hy)).1
  have hA (y : V) (hy : y ∈ ball (0 : V) 1) (i j : Fin 4) : a i j y =
      ((-((2 * Real.pi) ^ 2)⁻¹ *
        (scalarRescaledPrincipal g c z₀ r y i j - (1 : Mat4) i j) : ℝ) : ℂ) := by
    have h := ha i j y
    simpa only [scalarCutoffPrincipal, scalarCoefficientBump_one (ball_subset_closedBall hy),
      one_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg] using h
  have hB (y : V) (hy : y ∈ ball (0 : V) 1) (i : Fin 4) : b i y =
      ((-((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledDrift g c z₀ r y i : ℝ) : ℂ) := by
    have h := hb i y
    simpa only [scalarCutoffDrift, scalarCoefficientBump_one (ball_subset_closedBall hy),
      one_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg] using h
  let F := scalarRescaledSourceL2 g c f χ hχ hc ht z₀ r hr.ne'
  have hreal (ψ : V → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
      (hψs : tsupport ψ ⊆ ball (0 : V) 1) :
      (∫ y, w y * scalarRescaledOperator g c z₀ r ψ y) = ∫ y, F y * ψ y := by
    rw [scalarRescaled_L2_test_equation g o d f u hw c hc ht χ hχ hc (Subset.refl _)
      z₀ r hr.ne' ψ hψ hψc (fun y hy => htarget y (hψs hy))
      (fun y hy => (hchart r hr₁ y (ball_subset_closedBall (hψs hy))).2)]
    exact (scalarRescaledSourceL2_pairing g c f χ hχ hc ht z₀ r hr.ne' ψ
      (fun y hy => (hchart r hr₁ y (ball_subset_closedBall (hψs hy))).2)).symm
  have htests (φ : S) (hφc : HasCompactSupport (φ : V → ℂ))
      (hφs : tsupport (φ : V → ℂ) ⊆ ball 0 1) :
      (scalarPerturbedOperator a (scalarAdjointDrift a b) (scalarComplexL2 w : T) -
          (scalarComplexL2 w : T) - smulLeftCLM ℂ (-scalarAdjointPotential a b : S)
            (scalarComplexL2 w : T)) φ =
        ∫ y, φ y * ((-((2 * Real.pi) ^ 2)⁻¹ * F y : ℝ) : ℂ) := by
    rw [scalarFormalAdjointOperator_remainder]
    exact scalar_normalized_adjoint_test_equation_of_integrable g c z₀ r F w a b
      (ball 0 1) hA hB hreal φ hφc hφs (scalar_real_L2_test_integrable F φ _)
  have hwbase : (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
      scalarH1BaseValue g o d u
        ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
          volume.restrict (ball (0 : V) 1)] w := by
    have hmp : Measure.QuasiMeasurePreserving (fun y : V => A y + z₀) volume volume := by
      refine ⟨by fun_prop, ?_⟩
      rw [scalarAffine_map_volume]
      exact Measure.smul_absolutelyContinuous
    have hbase := hmp.ae_eq_comp (scalarWeightedChartL2_coe g o d c hc ht u χ hχ hc (Subset.refl _))
    have hwr := scalarAffinePullbackL2_coe A z₀ w₀
    filter_upwards [ae_restrict_of_ae hbase, ae_restrict_of_ae hwr,
      ae_restrict_mem isOpen_ball.measurableSet] with y hbq hwq hy
    have hy₁ : y ∈ closedBall (0 : V) 1 := ball_subset_closedBall hy
    have hp := scalarRescalingLinearEquiv_apply g c z₀ r hr.ne' y
    dsimp only [Function.comp_apply] at hbq
    change w₀ (A y + z₀) = _ at hbq
    rw [hp, (hchart r hr₁ y hy₁).2, one_mul] at hbq
    change w y = w₀ (A y + z₀) at hwq
    rw [hp] at hwq
    exact (hwq.trans hbq).symm

  let ρ : V → ℝ := fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y)
  let b₀ : V → ℝ := fun y => v ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))
  have hurep' := scalar_rescaled_ae_predicate g c z₀ r hr.ne'
    (fun x => scalarH1BaseValue g o d u x = v x) hurep
  have hwv : (fun y => ρ y * b₀ y) =ᵐ[volume.restrict (ball (0 : V) 1)] w := by
    filter_upwards [hwbase, ae_restrict_of_ae hurep',
      ae_restrict_mem isOpen_ball.measurableSet] with y hy huv hyB
    exact (congrArg (fun t : ℝ => ρ y * t) (huv (htarget y hyB))).symm.trans hy
  have hreg2 (φ : S) (hφc : HasCompactSupport (φ : V → ℂ))
      (hφs : tsupport (φ : V → ℂ) ⊆ closedBall 0 (1 / 2)) :
      MemSobolev 2 2 (smulLeftCLM ℂ φ (scalarComplexL2 w : T)) := by
    exact scalar_ball_L2_forcing_gain a (scalarAdjointDrift a b)
      scalarEllipticSmallSize scalarEllipticSmallSize_pos.le ha₀ ha₁ ha₂ hb₀ hb₁
      scalarEllipticSmallSize_small (-scalarAdjointPotential a b)
      (scalarComplexL2 w : T) (fun y => ((-((2 * Real.pi) ^ 2)⁻¹ * F y : ℝ) : ℂ))
      (((Lp.memLp F).const_mul _).ofReal) hW htests
      (1 / 2) (by norm_num) (by norm_num) φ hφc hφs
  let κ : ℝ := -((2 * Real.pi) ^ 2)⁻¹
  let Ft := scalarComplexL2 (κ • F)
  have hpair (φ : S) : (Ft : T) φ = ∫ y, φ y * ((κ * F y : ℝ) : ℂ) := by
    rw [Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [scalarComplexL2_coe (κ • F), Lp.coeFn_smul κ F] with y hc hs
    rw [hc, hs]
    rfl
  have htests' (φ : S) (hφc : HasCompactSupport (φ : V → ℂ))
      (hφs : tsupport (φ : V → ℂ) ⊆ ball 0 1) :
      (scalarPerturbedOperator a (scalarAdjointDrift a b) (scalarComplexL2 w : T) -
          (scalarComplexL2 w : T) - smulLeftCLM ℂ (-scalarAdjointPotential a b : S)
            (scalarComplexL2 w : T)) φ = (Ft : T) φ :=
    (htests φ hφc hφs).trans (hpair φ).symm
  have hρ (y : V) (hy : y ∈ closedBall (0 : V) (1 / 2)) : ContDiffAt ℝ ∞ ρ y :=
    (chartVolumeDensity_contDiffAt g c _
      (htarget y (closedBall_subset_ball (by norm_num) hy))).comp y (by
        unfold scalarRescaledPoint
        fun_prop)
  have hρ0 (y : V) (hy : y ∈ closedBall (0 : V) (1 / 2)) : ρ y ≠ 0 :=
    (chartVolumeDensity_pos g c _
      (htarget y (closedBall_subset_ball (by norm_num) hy))).ne'
  obtain ⟨L, U, hL, hU, hrange⟩ := scalar_positive_continuous_range v hv hpos
  have hf' := scalar_rescaled_ae_predicate g c z₀ r hr.ne'
    (fun x => f x = α * v x + β * (v x) ^ q) hf
  have hFt : (Ft : V → ℂ) =ᵐ[volume.restrict (ball (0 : V) (1 / 2))]
      fun y => (ρ y * ((κ * r ^ 2 * α) * b₀ y +
        (κ * r ^ 2 * β) * (b₀ y) ^ q) : ℝ) := by
    filter_upwards [ae_restrict_of_ae (scalarComplexL2_coe (κ • F)),
      ae_restrict_of_ae (Lp.coeFn_smul κ F),
      ae_restrict_of_ae (scalarRescaledSourceL2_coe g c f χ hχ hc ht z₀ r hr.ne'),
      ae_restrict_of_ae hf', ae_restrict_mem isOpen_ball.measurableSet]
      with y hC hmul hF hfY hy
    have hy1 : y ∈ closedBall (0 : V) 1 :=
      closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hy)
    change scalarComplexL2 (κ • F) y = _
    rw [hC, hmul]
    change ((κ * F y : ℝ) : ℂ) = _
    rw [hF, (hchart r hr₁ y hy1).2, hfY (htarget y
      (ball_subset_ball (by norm_num) hy))]
    congr 1
    dsimp only [ρ, b₀]
    ring
  refine ⟨r, hr, fun y hy => (hchart r hr₁ y hy).1, w, hwv, ?_⟩
  exact scalar_local_positive_Euler_all_orders a (scalarAdjointDrift a b)
    scalarEllipticSmallSize scalarEllipticSmallSize_pos.le ha₀ ha₁ ha₂ hb₀ hb₁
    scalarEllipticSmallSize_small (-scalarAdjointPotential a b) w hW hreg2
    ρ b₀ hwv hρ hρ0 L U q (κ * r ^ 2 * α) (κ * r ^ 2 * β)
    hL hU (fun y _ => hrange _) Ft hFt
    (fun ψ hc hs => htests' ψ hc (hs.trans (ball_subset_ball (by norm_num))))

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.positiveEulerSmooth_frameCompact
theorem scalar_positive_Euler_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : Lp ℝ 2 (normalizedVolume g)) (u : scalarH1 d)
    (v : M → ℝ) (hv : Continuous v) (hpos : ∀ x, 0 < v x)
    (hurep : (scalarH1BaseValue g o d u : M → ℝ) =ᵐ[normalizedVolume g] v)
    (α β q : ℝ)
    (hf : (f : M → ℝ) =ᵐ[normalizedVolume g] fun x => α * v x + β * (v x) ^ q)
    (hw : ∀ a : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i a)) =
        -(inner ℝ (scalarBasePullback g o f) (scalarH1Value d a))) :
    ContMDiff I4 𝓘(ℝ, ℝ) ∞ v := by
  let b := scalarH1BaseValue g o d u
  have hlocal (x : M) : ∃ U : Set M, ∃ F : M → ℝ,
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn I4 𝓘(ℝ, ℝ) ∞ F U ∧
        (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict U] F := by
    let z₀ : ChartTarget x := ⟨chartAt FourSpace x x,
      (chartAt FourSpace x).map_source (mem_chart_source FourSpace x)⟩
    obtain ⟨r, hr, ht, w, he, hreg⟩ :=
      scalar_positive_Euler_local_all_orders g o d f u v hv hpos hurep α β q hf hw x z₀
    obtain ⟨G, hG, hwG⟩ := scalar_half_smooth_real_representative w hreg
    have hbr := scalar_rescaled_ae_predicate g x z₀ r hr.ne'
      (fun y => b y = v y) hurep
    have he' : (fun y => chartVolumeDensity g x (scalarRescaledPoint g x z₀ r y) *
        b ((chartAt FourSpace x).symm (scalarRescaledPoint g x z₀ r y))) =ᵐ[
          volume.restrict (ball (0 : FourSpace) (1 / 8))] G := by
      have he₁ := ae_restrict_of_ae_restrict_of_subset
        (ball_subset_ball (by norm_num : (1 / 8 : ℝ) ≤ 1)) he
      filter_upwards [he₁, hwG, ae_restrict_of_ae hbr,
        ae_restrict_mem isOpen_ball.measurableSet] with y hvw hwg hrep hy
      rw [hrep (ht y (ball_subset_closedBall (ball_subset_ball (by norm_num) hy)))]
      exact hvw.trans hwg
    obtain ⟨U, hU, hxU, _, H, hH, heH⟩ := scalar_chart_smooth_unweight g x z₀ r hr
      (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num) b ht G hG he'
    let W := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' U
    refine ⟨W, fun y => H (chartAt FourSpace x y),
      (chartAt FourSpace x).isOpen_inter_preimage hU, ⟨mem_chart_source FourSpace x, hxU⟩,
      ?_, scalar_chart_representative_ae g x U hU b H heH⟩
    intro y hy
    have hHC : ContDiffAt ℝ ∞ H (chartAt FourSpace x y) :=
      (hH _ hy.2).contDiffAt (hU.mem_nhds hy.2)
    exact (hHC.contMDiffAt.comp y
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hy.1)).contMDiffWithinAt
  obtain ⟨F, hFb⟩ := scalar_smooth_representative_of_local g b hlocal
  let := normalizedVolume_isOpenPosMeasure g
  have hFv : F.val = v := Measure.eq_of_ae_eq (hFb.trans hurep) F.property.continuous hv
  have hFs : ContMDiff I4 𝓘(ℝ, ℝ) ∞ F.val := F.property
  rwa [hFv] at hFs

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

theorem heatNormalBundleParametrix_residual {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∀ x ∈ ball 0 r, ∀ t > (0 : ℝ), ∀ k l : Fin 6,
      deriv (fun s => heatNormalBundleParametrix E s x k l) t +
        fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
          (fun y q => heatNormalBundleParametrix E t y q l) x k =
      fourHeatGaussian t x * t ^ 3 *
        fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
          (fun y q => E.amplitude 3 y q l) x k := by
  obtain ⟨s, hs, htrans⟩ := E.amplitude_transport hRic he
  obtain ⟨s', hs', hbase⟩ := E.base.transport_neighborhood hRic he
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace),
      E.base.a x = (heatNormalMetric g o e x)⁻¹ ∧ E.base.b x = heatNormalDrift g o e x ∧
      E.B x = heatNormalBundleFirst D x ∧ E.C x = heatNormalBundleZero D x ∧
      x ∈ ball 0 s ∧ x ∈ ball 0 s' := by
    filter_upwards [E.base.a_near, E.base.b_near, E.B_near, E.C_near,
      ball_mem_nhds (0 : FourSpace) hs, ball_mem_nhds (0 : FourSpace) hs']
      with x ha hb hB hC hx hx'
    exact ⟨ha, hb, hB, hC, hx, hx'⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, ?_⟩
  intro x hx t ht k l
  obtain ⟨ha, hb, hB, hC, hxs, hxs'⟩ := hball hx
  obtain ⟨hrad, hEik, hnext⟩ := htrans x hxs
  have hTU := (hbase x hxs').2.2.2
  have hreg (m : Fin 4) (q : Fin 6) : ContDiff ℝ 2 (fun y => E.amplitude m y q l) :=
    (E.amplitude_regular m (by omega) q l).of_le (by norm_num)
  have hzero (q : Fin 6) : fourHeatRadialTransport (E.base.a x) (E.base.b x)
      (fun y => E.amplitude 0 y q l) x = 0 := by
    by_cases hql : q = l
    · subst q
      simpa [HeatNormalBundleExtension.amplitude, fourHeatBundleCoefficient] using hTU
    · have hz : (fun y => E.amplitude 0 y q l) = fun _ => (0 : ℝ) := by
        funext y
        simp [HeatNormalBundleExtension.amplitude, fourHeatBundleCoefficient, hql]
      rw [hz]
      have hc := fourHeatRadialTransport_const_mul (E.base.a x) (E.base.b x) 0 E.base.U x
      simpa only [zero_mul] using hc
  have h := fourHeatBundlePolynomial_gaussian_residual (E.base.a x) (E.base.b x)
    (E.B x) (E.C x) (fun m y q => E.amplitude m y q l) hreg t ht x hrad hEik hzero
    (by intro q; simpa using hnext 0 (by omega) q l)
    (by intro q; convert hnext 1 (by omega) q l using 1 <;> norm_num)
    (by intro q; convert hnext 2 (by omega) q l using 1 <;> norm_num) k
  rw [ha, hb, hB, hC] at h
  exact h

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.minimumGradientL4_compact
theorem scalar_subcritical_minimum_gradient_memLp_four
    (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (i : Fin 4) :
    MemLp (scalarH1Gradient d i (scalarWeightedH1ToH1 d w) : FrameBundle g → ℝ)
      4 (canonicalFrameMeasure g o) := by
  let u := scalarWeightedH1ToH1 d w
  have hlocal (c : M) : ∃ U : Set M, IsOpen U ∧ c ∈ U ∧
      ∃ hU : U ⊆ (chartAt FourSpace c).source,
      ∀ (ρ : SmoothScalar (M := M)) (hρ : tsupport ρ.val ⊆ U),
      MemSobolev 2 2 (scalarComplexL2 (scalarH1CutoffValueL2 g o d c
        (scalarChartSupport_compact c ρ (hρ.trans hU))
        (scalarChartSupport_subset c ρ (hρ.trans hU))
        (scalarChartCutoff c ρ) (scalarChartCutoff_smooth c ρ (hρ.trans hU))
        (scalarChartCutoff_compact c ρ (hρ.trans hU))
        (scalarChartCutoff_support c ρ (hρ.trans hU)) u) : 𝓢'(FourSpace, ℂ)) := by
    let z₀ : ChartTarget c := ⟨chartAt FourSpace c c,
      (chartAt FourSpace c).map_source (mem_chart_source FourSpace c)⟩
    obtain ⟨r, hr, ht, v, hv, hreg⟩ :=
      scalar_subcritical_minimum_local_H2 g o d hp hp4 w hw hm hmin c z₀
    obtain ⟨U, hU, hcU, hUc, hcut⟩ := scalar_elliptic_cutoff_neighborhood g c z₀ r hr
    have hcU' : c ∈ U := by
      simpa only [z₀, (chartAt FourSpace c).left_inv (mem_chart_source FourSpace c)] using hcU
    refine ⟨U, hU, hcU', hUc, ?_⟩
    intro ρ hρ
    obtain ⟨v', hv'2, hv'⟩ := scalar_chart_H2_realization g c z₀ r hr ht
      (scalarH1BaseValue g o d u) v hv hreg (scalarChartCutoff c ρ)
      (scalarChartCutoff_smooth c ρ (hρ.trans hUc))
      (scalarChartCutoff_compact c ρ (hρ.trans hUc)) (hcut ρ hρ)
    exact scalarH1CutoffValue_H2_of_rep g o d c
      (scalarChartSupport_compact c ρ (hρ.trans hUc))
      (scalarChartSupport_subset c ρ (hρ.trans hUc))
      (scalarChartCutoff c ρ) (scalarChartCutoff_smooth c ρ (hρ.trans hUc))
      (scalarChartCutoff_compact c ρ (hρ.trans hUc))
      (scalarChartCutoff_support c ρ (hρ.trans hUc)) u v' hv'2 hv'
  choose U hU hx hchart hH2 using hlocal
  obtain ⟨P, hP⟩ := scalarPartition_subordinate_neighborhoods U hU hx hchart
  apply scalarH1Gradient_memLp_four_of_partition g o d P u i
  intro j
  apply scalarH1LocalizedFrame_memLp_four g o d (P.center j) (scalarPartitionFunction P j)
    (scalarPartitionFunction_support P j) (scalarPartitionFunction_abs_le_one P j) u
  intro k
  exact scalarH1LocalizedCoordinate_memLp_four_of_H2 g o d (P.center j)
    (scalarPartitionFunction P j) (scalarPartitionFunction_support P j) u
    (hH2 (P.center j) (scalarPartitionFunction P j) (hP j)) k

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates07
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite
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

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def smoothHarmonicToWeak (hRic : RicciThree g) :
    smoothHarmonicTwoForms (o := o) →ₗ[ℝ] twoFormWeitzenbockKernel (o := o) where
  toFun u := ⟨smoothTwoFormToH1 (show SmoothH1TwoForm o from u.val), by
    apply (mem_twoFormWeitzenbockKernel_iff_energy_zero hRic _).mpr
    rw [twoFormHodgeForm_smooth hRic]
    exact smoothHarmonicTwoForm_energy_zero u.val u.property⟩
  map_add' u v := Subtype.ext (map_add smoothTwoFormToH1
    (show SmoothH1TwoForm o from u.val) (show SmoothH1TwoForm o from v.val))
  map_smul' r u := Subtype.ext (map_smul smoothTwoFormToH1 r
    (show SmoothH1TwoForm o from u.val))

theorem smoothHarmonicToWeak_injective (hRic : RicciThree g) :
    Function.Injective (smoothHarmonicToWeak (o := o) hRic) := by
  intro u v h
  apply Subtype.ext
  have he : smoothTwoFormToH1 (show SmoothH1TwoForm o from u.val) =
      smoothTwoFormToH1 (show SmoothH1TwoForm o from v.val) := congrArg Subtype.val h
  have hv : (show SmoothH1TwoForm o from u.val) = (show SmoothH1TwoForm o from v.val) :=
    (smoothTwoFormToH1 (o := o)).injective he
  exact hv

theorem smoothHarmonicTwoForms_finite (hRic : RicciThree g) :
    FiniteDimensional ℝ (smoothHarmonicTwoForms (o := o)) :=
  FiniteDimensional.of_injective (smoothHarmonicToWeak hRic) (smoothHarmonicToWeak_injective hRic)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Vanishing lower-order signed traces for the actual normal-frame
connection and first heat amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

variable [T3Space M] [CompactSpace M]
  {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.first_amplitude_signed_trace
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source) :
    (twoFormHodgeMatrix * E.amplitude 1 0).trace = 0 := by
  rw [E.first_amplitude_intrinsic_center he, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul, twoFormHodgeMatrix_trace,
    heat_actual_potential_signed_trace]
  ring

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

theorem scalarBaseEigenbasis_apply (i : ScalarBaseEigenIndex g o d) :
    scalarBaseEigenbasis g o d i = scalarBaseEigenvector g o d i := by
  simp only [scalarBaseEigenbasis, HilbertBasis.coe_mk]

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.minimumH1Source_compact
theorem scalar_minimum_H1_source (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2) :
    ∃ S : scalarH1 d, ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i (scalarWeightedH1ToH1 d w))
        (scalarH1Gradient d i v)) = -(inner ℝ (scalarH1Value d S) (scalarH1Value d v)) := by
  let u := scalarWeightedH1ToH1 d w
  let b := scalarH1BaseValue g o d u
  have hbu : scalarBasePullback g o b = scalarH1Value d u := scalarH1BaseValue_spec g o d u
  have hu8 : MemLp (scalarH1Value d u : FrameBundle g → ℝ) 8 (canonicalFrameMeasure g o) := by
    rw [← hbu]
    exact (memLp_congr_ae (Lp.coeFn_compMeasurePreserving b (canonicalFrameMeasure_base g o)).symm).mp
      ((scalar_minimum_memLp_eight g o d hp hp4 w hw hm hmin).comp_measurePreserving
        (canonicalFrameMeasure_base g o))
  obtain ⟨N, hN, _⟩ := scalarH1_subcritical_compose d u hp hp4 hu8
    (scalar_subcritical_minimum_gradient_memLp_four g o d hp hp4 w hw hm hmin)
  obtain ⟨F, hF, hweak⟩ := scalar_minimum_L2_source g o d hp hp4 w hw hm hmin
  have hNF : scalarH1Value d N = scalarBasePullback g o F := by
    apply Lp.ext
    have hbase := (canonicalFrameMeasure_base g o).quasiMeasurePreserving.ae hF
    have hT := (canonicalFrameMeasure_base g o).quasiMeasurePreserving.ae
      (scalarWeightedBaseLp_coe g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w)
    have hval : (scalarBasePullback g o b : FrameBundle g → ℝ) =ᵐ[canonicalFrameMeasure g o]
        (fun e => b e.base) := Lp.coeFn_compMeasurePreserving b (canonicalFrameMeasure_base g o)
    rw [hbu] at hval
    filter_upwards [hN, hbase, hT, hval,
      Lp.coeFn_compMeasurePreserving F (canonicalFrameMeasure_base g o)]
      with e hn hf ht hu hfp
    change scalarH1Value d N e = Lp.compMeasurePreserving FrameBundle.base
      (canonicalFrameMeasure_base g o) F e
    rw [hfp]
    simp only [Function.comp_apply]
    rw [hf, ht]
    change scalarH1Value d N e = |b e.base| ^ (p - 2) * b e.base
    rw [← hu]
    exact hn
  refine ⟨(2 : ℝ) • u - (2 * ‖w‖ ^ 2) • N, ?_⟩
  intro v
  simpa only [map_sub, map_smul, hNF] using hweak v

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual second transport coefficient at the center, with its
quadratic Weitzenböck contribution to the signed trace isolated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.second_amplitude_signed_trace
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source) :
    2 * (twoFormHodgeMatrix * E.amplitude 2 0).trace =
      -(twoFormHodgeMatrix * heatMatrixScalarOperator (E.base.a 0) (E.base.b 0) (E.amplitude 1) 0).trace +
      (twoFormHodgeMatrix * twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) *
        twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)).trace := by
  have h := congrArg (fun A : HeatMat6 => (twoFormHodgeMatrix * A).trace)
    (E.second_amplitude_center he)
  rw [E.first_amplitude_intrinsic_center he] at h
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_sub, Matrix.mul_neg,
    Matrix.trace_sub, Matrix.trace_neg, Matrix.mul_one] at h
  rw [heat_actual_potential_signed_trace, mul_zero] at h
  simpa only [zero_sub, sub_neg_eq_add, Matrix.mul_assoc] using h

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.minimumContinuity_compact
theorem scalar_subcritical_minimum_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2) :
    ∃ f : M → ℝ, Continuous f ∧
      (scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w : M → ℝ)
        =ᵐ[normalizedVolume g] f := by
  let u := scalarWeightedH1ToH1 d w
  let b := scalarH1BaseValue g o d u
  obtain ⟨S, hS⟩ := scalar_minimum_H1_source g o d hp hp4 w hw hm hmin
  have hlocal (x : M) : ∃ U : Set M, ∃ F : M → ℝ,
      IsOpen U ∧ x ∈ U ∧ ContinuousOn F U ∧
        (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict U] F := by
    let z₀ : ChartTarget x := ⟨chartAt FourSpace x x,
      (chartAt FourSpace x).map_source (mem_chart_source FourSpace x)⟩
    obtain ⟨r, hr, ht, z, he, hreg⟩ := scalar_local_weighted_H3 g o d S u hS x z₀
    obtain ⟨G, hG, hzG⟩ := scalar_local_H3_continuous_real_representative z hreg
    have he' : (fun y => chartVolumeDensity g x (scalarRescaledPoint g x z₀ r y) *
        b ((chartAt FourSpace x).symm (scalarRescaledPoint g x z₀ r y))) =ᵐ[
          volume.restrict (ball (0 : FourSpace) (1 / 4))] G := by
      have he₁ : (fun y => chartVolumeDensity g x (scalarRescaledPoint g x z₀ r y) *
          b ((chartAt FourSpace x).symm (scalarRescaledPoint g x z₀ r y))) =ᵐ[
            volume.restrict (ball (0 : FourSpace) (1 / 4))] z :=
        ae_restrict_of_ae_restrict_of_subset
          (ball_subset_ball (by norm_num : (1 / 4 : ℝ) ≤ 1)) he
      exact he₁.trans hzG
    obtain ⟨U, hU, hxU, _, H, hH, heH⟩ := scalar_chart_continuous_unweight g x z₀ r hr
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num) b ht G hG he'
    let W := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' U
    refine ⟨W, fun y => H (chartAt FourSpace x y),
      (chartAt FourSpace x).isOpen_inter_preimage hU, ⟨mem_chart_source FourSpace x, hxU⟩,
      ?_, scalar_chart_representative_ae g x U hU b H heH⟩
    intro y hy
    exact ((hH.continuousAt (hU.mem_nhds hy.2)).comp
      ((chartAt FourSpace x).continuousAt hy.1)).continuousWithinAt
  obtain ⟨f, hf, hfb⟩ := scalar_continuous_representative_of_local g b hlocal
  exact ⟨f, hf, (scalarWeightedBaseLp_coe g o d (ENNReal.ofReal p)
    (by exact_mod_cast hp4.le) w).trans hfb.symm⟩

variable [PreconnectedSpace M]

theorem scalar_subcritical_minimum_positive_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (hn : ∀ᵐ x ∂normalizedVolume g,
      0 ≤ scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x) :
    ∃ f : M → ℝ, Continuous f ∧
      (scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w : M → ℝ)
        =ᵐ[normalizedVolume g] f ∧ ∀ x, 0 < f x := by
  obtain ⟨f, hf, hrep⟩ := scalar_subcritical_minimum_continuous g o d hp hp4 w hw hm hmin
  exact ⟨f, hf, hrep,
    scalar_subcritical_minimum_positive_of_continuous g o d hp hp4 w hw hm hmin hn f hf hrep⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth harmonic two-forms are preserved by Hodge star,
with finite positive and negative summands. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms
instance smoothHarmonicPositive_finite (hRic : RicciThree g) :
    FiniteDimensional ℝ (smoothHarmonicPositive (o := o) hRic) := by
  let _ := smoothHarmonicTwoForms_finite (o := o) hRic
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance smoothHarmonicNegative_finite (hRic : RicciThree g) :
    FiniteDimensional ℝ (smoothHarmonicNegative (o := o) hRic) := by
  let _ := smoothHarmonicTwoForms_finite (o := o) hRic
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.minimumSmoothness_compact
theorem scalar_subcritical_minimum_positive_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) (hp4 : p < 4)
    (w : scalarWeightedH1 d)
    (hw : ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w‖ = 1)
    (hm : ‖w‖ ^ 2 ≤ 1)
    (hmin : ∀ v : scalarWeightedH1 d, ‖w‖ ^ 2 *
      ‖scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) v‖ ^ 2 ≤ ‖v‖ ^ 2)
    (hn : ∀ᵐ x ∂normalizedVolume g,
      0 ≤ scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w x) :
    ∃ v : M → ℝ, ContMDiff I4 𝓘(ℝ, ℝ) ∞ v ∧
      (scalarWeightedBaseLp g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w : M → ℝ)
        =ᵐ[normalizedVolume g] v ∧ ∀ x, 0 < v x := by
  obtain ⟨v, hv, hrep, hpos⟩ :=
    scalar_subcritical_minimum_positive_continuous g o d hp hp4 w hw hm hmin hn
  let u := scalarWeightedH1ToH1 d w
  let b := scalarH1BaseValue g o d u
  have hb : (b : M → ℝ) =ᵐ[normalizedVolume g] v :=
    (scalarWeightedBaseLp_coe g o d (ENNReal.ofReal p) (by exact_mod_cast hp4.le) w).symm.trans hrep
  obtain ⟨F, hF, hweak⟩ := scalar_minimum_L2_source g o d hp hp4 w hw hm hmin
  let S := (2 : ℝ) • b - (2 * ‖w‖ ^ 2) • F
  have hsource : (S : M → ℝ) =ᵐ[normalizedVolume g]
      fun x => (2 : ℝ) * v x + (-(2 * ‖w‖ ^ 2)) * (v x) ^ (p - 1) := by
    filter_upwards [Lp.coeFn_sub ((2 : ℝ) • b) ((2 * ‖w‖ ^ 2) • F),
      Lp.coeFn_smul (2 : ℝ) b, Lp.coeFn_smul (2 * ‖w‖ ^ 2) F, hb, hF, hrep]
      with x hs h1 h2 hb hf hr
    change ((2 : ℝ) • b - (2 * ‖w‖ ^ 2) • F) x = _
    rw [hs]
    simp only [Pi.sub_apply]
    rw [h1, h2]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hb, hf, hr, abs_of_pos (hpos x)]
    have hpow : (v x) ^ (p - 2) * v x = (v x) ^ (p - 1) := by
      calc
        _ = (v x) ^ ((p - 2) + 1) := by rw [Real.rpow_add (hpos x), Real.rpow_one]
        _ = _ := by congr 1; ring
    rw [hpow]
    ring
  have hS (a : scalarH1 d) :
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i a)) =
        -(inner ℝ (scalarBasePullback g o S) (scalarH1Value d a)) := by
    have he : scalarBasePullback g o S = (2 : ℝ) • scalarH1Value d u -
        (2 * ‖w‖ ^ 2) • scalarBasePullback g o F := by
      simp only [S, b, map_sub, map_smul, scalarH1BaseValue_spec]
    rw [he]
    exact hweak a
  exact ⟨v, scalar_positive_Euler_smooth g o d S u v hv hpos hb
    2 (-(2 * ‖w‖ ^ 2)) (p - 1) hsource hS, hrep, hpos⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! One common actual normal family for all three Euler heat degrees. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_heatUniformEulerFamily (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) :
    ∃ F : HeatFamilyOneCoefficients, ∃ r > (0 : ℝ),
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧
      ∀ e' ∈ U, frameCoordinateState g e.base e' ∈ ball (frameCoordinateState g e.base e) (r / 2) ∧
        Nonempty (HeatCommonEulerMember g o e.base F r e') := by
  obtain ⟨F, t, _, _, hP, U₀, hU₀, he₀, R, hR, hdata⟩ := exists_heatNormalCommonChart g o e
  let p := frameCoordinateState g e.base e
  let P := heatRadialFrameFamily F t
  obtain ⟨D₀, C₀, hD₀P, hC₀, hE₀, hCt₀, _, hRD₀⟩ := hdata e he₀
  have hzero : P (0, p) = p := by simpa only [hD₀P] using D₀.initial
  have hc : (P (0, p)).1 ∈ (chartAt FourSpace e.base).target := by
    simpa only [hD₀P] using D₀.in_chart 0 (mem_ball_self D₀.radius_pos)
  have hf : (P (0, p)).2.det ≠ 0 := by
    rw [hzero]
    have hg := congrArg Matrix.det (frameChartMatrix_normalizes g e.base e (mem_chart_source FourSpace e.base))
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hg
    change p.2.det * (metricInChart g e.base p.1).det * p.2.det = 1 at hg
    intro hz
    rw [hz] at hg
    norm_num at hg
  have hm : heatFamilyMetric g e.base P (0, p) = 1 := by
    have hh := D₀.metric_slice_eq P hD₀P 0 (mem_ball_self D₀.radius_pos)
      (hP.differentiableAt (by norm_num)) (by rw [frameExponential_zero]; exact mem_chart_source FourSpace e.base)
    exact hh.trans (heatNormalMetric_zero g o e)
  have hmp : 0 < (heatFamilyMetric g e.base P (0, p)).det := by rw [hm, Matrix.det_one]; norm_num
  obtain ⟨E, ha, hb, hB, hC, hU⟩ := exists_heatFamilySmoothCoefficients g e.base P (0, p) hP hc hf hmp
  obtain ⟨F₀, _hFE, hFB, hFC⟩ := exists_heatFamilyOneCoefficients E g e.base P (0, p) hP hc hf hmp
  let F : HeatFamilyOneCoefficients := { F₀ with base := E }
  have hdetc : ContinuousAt (fun z => (heatFamilyMetric g e.base P z).det) (0, p) :=
    (heatFamilyMatrixDeterminant_contDiffAt 0 _ (0, p)
      (heatFamilyMetric_contDiffAt 0 g e.base P (0, p) (hP.of_le (by norm_num)) hc)).continuousAt
  have hdetpos : ∀ᶠ z in 𝓝 ((0 : FourSpace), p), 0 < (heatFamilyMetric g e.base P z).det :=
    hdetc.preimage_mem_nhds (isOpen_Ioi.mem_nhds hmp)
  have hn : ∀ᶠ z in 𝓝 ((0 : FourSpace), p),
      ContDiffAt ℝ 4 P z ∧ 0 < (heatFamilyMetric g e.base P z).det ∧
      E.a =ᶠ[𝓝 z] (fun y => (heatFamilyMetric g e.base P y)⁻¹) ∧
      E.b =ᶠ[𝓝 z] heatFamilyDrift g e.base P ∧
      E.B =ᶠ[𝓝 z] heatFamilyFirst g e.base P ∧
      E.C =ᶠ[𝓝 z] heatFamilyZero g e.base P ∧
      E.U =ᶠ[𝓝 z] heatFamilyLeading g e.base P ∧
      F.B =ᶠ[𝓝 z] heatFamilyOneFirst g e.base P ∧
      F.C =ᶠ[𝓝 z] heatFamilyOneZero g e.base P := by
    filter_upwards [(hP.of_le (show (4 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num),
      hdetpos, ha.eventuallyEq_nhds, hb.eventuallyEq_nhds, hB.eventuallyEq_nhds,
      hC.eventuallyEq_nhds, hU.eventuallyEq_nhds, hFB.eventuallyEq_nhds,
      hFC.eventuallyEq_nhds] with z hz hdz haz hbz hBz hCz hUz hB1z hC1z
    exact ⟨hz, hdz, haz, hbz, hBz, hCz, hUz, hB1z, hC1z⟩
  obtain ⟨S, hS, hball⟩ := Metric.mem_nhds_iff.mp hn
  let r := min R (S / 2)
  have hr : 0 < r := lt_min hR (half_pos hS)
  have hrR : r ≤ R := min_le_left _ _
  have hrS : r < S := (min_le_right _ _).trans_lt (half_lt_self hS)
  have hcoord : {e' : FrameBundle g | frameCoordinateState g e.base e' ∈ ball p (r / 2)} ∈ 𝓝 e :=
    (frameCoordinateState_continuousAt g e.base e (mem_chart_source FourSpace e.base)).preimage_mem_nhds
      (ball_mem_nhds _ (half_pos hr))
  obtain ⟨U, hsub, hUopen, heU⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU₀.mem_nhds he₀) hcoord)
  have hpair (q : CoordinateFrameSpace) (hq : q ∈ ball p (r / 2))
      (x : FourSpace) (hx : x ∈ ball 0 r) : (x, q) ∈ ball (0, p) S := by
    change max (dist x 0) (dist q p) < S
    exact max_lt (lt_trans hx hrS) ((show dist q p < r / 2 from hq).trans
      ((half_lt_self hr).trans hrS))
  refine ⟨F, r, hr, U, hUopen, heU, ?_⟩
  intro e' he'
  obtain ⟨he'₀, hq⟩ := hsub he'
  obtain ⟨D, C, hDP, hCs, hCE, hCt, hCi, hRD⟩ := hdata e' he'₀
  let q := frameCoordinateState g e.base e'
  obtain ⟨hPq, _, haq, hbq, hBq, hCq, hUq, hB1q, hC1q⟩ := hball (hpair q hq 0 (mem_ball_self hr))
  have he'c : e'.base ∈ (chartAt FourSpace e.base).source := by
    have hh := hCt (C.map_source (hCs ▸ mem_ball_self hR))
    rwa [hCE (hCs ▸ mem_ball_self hR), frameExponential_zero] at hh
  let A := E.normalExtension D he'c P (hPq.of_le (by norm_num)) hDP haq hbq hBq hCq hUq
  have hbs : ball (0 : FourSpace) r ⊆ C.source := by rw [hCs]; exact ball_subset_ball hrR
  have hsource (x : FourSpace) (hx : x ∈ ball 0 r) :
      frameExponential g o e' x ∈ (chartAt FourSpace e.base).source := by
    rw [← hCE (hbs hx)]
    exact hCt (C.map_source (hbs hx))
  have hraw := heatFamilyNormal_on_ball D P hDP r (hrR.trans hRD)
    (fun x hx => (hball (hpair q hq x hx)).1.of_le (by norm_num)) hsource
    (fun x hx => (hball (hpair q hq x hx)).2.1)
  let N : HeatCommonNormalMember g o e.base E r e' := {
    frameData := D, extension := A, chart := C,
    radius_le := hrR.trans hRD,
    point_regular := fun x hx => by
      rw [hDP]
      exact ContDiffAt.comp (f := fun y : FourSpace => (y, q)) (g := P) x
        ((hball (hpair q hq x hx)).1.of_le (by norm_num)) (contDiffAt_id.prodMk contDiffAt_const)
    metric_pos := fun x hx => by
      have hh := D.metric_slice_eq P hDP x (ball_subset_ball (hrR.trans hRD) hx)
        ((hball (hpair q hq x hx)).1.differentiableAt (by norm_num)) (hsource x hx)
      rw [← hh]
      exact (hball (hpair q hq x hx)).2.1
    ball_source := hbs, exponential := hCE, target_chart := hCt, inverse_regular := hCi,
    a_family := rfl, b_family := rfl, B_family := rfl, C_family := rfl, U_family := rfl,
    actual := fun x hx => by
      obtain ⟨_, _, hax, hbx, hBx, hCx, hUx, _, _⟩ := hball (hpair q hq x hx)
      obtain ⟨ha', hb', hB', hC', hU'⟩ := hraw x hx
      exact ⟨hax.self_of_nhds.trans ha', hbx.self_of_nhds.trans hb',
        hBx.self_of_nhds.trans hB', hCx.self_of_nhds.trans hC', hUx.self_of_nhds.trans hU'⟩ }
  let A₁ := F.normalExtension D A.base he'c P (hPq.of_le (by norm_num)) hDP hB1q hC1q
  have hraw₁ := heatFamilyOneNormal_on_ball D P hDP r (hrR.trans hRD)
    (fun x hx => (hball (hpair q hq x hx)).1.of_le (by norm_num)) hsource
    (fun x hx => (hball (hpair q hq x hx)).2.1)
  refine ⟨hq, ⟨{
    normal := N, one := A₁, one_base := rfl,
    one_B_family := rfl, one_C_family := rfl,
    point_regular_four := ?_, one_actual := ?_ }⟩⟩
  · intro x hx
    rw [hDP]
    exact ContDiffAt.comp (f := fun y : FourSpace => (y, q)) (g := P) x
      (hball (hpair q hq x hx)).1 (contDiffAt_id.prodMk contDiffAt_const)
  · intro x hx
    obtain ⟨_, _, _, _, _, _, _, hB1x, hC1x⟩ := hball (hpair q hq x hx)
    exact ⟨hB1x.self_of_nhds.trans (hraw₁ x hx).1, hC1x.self_of_nhds.trans (hraw₁ x hx).2⟩

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory09
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The eigenvalue one of the actual shifted resolvent is exactly the
smooth harmonic space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormShiftedSolution_harmonic (hRic : RicciThree g) (u : TwoFormH1 o)
    (hu : u ∈ twoFormWeitzenbockKernel (o := o)) :
    twoFormShiftedSolution hRic (twoFormH1ToL2 u) = u := by
  symm
  apply twoFormShiftedSolution_unique hRic
  intro v
  rw [twoFormHodgeForm_zero_left hRic u
    ((mem_twoFormWeitzenbockKernel_iff_energy_zero hRic u).mp hu) v, zero_add]

theorem twoFormShiftedResolvent_harmonic (hRic : RicciThree g) (u : TwoFormH1 o)
    (hu : u ∈ twoFormWeitzenbockKernel (o := o)) :
    twoFormShiftedResolvent hRic (twoFormH1ToL2 u) = twoFormH1ToL2 u := by
  change twoFormH1ToL2 (twoFormShiftedSolution hRic (twoFormH1ToL2 u)) = _
  rw [twoFormShiftedSolution_harmonic hRic u hu]

theorem twoFormShiftedSolution_mem_harmonic (hRic : RicciThree g) (f : TwoFormL2 o)
    (hf : twoFormShiftedResolvent hRic f = f) :
    twoFormShiftedSolution hRic f ∈ twoFormWeitzenbockKernel (o := o) := by
  apply (mem_twoFormWeitzenbockKernel_iff_energy_zero hRic _).mpr
  have he := twoFormShiftedSolution_weak hRic f (twoFormShiftedSolution hRic f)
  change twoFormHodgeForm (twoFormShiftedSolution hRic f) (twoFormShiftedSolution hRic f) +
    inner ℝ (twoFormShiftedResolvent hRic f) (twoFormShiftedResolvent hRic f) =
      inner ℝ f (twoFormShiftedResolvent hRic f) at he
  rw [hf] at he
  linarith only [he]

def twoFormWeakHarmonicToResolvent (hRic : RicciThree g) :
    twoFormWeitzenbockKernel (o := o) →ₗ[ℝ]
      Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1 :=
  (twoFormH1ToL2.toLinearMap.comp (twoFormWeitzenbockKernel (o := o)).subtype).codRestrict _
    (fun u => Module.End.mem_eigenspace_iff.mpr (by
      change twoFormShiftedResolvent hRic (twoFormH1ToL2 u.val) =
        (1 : ℝ) • twoFormH1ToL2 u.val
      rw [one_smul]
      exact twoFormShiftedResolvent_harmonic hRic u.val u.property))

def twoFormWeakHarmonicResolventEquiv (hRic : RicciThree g) :
    twoFormWeitzenbockKernel (o := o) ≃ₗ[ℝ]
      Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1 :=
  LinearEquiv.ofBijective (twoFormWeakHarmonicToResolvent hRic) ⟨by
    intro u v huv
    exact Subtype.ext (twoFormH1ToL2_injective hRic (congrArg Subtype.val huv)), by
    intro f
    have hf := Module.End.mem_eigenspace_iff.mp f.property
    change twoFormShiftedResolvent hRic f.val = (1 : ℝ) • f.val at hf
    rw [one_smul] at hf
    refine ⟨⟨twoFormShiftedSolution hRic f.val,
      twoFormShiftedSolution_mem_harmonic hRic f.val hf⟩, Subtype.ext ?_⟩
    exact hf⟩

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

theorem smoothHodgeLaplacian_eq_zero_iff (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothHodgeLaplacian hRic u = 0 ↔ u ∈ smoothHarmonicTwoForms := by
  constructor
  · intro h
    apply (smoothTwoFormDeRhamEnergy_eq_zero_iff u).mp
    have he := (smoothHodgeLaplacian_pairing hRic u u).trans
      (twoFormHodgeForm_smooth hRic (u : SmoothH1TwoForm o))
    rw [h] at he
    exact he.symm.trans (show smoothTwoFormL2Inner (0 : smoothTwoForms o) u = 0 from
      @inner_zero_left ℝ (SmoothL2TwoForm o) _ _ _ (u : SmoothL2TwoForm o))
  · intro hu
    have hE : twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o))
        (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) = 0 :=
      (twoFormHodgeForm_smooth hRic (u : SmoothH1TwoForm o)).trans
        ((smoothTwoFormDeRhamEnergy_eq_zero_iff u).mpr hu)
    apply smoothTwoForm_eq_of_pairings
    intro v
    exact ((smoothHodgeLaplacian_pairing hRic u v).trans
      (twoFormHodgeForm_zero_left hRic _ hE _)).trans
        (@inner_zero_left ℝ (SmoothL2TwoForm o) _ _ _ (v : SmoothL2TwoForm o)).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The shifted Hodge resolvent commutes with the actual Hodge
involution. Consequently each finite spectral space is graded. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormShiftedSolution_hodge (hRic : RicciThree g) (f : TwoFormL2 o) :
    twoFormShiftedSolution hRic (twoFormL2Hodge f) =
      twoFormH1Hodge (twoFormShiftedSolution hRic f) := by
  symm
  apply twoFormShiftedSolution_unique hRic
  intro v
  calc
    _ = twoFormHodgeForm (twoFormShiftedSolution hRic f) (twoFormH1Hodge v) +
        inner ℝ (twoFormH1ToL2 (twoFormShiftedSolution hRic f))
          (twoFormH1ToL2 (twoFormH1Hodge v)) := by
      rw [twoFormHodgeForm_hodge_left hRic, twoFormH1ToL2_hodge,
        twoFormL2Hodge_selfAdjoint, twoFormH1ToL2_hodge]
    _ = inner ℝ f (twoFormH1ToL2 (twoFormH1Hodge v)) :=
      twoFormShiftedSolution_weak hRic f (twoFormH1Hodge v)
    _ = _ := by rw [twoFormH1ToL2_hodge, twoFormL2Hodge_selfAdjoint]

theorem twoFormShiftedResolvent_hodge (hRic : RicciThree g) (f : TwoFormL2 o) :
    twoFormShiftedResolvent hRic (twoFormL2Hodge f) =
      twoFormL2Hodge (twoFormShiftedResolvent hRic f) := by
  change twoFormH1ToL2 (twoFormShiftedSolution hRic (twoFormL2Hodge f)) = _
  rw [twoFormShiftedSolution_hodge, twoFormH1ToL2_hodge]
  rfl

theorem twoFormResolvent_eigenspace_hodge (hRic : RicciThree g) (μ : ℝ) (f : TwoFormL2 o)
    (hf : f ∈ Module.End.eigenspace (twoFormShiftedResolvent hRic).toLinearMap μ) :
    twoFormL2Hodge f ∈ Module.End.eigenspace (twoFormShiftedResolvent hRic).toLinearMap μ := by
  apply Module.End.mem_eigenspace_iff.mpr
  have he := Module.End.mem_eigenspace_iff.mp hf
  change twoFormShiftedResolvent hRic f = μ • f at he
  change twoFormShiftedResolvent hRic (twoFormL2Hodge f) = μ • twoFormL2Hodge f
  rw [twoFormShiftedResolvent_hodge, he, map_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak Hodge operator as a densely defined operator on L2.
Its domain is the range of the shifted resolvent. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHodgeDomain_of_weak (hRic : RicciThree g) (u : TwoFormH1 o) (h : TwoFormL2 o)
    (hu : ∀ v, twoFormHodgeForm u v = inner ℝ h (twoFormH1ToL2 v)) :
    twoFormH1ToL2 u ∈ twoFormHodgeDomain hRic := by
  refine ⟨h + twoFormH1ToL2 u, ?_⟩
  have he : u = twoFormShiftedSolution hRic (h + twoFormH1ToL2 u) := by
    apply twoFormShiftedSolution_unique hRic
    intro v
    rw [hu v, inner_add_left]
  change twoFormH1ToL2 (twoFormShiftedSolution hRic (h + twoFormH1ToL2 u)) = _
  exact congrArg twoFormH1ToL2 he.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The densely defined L2 generator agrees with the actual smooth
Hodge Laplacian, not merely with a formal spectral expression. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_mem_hodgeDomain (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormToL2 (u : SmoothL2TwoForm o) ∈ twoFormHodgeDomain hRic := by
  have h := twoFormHodgeDomain_of_weak hRic _ _ (smoothHodgeLaplacian_weak hRic u)
  have hv : twoFormH1ToL2 (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) =
      smoothTwoFormToL2 (u : SmoothL2TwoForm o) := twoFormH1ToL2_smooth _
  exact hv ▸ h

theorem twoFormHodgeGenerator_smooth (hRic : RicciThree g) (u : smoothTwoForms o) :
    twoFormHodgeGenerator hRic
      ⟨smoothTwoFormToL2 (u : SmoothL2TwoForm o), smoothTwoForm_mem_hodgeDomain hRic u⟩ =
        smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o) := by
  let f : twoFormHodgeDomain (o := o) hRic :=
    ⟨smoothTwoFormToL2 (u : SmoothL2TwoForm o), smoothTwoForm_mem_hodgeDomain hRic u⟩
  obtain ⟨v, hv, he⟩ := twoFormHodgeDomain_weak hRic f
  have hv' : v = smoothTwoFormToH1 (u : SmoothH1TwoForm o) :=
    twoFormH1ToL2_injective hRic (hv.trans (twoFormH1ToL2_smooth _).symm)
  have hpair (w : TwoFormH1 o) : inner ℝ (twoFormHodgeGenerator hRic f) (twoFormH1ToL2 w) =
      inner ℝ (smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o))
        (twoFormH1ToL2 w) := by
    rw [← he w, hv']
    exact smoothHodgeLaplacian_weak hRic u w
  have hall := twoFormH1ToL2_dense.equalizer
    (continuous_const.inner continuous_id) (continuous_const.inner continuous_id) (funext hpair)
  exact ext_inner_right ℝ (congrFun hall)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Orthogonal harmonic projection and smooth Poisson decomposition of
actual two-form sections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothHarmonicL2_finite (hRic : RicciThree g) :
    FiniteDimensional ℝ (smoothHarmonicL2 (o := o)) := by
  let _ : AddCommGroup (smoothHarmonicTwoForms (o := o)) := Submodule.addCommGroup _
  let _ : FiniteDimensional ℝ (smoothHarmonicTwoForms (o := o)) :=
    smoothHarmonicTwoForms_finite (o := o) hRic
  exact FiniteDimensional.of_injective (smoothHarmonicL2ToHarmonic (o := o))
    (smoothHarmonicL2ToHarmonic_injective (o := o))

theorem exists_smoothHarmonic_projection (hRic : RicciThree g) (f : smoothTwoForms o) :
    ∃ h : smoothTwoForms o, h ∈ smoothHarmonicTwoForms ∧
      ∀ v ∈ smoothHarmonicTwoForms (o := o), smoothTwoFormL2Inner (f - h) v = 0 := by
  let _ := smoothHarmonicL2_finite (o := o) hRic
  let p := (smoothHarmonicL2 (o := o)).orthogonalProjectionOnto (f : SmoothL2TwoForm o)
  refine ⟨p.val, p.property, ?_⟩
  intro v hv
  exact (smoothHarmonicL2 (o := o)).starProjection_inner_eq_zero
    (f : SmoothL2TwoForm o) (v : SmoothL2TwoForm o) hv

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite spectral heat kernels and their actual diagonal trace integrals.
The normalization is the same probability-volume L2 pairing used throughout. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormEigenSection (hRic : RicciThree g) (i : TwoFormEigenIndex (o := o) hRic) :
    smoothTwoForms o := (twoFormEigenvector_smooth hRic i).choose

theorem twoFormEigenSection_L2 (hRic : RicciThree g) (i : TwoFormEigenIndex (o := o) hRic) :
    smoothTwoFormToL2 (twoFormEigenSection hRic i : SmoothL2TwoForm o) =
      twoFormEigenvector hRic i :=
  (twoFormEigenvector_smooth hRic i).choose_spec.1.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact/coexact differential identities underlying cancellation of
the nonzero two-form spectrum in the signed trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem smoothHodgeLaplacian_hodge (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothHodgeLaplacian hRic (smoothTwoFormHodge o u) =
      smoothTwoFormHodge o (smoothHodgeLaplacian hRic u) := by
  rw [smoothHodgeLaplacian_dDelta_hodge hRic, smoothHodgeLaplacian_dDelta_hodge hRic,
    map_add, smoothTwoFormHodge_involutive, smoothTwoFormHodge_involutive]
  exact add_comm _ _

theorem smoothTwoFormDDelta_laplacian (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormDDelta (smoothHodgeLaplacian hRic u) =
      smoothTwoFormDDelta (smoothTwoFormDDelta u) := by
  rw [smoothHodgeLaplacian_dDelta_hodge hRic, smoothTwoFormDDelta_add,
    smoothTwoFormDDelta_hodge_DDelta hRic, add_zero]

theorem smoothHodgeLaplacian_DDelta (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothHodgeLaplacian hRic (smoothTwoFormDDelta u) =
      smoothTwoFormDDelta (smoothTwoFormDDelta u) := by
  rw [smoothHodgeLaplacian_dDelta_hodge hRic, smoothTwoFormDDelta_hodge_DDelta hRic,
    map_zero, add_zero]

theorem smoothTwoFormDDelta_eigen_square (hRic : RicciThree g) (κ : ℝ)
    (u : smoothTwoForms o) (hu : smoothHodgeLaplacian hRic u = κ • u) :
    smoothTwoFormDDelta (smoothTwoFormDDelta u) = κ • smoothTwoFormDDelta u := by
  rw [← smoothTwoFormDDelta_laplacian hRic, hu, smoothTwoFormDDelta_smul]

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

/-! The inertia of the actual harmonic intersection form. The positive
and negative indices are the dimensions of the Hodge summands. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.harmonicSignatureAddGroup
theorem harmonicIntersection_sigPos (hRic : RicciThree g) :
    sigPos (harmonicIntersectionQuadratic (o := o)) =
      Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) := by
  let _ := smoothHarmonicTwoForms_finite (o := o) hRic
  have hlo := le_sigPos_of_posDef
    (harmonicIntersectionQuadratic (o := o)) (harmonicIntersection_positive_definite hRic)
  have hhi := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := harmonicIntersectionQuadratic (o := o))
    (V := smoothHarmonicNegative hRic) (fun u hu => by
      change twoFormIntersection u.val u.val ≤ 0
      rw [smoothHarmonicIntersection_negative hRic ⟨u, hu⟩]
      exact neg_nonpos.mpr (smoothTwoFormL2Inner_nonneg _))
  have hd := (smoothHarmonicSumEquiv (o := o) hRic).finrank_eq
  rw [Module.finrank_prod] at hd
  omega

theorem harmonicIntersection_sigNeg (hRic : RicciThree g) :
    sigNeg (harmonicIntersectionQuadratic (o := o)) =
      Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) := by
  let _ := smoothHarmonicTwoForms_finite (o := o) hRic
  have hlo := le_sigNeg_of_negDef
    (harmonicIntersectionQuadratic (o := o)) (harmonicIntersection_negative_definite hRic)
  have hhi := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := -harmonicIntersectionQuadratic (o := o))
    (V := smoothHarmonicPositive hRic) (fun u hu => by
      change -twoFormIntersection u.val u.val ≤ 0
      rw [smoothHarmonicIntersection_positive hRic ⟨u, hu⟩]
      exact neg_nonpos.mpr (smoothTwoFormL2Inner_nonneg _))
  change sigNeg (harmonicIntersectionQuadratic (o := o)) + _ ≤ _ at hhi
  have hd := (smoothHarmonicSumEquiv (o := o) hRic).finrank_eq
  rw [Module.finrank_prod] at hd
  omega

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every nonharmonic two-form eigenspace has vanishing Hodge trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormSmoothEigenDDelta (hRic : RicciThree g) (μ : TwoFormSpectralValue (o := o) hRic) :
    Module.End ℝ (TwoFormSmoothEigenSpace hRic μ) where
  toFun u := ⟨smoothTwoFormDDelta u.val, by
    apply Module.End.mem_eigenspace_iff.mpr
    change smoothHodgeLaplacian hRic (smoothTwoFormDDelta u.val) =
      (μ.val⁻¹ - 1) • smoothTwoFormDDelta u.val
    rw [smoothHodgeLaplacian_DDelta]
    exact smoothTwoFormDDelta_eigen_square hRic _ u.val
      (Module.End.mem_eigenspace_iff.mp u.property)⟩
  map_add' u v := Subtype.ext (smoothTwoFormDDelta_add u.val v.val)
  map_smul' r u := Subtype.ext (smoothTwoFormDDelta_smul r u.val)

def twoFormSmoothEigenHodge (hRic : RicciThree g) (μ : TwoFormSpectralValue (o := o) hRic) :
    Module.End ℝ (TwoFormSmoothEigenSpace hRic μ) where
  toFun u := ⟨smoothTwoFormHodge o u.val, by
    apply Module.End.mem_eigenspace_iff.mpr
    change smoothHodgeLaplacian hRic (smoothTwoFormHodge o u.val) =
      (μ.val⁻¹ - 1) • smoothTwoFormHodge o u.val
    have hu : smoothHodgeLaplacian hRic u.val = (μ.val⁻¹ - 1) • u.val :=
      Module.End.mem_eigenspace_iff.mp u.property
    rw [smoothHodgeLaplacian_hodge hRic, hu, map_smul]⟩
  map_add' u v := Subtype.ext (map_add (smoothTwoFormHodge o) u.val v.val)
  map_smul' r u := Subtype.ext (map_smul (smoothTwoFormHodge o) r u.val)

theorem twoFormSmoothEigenDDelta_square (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    twoFormSmoothEigenDDelta hRic μ * twoFormSmoothEigenDDelta hRic μ =
      (μ.val⁻¹ - 1) • twoFormSmoothEigenDDelta hRic μ := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  exact smoothTwoFormDDelta_eigen_square hRic _ u.val
    (Module.End.mem_eigenspace_iff.mp u.property)

theorem twoFormSmoothEigenDDelta_hodge_zero (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    twoFormSmoothEigenDDelta hRic μ * twoFormSmoothEigenHodge hRic μ *
      twoFormSmoothEigenDDelta hRic μ = 0 := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  exact smoothTwoFormDDelta_hodge_DDelta hRic u.val

theorem twoFormSmoothEigenHodge_anticommutator (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    twoFormSmoothEigenHodge hRic μ * twoFormSmoothEigenDDelta hRic μ +
      twoFormSmoothEigenDDelta hRic μ * twoFormSmoothEigenHodge hRic μ =
        (μ.val⁻¹ - 1) • twoFormSmoothEigenHodge hRic μ := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  have he := congrArg (smoothTwoFormHodge o)
    ((smoothHodgeLaplacian_dDelta_hodge hRic u.val).symm.trans
      (Module.End.mem_eigenspace_iff.mp u.property))
  rw [map_add, smoothTwoFormHodge_involutive, map_smul] at he
  exact he

theorem twoFormSmoothEigenHodge_trace_zero (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) (hμ : μ.val ≠ 1) :
    LinearMap.trace ℝ (TwoFormSmoothEigenSpace hRic μ) (twoFormSmoothEigenHodge hRic μ) = 0 := by
  apply finite_hodge_trace_cancel (V := TwoFormSmoothEigenSpace hRic μ)
    (twoFormSmoothEigenDDelta hRic μ)
    (twoFormSmoothEigenHodge hRic μ) (μ.val⁻¹ - 1)
  · simpa only [ne_eq, sub_eq_zero, inv_eq_one] using hμ
  · exact twoFormSmoothEigenDDelta_square hRic μ
  · exact twoFormSmoothEigenDDelta_hodge_zero hRic μ
  · exact twoFormSmoothEigenHodge_anticommutator hRic μ

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual codifferential and Hodge star on each two-form eigenspace.
These identities give the degree-one multiplicities in the Euler heat trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothCodifferential_DDelta_eigen (hRic : RicciThree g)
    (u : smoothTwoForms o) (κ : ℝ) (hu : smoothHodgeLaplacian hRic u = κ • u) :
    smoothTwoFormCodifferentialField (smoothTwoFormDDelta u) =
      κ • smoothTwoFormCodifferentialField u := by
  have h := smoothCodiff_eigen hRic u κ hu
  rw [smoothOneFormHodgeLaplacian_apply] at h
  have hz : smoothScalarDifferential g
      (smoothOneFormDivergence g (smoothTwoFormCodifferentialField u)) = 0 := by
    rw [smoothTwoFormCodifferential_divergence hRic]
    exact (smoothScalarDifferentialLinear g).map_zero
  rw [hz, sub_zero] at h
  exact h

theorem twoFormEigenCodiff_DDelta (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    (oneFormCodiffEigenMap hRic μ).comp (twoFormSmoothEigenDDelta hRic μ) =
      (μ.val⁻¹ - 1) • oneFormCodiffEigenMap hRic μ := by
  apply LinearMap.ext
  intro u
  change smoothOneFormL2Linear (o := o)
    (smoothTwoFormCodifferentialField (smoothTwoFormDDelta u.val)) =
      (μ.val⁻¹ - 1) • smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField u.val)
  rw [smoothCodifferential_DDelta_eigen hRic u.val _
    (Module.End.mem_eigenspace_iff.mp u.property), map_smul]

theorem twoFormEigenCodiff_hodge_DDelta (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    ((oneFormCodiffEigenMap hRic μ).comp (twoFormSmoothEigenHodge hRic μ)).comp
      (twoFormSmoothEigenDDelta hRic μ) = 0 := by
  apply LinearMap.ext
  intro u
  have hz := (smoothTwoForm_closed_iff_codifferential_hodge (smoothTwoFormDDelta u.val)).mp
    (smoothTwoFormDDelta_closed hRic u.val)
  change smoothOneFormL2Linear (o := o)
    (smoothTwoFormCodifferentialField (smoothTwoFormHodge o (smoothTwoFormDDelta u.val))) = 0
  rw [hz, map_zero]

theorem twoFormEigenHodge_square (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    twoFormSmoothEigenHodge hRic μ * twoFormSmoothEigenHodge hRic μ = 1 := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  exact smoothTwoFormHodge_involutive o u.val

theorem twoFormEigen_DDelta_hodge_split (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    twoFormSmoothEigenDDelta hRic μ +
      twoFormSmoothEigenHodge hRic μ * twoFormSmoothEigenDDelta hRic μ *
        twoFormSmoothEigenHodge hRic μ =
      (μ.val⁻¹ - 1) • (1 : Module.End ℝ (TwoFormSmoothEigenSpace hRic μ)) := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  exact (smoothHodgeLaplacian_dDelta_hodge hRic u.val).symm.trans
    (Module.End.mem_eigenspace_iff.mp u.property)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer of Hodge trace cancellation to the actual L2 eigenspaces. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormEigenspaceHodge (hRic : RicciThree g) (μ : ℝ) :
    Module.End ℝ (Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap μ) where
  toFun f := ⟨twoFormL2Hodge f.val, twoFormResolvent_eigenspace_hodge hRic μ f.val f.property⟩
  map_add' f h := Subtype.ext (map_add twoFormL2Hodge f.val h.val)
  map_smul' r f := Subtype.ext (map_smul twoFormL2Hodge r f.val)

theorem twoFormEigenspaceHodge_trace_basis (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    LinearMap.trace ℝ (TwoFormSpectralSpace hRic μ) (twoFormEigenspaceHodge hRic μ.val) =
      ∑ j : Fin (Module.finrank ℝ (TwoFormSpectralSpace hRic μ)),
        inner ℝ (twoFormEigenvector hRic ⟨μ,j⟩) (twoFormL2Hodge (twoFormEigenvector hRic ⟨μ,j⟩)) := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (TwoFormSpectralSpace hRic μ))]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The trace on the harmonic eigenspace is the difference of the two
actual harmonic Hodge dimensions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.harmonicTraceAddGroup
theorem smoothHarmonicHodge_trace (hRic : RicciThree g) :
    LinearMap.trace ℝ (smoothHarmonicTwoForms (o := o)) (smoothHarmonicHodge hRic) =
      (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) -
        (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℝ) := by
  let E := smoothHarmonicSumEquiv (o := o) hRic
  let D : Module.End ℝ (smoothHarmonicPositive (o := o) hRic ×
      smoothHarmonicNegative (o := o) hRic) :=
    LinearMap.prodMap LinearMap.id (-LinearMap.id)
  have hcomm (u) : E (D u) = smoothHarmonicHodge hRic (E u) := by
    change u.1.val + -u.2.val = smoothHarmonicHodge hRic (u.1.val + u.2.val)
    rw [map_add, smoothHarmonicPositive_star, smoothHarmonicNegative_star]
  have he : E.conj D = smoothHarmonicHodge hRic := by
    apply LinearMap.ext
    intro w
    obtain ⟨u, rfl⟩ := E.surjective w
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact hcomm u
  rw [← he, LinearMap.trace_conj']
  change LinearMap.trace ℝ _ (LinearMap.prodMap LinearMap.id (-LinearMap.id)) = _
  rw [LinearMap.trace_prodMap']
  have hn := (LinearMap.trace ℝ (smoothHarmonicNegative (o := o) hRic)).map_neg
    (LinearMap.id : Module.End ℝ (smoothHarmonicNegative (o := o) hRic))
  rw [hn, LinearMap.trace_id, LinearMap.trace_id]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Each nonzero two-form Hodge eigenspace consists of two copies of its
actual coexact one-form image. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem oneFormCoexact_harmonic_eq_bot (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) (hμ : μ.val = 1) :
    OneFormCoexactSpectralSpace hRic μ = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  obtain ⟨u, hu, he⟩ := oneFormCoexactSpectral_representation hRic μ ⟨v, hv⟩
  have hδ := smoothCodiff_eigen hRic u (μ.val⁻¹ - 1) hu
  rw [hμ, inv_one, sub_self, zero_smul] at hδ
  have hz := smoothOneFormHodgeLaplacian_eq_zero (o := o) hRic _ hδ
  exact he.trans ((congrArg (smoothOneFormL2Linear (o := o)) hz).trans
    (map_zero smoothOneFormL2Linear))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual L2 spectral heat column with one frame and component fixed.
Square summability follows from the proved positive-time diagonal estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Manifold _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHeatFrameCoefficient (hRic : RicciThree g) (t : ℝ≥0)
    (e : FrameBundle g) (l : Fin 6) (i : TwoFormEigenIndex (o := o) hRic) : ℝ :=
  twoFormHeatWeight hRic t i.1 * twoFormFrameValue o (twoFormEigenSection hRic i).val e l

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

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def oneFormHeatTrace (t : ℝ≥0) : ℝ := ∑' i, oneFormHeatWeight hRic d t i

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact grouping of the scalar, one-form and two-form heat traces
by the finite eigenspaces of the actual shifted resolvents. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def oneFormCoexactHeatTrace (t : ℝ≥0) : ℝ :=
  ∑' i : OneFormCoexactEigenIndex (o := o) hRic, twoFormHeatWeight hRic t i.1

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform remainder bound for every entry of the constructed bundle
parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalBundleParametrix_residual_bound {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ x ∈ ball 0 r, ∀ t > (0 : ℝ), ∀ k l : Fin 6,
      |deriv (fun s => heatNormalBundleParametrix E s x k l) t +
        fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
          (fun y q => heatNormalBundleParametrix E t y q l) x k| ≤
      C * t ^ 3 * fourHeatGaussian t x := by
  let F := fun (x : FourSpace) (k l : Fin 6) =>
    fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
      (fun y q => E.amplitude 3 y q l) x k
  have hF (k l : Fin 6) : ContDiff ℝ 1 (fun x => F x k l) := by
    exact fourHeatBundleOperator_contDiff 1 E.base.a E.base.b E.B E.C _
      (fun i j => (E.base.a_regular i j).of_le (by norm_num))
      (fun i => (E.base.b_regular i).of_le (by norm_num))
      (fun i k l => (E.B_regular i k l).of_le (by norm_num))
      (fun k l => (E.C_regular k l).of_le (by norm_num))
      (fun q => (E.amplitude_regular 3 (by omega) q l).of_le (by norm_num)) k
  let S := fun x => ∑ k : Fin 6, ∑ l : Fin 6, |F x k l|
  have hS : Continuous S := continuous_finsetSum _ (fun k _ =>
    continuous_finsetSum _ (fun l _ => (hF k l).continuous.abs))
  have hle (x : FourSpace) (k l : Fin 6) : |F x k l| ≤ S x := by
    apply (Finset.single_le_sum (fun q _ => abs_nonneg (F x k q)) (Finset.mem_univ l)).trans
    exact Finset.single_le_sum (fun p _ => Finset.sum_nonneg (fun q _ => abs_nonneg (F x p q)))
      (Finset.mem_univ k)
  obtain ⟨r₀, hr₀, hR⟩ := heatNormalBundleParametrix_residual E hRic he
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), x ∈ ball 0 r₀ ∧
      E.base.a x = (heatNormalMetric g o e x)⁻¹ ∧ E.base.b x = heatNormalDrift g o e x ∧
      E.B x = heatNormalBundleFirst D x ∧ E.C x = heatNormalBundleZero D x := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) hr₀, E.base.a_near, E.base.b_near,
      E.B_near, E.C_near] with x hx ha hb hB hC
    exact ⟨hx, ha, hb, hB, hC⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : FourSpace) (r / 2)).bddAbove_image hS.continuousOn
  refine ⟨r / 2, by positivity, max C 0, le_max_right _ _, ?_⟩
  intro x hx t ht k l
  have hxr : x ∈ ball (0 : FourSpace) r := ball_subset_ball (by linarith) hx
  have hxcl : x ∈ closedBall (0 : FourSpace) (r / 2) := ball_subset_closedBall hx
  obtain ⟨hx₀, ha, hb, hB, hC'⟩ := hball hxr
  have hFx : |F x k l| ≤ max C 0 :=
    (hle x k l).trans ((hC (mem_image_of_mem _ hxcl)).trans (le_max_left _ _))
  rw [hR x hx₀ t ht k l, abs_mul, abs_mul,
    abs_of_pos (fourHeatGaussian_pos t ht x), abs_of_pos (pow_pos ht 3)]
  have heq : F x k l = fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹
      (heatNormalDrift g o e x) (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
      (fun y q => E.amplitude 3 y q l) x k := by
    dsimp only [F]
    rw [ha, hb, hB, hC']
  rw [← heq]
  calc
    _ ≤ (fourHeatGaussian t x * t ^ 3) * max C 0 :=
      mul_le_mul_of_nonneg_left hFx (mul_nonneg (fourHeatGaussian_pos t ht x).le
        (pow_nonneg ht.le 3))
    _ = _ := by ring

theorem heatNormalBundleParametrix_residual_uniform_linear {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ x ∈ ball 0 r, ∀ t > (0 : ℝ), ∀ k l : Fin 6,
      |deriv (fun s => heatNormalBundleParametrix E s x k l) t +
        fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
          (fun y q => heatNormalBundleParametrix E t y q l) x k| ≤ C * t := by
  obtain ⟨r, hr, C, hC, hR⟩ := heatNormalBundleParametrix_residual_bound E hRic he
  refine ⟨r, hr, C / (16 * Real.pi ^ 2), by positivity, ?_⟩
  intro x hx t ht k l
  calc
    _ ≤ C * t ^ 3 * fourHeatGaussian t x := hR x hx t ht k l
    _ ≤ C * t ^ 3 * fourHeatGaussian t 0 :=
      mul_le_mul_of_nonneg_left (fourHeatGaussian_le_diagonal t ht x)
        (mul_nonneg hC (pow_nonneg ht.le 3))
    _ = C * (t ^ (1 + 2) * fourHeatGaussian t 0) := by ring
    _ = _ := by rw [fourHeatGaussian_diagonal_power 1 t ht, pow_one]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform remainder bound for every entry of the constructed bundle
parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalOneParametrix_residual_bound {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ x ∈ ball 0 r, ∀ t > (0 : ℝ), ∀ k l : Fin 4,
      |deriv (fun s => heatNormalOneParametrix E s x k l) t +
        fourHeatOneOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalOneFirst D x) (heatNormalOneZero D x)
          (fun y q => heatNormalOneParametrix E t y q l) x k| ≤
      C * t ^ 3 * fourHeatGaussian t x := by
  let F := fun (x : FourSpace) (k l : Fin 4) =>
    fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
      (fun y q => E.amplitude 3 y q l) x k
  have hF (k l : Fin 4) : ContDiff ℝ 1 (fun x => F x k l) := by
    exact fourHeatOneOperator_contDiff 1 E.base.a E.base.b E.B E.C _
      (fun i j => (E.base.a_regular i j).of_le (by norm_num))
      (fun i => (E.base.b_regular i).of_le (by norm_num))
      (fun i k l => (E.B_regular i k l).of_le (by norm_num))
      (fun k l => (E.C_regular k l).of_le (by norm_num))
      (fun q => (E.amplitude_regular 3 (by omega) q l).of_le (by norm_num)) k
  let S := fun x => ∑ k : Fin 4, ∑ l : Fin 4, |F x k l|
  have hS : Continuous S := continuous_finsetSum _ (fun k _ =>
    continuous_finsetSum _ (fun l _ => (hF k l).continuous.abs))
  have hle (x : FourSpace) (k l : Fin 4) : |F x k l| ≤ S x := by
    apply (Finset.single_le_sum (fun q _ => abs_nonneg (F x k q)) (Finset.mem_univ l)).trans
    exact Finset.single_le_sum (fun p _ => Finset.sum_nonneg (fun q _ => abs_nonneg (F x p q)))
      (Finset.mem_univ k)
  obtain ⟨r₀, hr₀, hR⟩ := heatNormalOneParametrix_residual E hRic he
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), x ∈ ball 0 r₀ ∧
      E.base.a x = (heatNormalMetric g o e x)⁻¹ ∧ E.base.b x = heatNormalDrift g o e x ∧
      E.B x = heatNormalOneFirst D x ∧ E.C x = heatNormalOneZero D x := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) hr₀, E.base.a_near, E.base.b_near,
      E.B_near, E.C_near] with x hx ha hb hB hC
    exact ⟨hx, ha, hb, hB, hC⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : FourSpace) (r / 2)).bddAbove_image hS.continuousOn
  refine ⟨r / 2, by positivity, max C 0, le_max_right _ _, ?_⟩
  intro x hx t ht k l
  have hxr : x ∈ ball (0 : FourSpace) r := ball_subset_ball (by linarith) hx
  have hxcl : x ∈ closedBall (0 : FourSpace) (r / 2) := ball_subset_closedBall hx
  obtain ⟨hx₀, ha, hb, hB, hC'⟩ := hball hxr
  have hFx : |F x k l| ≤ max C 0 :=
    (hle x k l).trans ((hC (mem_image_of_mem _ hxcl)).trans (le_max_left _ _))
  rw [hR x hx₀ t ht k l, abs_mul, abs_mul,
    abs_of_pos (fourHeatGaussian_pos t ht x), abs_of_pos (pow_pos ht 3)]
  have heq : F x k l = fourHeatOneOperator (heatNormalMetric g o e x)⁻¹
      (heatNormalDrift g o e x) (heatNormalOneFirst D x) (heatNormalOneZero D x)
      (fun y q => E.amplitude 3 y q l) x k := by
    dsimp only [F]
    rw [ha, hb, hB, hC']
  rw [← heq]
  calc
    _ ≤ (fourHeatGaussian t x * t ^ 3) * max C 0 :=
      mul_le_mul_of_nonneg_left hFx (mul_nonneg (fourHeatGaussian_pos t ht x).le
        (pow_nonneg ht.le 3))
    _ = _ := by ring

theorem heatNormalOneParametrix_residual_uniform_linear {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ x ∈ ball 0 r, ∀ t > (0 : ℝ), ∀ k l : Fin 4,
      |deriv (fun s => heatNormalOneParametrix E s x k l) t +
        fourHeatOneOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalOneFirst D x) (heatNormalOneZero D x)
          (fun y q => heatNormalOneParametrix E t y q l) x k| ≤ C * t := by
  obtain ⟨r, hr, C, hC, hR⟩ := heatNormalOneParametrix_residual_bound E hRic he
  refine ⟨r, hr, C / (16 * Real.pi ^ 2), by positivity, ?_⟩
  intro x hx t ht k l
  calc
    _ ≤ C * t ^ 3 * fourHeatGaussian t x := hR x hx t ht k l
    _ ≤ C * t ^ 3 * fourHeatGaussian t 0 :=
      mul_le_mul_of_nonneg_left (fourHeatGaussian_le_diagonal t ht x)
        (mul_nonneg hC (pow_nonneg ht.le 3))
    _ = C * (t ^ (1 + 2) * fourHeatGaussian t 0) := by ring
    _ = _ := by rw [fourHeatGaussian_diagonal_power 1 t ht, pow_one]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! One O(t) cutoff-residual constant works for every actual normal frame
in a compact coordinate neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformCutoffResidual (E : HeatFamilySmoothCoefficients) (r : ℝ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ ball 0 r) (hχb : ∀ x, |χ x| ≤ 1)
    (s : ℝ) (hs : 0 < s) (hinner : ∀ x ∈ ball 0 s, χ x = 1)
    (hRic : RicciThree g) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonNormalMember g o c E r e),
      frameCoordinateState g c e ∈ K → e ∈ o.positive →
      ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
        |deriv (fun v => heatNormalCutoffParametrix N.extension χ v x k l) t +
          fourHeatBundleOperator (N.extension.base.a x) (N.extension.base.b x)
            (N.extension.B x) (N.extension.C x)
            (fun y q => heatNormalCutoffParametrix N.extension χ t y q l) x k| ≤ B * t := by
  obtain ⟨C₀, hC₀, hb⟩ := E.lastCoefficient_compact_bound (tsupport χ ×ˢ K) (hc.prod hK)
  obtain ⟨C₁, hC₁, hcom⟩ := heatFamilyCommutator_gaussian_bound E χ hχ hc K hK s hs hinner
  let B₀ := C₀ / (16 * Real.pi ^ 2)
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  refine ⟨B₀ + C₁, add_nonneg hB₀ hC₁, ?_⟩
  intro e N hq he t ht x k l
  let A := N.extension
  let q := frameCoordinateState g c e
  let u : Fin 4 → FourSpace → Fin 6 → ℝ := fun m y a => A.amplitude m y a l
  have hu (m : Fin 4) (a : Fin 6) : ContDiff ℝ 2 (fun y => u m y a) :=
    (A.amplitude_regular m (by omega) a l).of_le (by norm_num)
  by_cases hx : x ∈ tsupport χ
  · have hxr := hχs hx
    have hsym (i j : Fin 4) : A.base.a x i j = A.base.a x j i := by
      rw [(N.actual x hxr).1]
      exact congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    let Q := deriv (fun v => heatNormalBundleParametrix A v x k l) t +
      fourHeatBundleOperator (A.base.a x) (A.base.b x) (A.B x) (A.C x)
        (fun y a => heatNormalBundleParametrix A t y a l) x k
    have hQ : |Q| ≤ B₀ * t := by
      have hres := N.parametrix_residual hRic he x hxr t ht.1 k l
      change Q = fourHeatGaussian t x * t ^ 3 * E.lastCoefficient (x, q) k l at hres
      rw [hres, abs_mul, abs_mul, abs_of_pos (fourHeatGaussian_pos t ht.1 x),
        abs_of_pos (pow_pos ht.1 3)]
      calc
        _ ≤ (fourHeatGaussian t x * t ^ 3) * C₀ :=
          mul_le_mul_of_nonneg_left (hb (x, q) ⟨hx, hq⟩ k l)
            (mul_nonneg (fourHeatGaussian_pos t ht.1 x).le (pow_nonneg ht.1.le 3))
        _ ≤ (fourHeatGaussian t 0 * t ^ 3) * C₀ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (fourHeatGaussian_le_diagonal t ht.1 x)
              (pow_nonneg ht.1.le 3)) hC₀
        _ = C₀ * (t ^ (1 + 2) * fourHeatGaussian t 0) := by ring
        _ = B₀ * t := by rw [fourHeatGaussian_diagonal_power 1 t ht.1, pow_one]; dsimp [B₀]; ring
    have hid := heatNormalCutoffParametrix_residual_identity A χ t ht.1 x hχ.contDiffAt
      (A.base.a x) (A.base.b x) (A.B x) (A.C x) hsym k l
    have hscaled := fourHeatScaledCommutator_identity A.base.a A.base.b A.B χ u hu t ht.1 x k
    have hfamily : fourHeatScaledCommutator A.base.a A.base.b A.B χ u t x k =
        heatFamilyCommutator E χ t (x, q) k l := by
      have hu' : u = fun (m : Fin 4) y a => E.amplitude m (y, q) a l := by
        funext m y a
        exact congrArg (fun f : FourSpace → HeatMat6 => f y a l)
          (N.amplitude_family m (by omega))
      rw [hu']
      change fourHeatScaledCommutator N.extension.base.a N.extension.base.b N.extension.B χ _ t x k = _
      rw [N.a_family, N.b_family, N.B_family]
      rfl
    have hid' : deriv (fun v => heatNormalCutoffParametrix A χ v x k l) t +
        fourHeatBundleOperator (A.base.a x) (A.base.b x) (A.B x) (A.C x)
          (fun y a => heatNormalCutoffParametrix A χ t y a l) x k =
        χ x * Q + (fourHeatGaussian t x / t) * heatFamilyCommutator E χ t (x, q) k l := by
      rw [← hfamily, ← hscaled, hid]
      dsimp only [Q, heatNormalBundleParametrix, u]
      ring
    change |deriv (fun v => heatNormalCutoffParametrix A χ v x k l) t + _| ≤ _
    rw [hid']
    calc
      _ ≤ |χ x * Q| + |(fourHeatGaussian t x / t) * heatFamilyCommutator E χ t (x, q) k l| :=
        abs_add_le _ _
      _ ≤ B₀ * t + C₁ * t := by
        apply add_le_add _ (hcom q hq t ht x k l)
        rw [abs_mul]
        exact (mul_le_mul (hχb x) hQ (abs_nonneg Q) (by norm_num)).trans_eq (one_mul _)
      _ = _ := by ring
  · rw [heatNormalCutoffParametrix_residual_zero N.extension χ t x hx, abs_zero]
    exact mul_nonneg (add_nonneg hB₀ hC₁) ht.1.le

end
end PositiveEinsteinFour.Geometry
end


section

/-! A fixed bump and one residual constant for all actual normal
parametrices near an initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_heatActualUniformResidual (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) :
    ∃ E : HeatFamilySmoothCoefficients, ∃ r : ℝ, ∃ hr : 0 < r,
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧
      ∃ B ≥ (0 : ℝ), ∀ e' ∈ U,
        ∃ N : HeatCommonNormalMember g o e.base E r e',
          e' ∈ o.positive → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
            |deriv (fun v => heatNormalCutoffParametrix N.extension
                (heatNormalChartBump r hr) v x k l) t +
              fourHeatBundleOperator (N.extension.base.a x) (N.extension.base.b x)
                (N.extension.B x) (N.extension.C x)
                (fun y q => heatNormalCutoffParametrix N.extension
                  (heatNormalChartBump r hr) t y q l) x k| ≤ B * t := by
  obtain ⟨E, r, hr, U, hU, heU, hN, _⟩ := exists_heatUniformNormalFamily g o e
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hχs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  have hχb (x : FourSpace) : |χ x| ≤ 1 := by
    rw [abs_of_nonneg (heatNormalChartBump r hr).nonneg]
    exact (heatNormalChartBump r hr).le_one
  have hinner (x : FourSpace) (hx : x ∈ ball 0 (r / 4)) : χ x = 1 :=
    (heatNormalChartBump r hr).one_of_mem_closedBall (ball_subset_closedBall hx)
  obtain ⟨B, hB, hb⟩ := heatUniformCutoffResidual E r
    (closedBall (frameCoordinateState g e.base e) (r / 2)) (isCompact_closedBall _ _)
    χ (heatNormalChartBump r hr).contDiff (heatNormalChartBump r hr).hasCompactSupport
    hχs hχb (r / 4) (by positivity) hinner hRic
  refine ⟨E, r, hr, U, hU, heU, B, hB, ?_⟩
  intro e' he'
  obtain ⟨hq, ⟨N⟩⟩ := hN e' he'
  exact ⟨N, hb e' N (ball_subset_closedBall hq)⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compactly supported actual normal parametrix whose full residual
is uniformly O(t), including the annulus where the cutoff varies. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalCutoffParametrix_bound_of_support {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ R > (0 : ℝ), ∀ (χ : FourSpace → ℝ), ContDiff ℝ 2 χ → HasCompactSupport χ →
      tsupport χ ⊆ ball 0 R → (∀ x, |χ x| ≤ 1) →
      ∀ r > (0 : ℝ), (∀ x ∈ ball 0 r, χ x = 1) →
      ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
        |deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t +
          fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
            (fun y q => heatNormalCutoffParametrix E χ t y q l) x k| ≤ C * t := by
  obtain ⟨R₀, hR₀, C₀, hC₀, hbound⟩ :=
    heatNormalBundleParametrix_residual_uniform_linear E hRic he
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), x ∈ ball 0 R₀ ∧
      E.base.a x = (heatNormalMetric g o e x)⁻¹ ∧ E.base.b x = heatNormalDrift g o e x ∧
      E.B x = heatNormalBundleFirst D x ∧ E.C x = heatNormalBundleZero D x := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) hR₀, E.base.a_near, E.base.b_near,
      E.B_near, E.C_near] with x hx ha hb hB hC
    exact ⟨hx, ha, hb, hB, hC⟩
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨R, hR, ?_⟩
  intro χ hχ hχc hχs hχb r hr hinner
  let u (l : Fin 6) : Fin 4 → FourSpace → Fin 6 → ℝ := fun m y q => E.amplitude m y q l
  have hu (l : Fin 6) (m : Fin 4) (q : Fin 6) : ContDiff ℝ 2 (fun y => u l m y q) :=
    (E.amplitude_regular m (by omega) q l).of_le (by norm_num)
  have herror (l : Fin 6) := fourHeatScaledCommutator_gaussian_bound
    E.base.a E.base.b E.B χ (u l)
    (fun i j => (E.base.a_regular i j).continuous)
    (fun i => (E.base.b_regular i).continuous)
    (fun i k q => (E.B_regular i k q).continuous)
    hχ hχc (hu l) r hr hinner
  choose C₁ hC₁ herror using herror
  refine ⟨C₀ + ∑ l, C₁ l, add_nonneg hC₀ (Finset.sum_nonneg fun l _ => hC₁ l), ?_⟩
  intro t ht x k l
  by_cases hx : x ∈ tsupport χ
  · obtain ⟨hx₀, ha, hb, hB, hC⟩ := hball (hχs hx)
    have hsym (i j : Fin 4) : E.base.a x i j = E.base.a x j i := by
      rw [ha]
      exact congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    let Q := deriv (fun s => heatNormalBundleParametrix E s x k l) t +
      fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
        (fun y q => heatNormalBundleParametrix E t y q l) x k
    have hQ : |Q| ≤ C₀ * t := by
      dsimp only [Q]
      rw [ha, hb, hB, hC]
      exact hbound x hx₀ t ht.1 k l
    have hid := heatNormalCutoffParametrix_residual_identity E χ t ht.1 x hχ.contDiffAt
      (E.base.a x) (E.base.b x) (E.B x) (E.C x) hsym k l
    have hscaled := fourHeatScaledCommutator_identity E.base.a E.base.b E.B χ (u l)
      (hu l) t ht.1 x k
    have hid' : deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t +
        fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
          (fun y q => heatNormalCutoffParametrix E χ t y q l) x k =
        χ x * Q + (fourHeatGaussian t x / t) *
          fourHeatScaledCommutator E.base.a E.base.b E.B χ (u l) t x k := by
      rw [← hscaled, hid]
      dsimp only [Q, heatNormalBundleParametrix, u]
      ring
    rw [hid']
    have hCl : C₁ l ≤ ∑ q, C₁ q :=
      Finset.single_le_sum (fun q _ => hC₁ q) (Finset.mem_univ l)
    calc
      _ ≤ |χ x * Q| + |(fourHeatGaussian t x / t) *
          fourHeatScaledCommutator E.base.a E.base.b E.B χ (u l) t x k| := abs_add_le _ _
      _ ≤ C₀ * t + C₁ l * t := by
        apply add_le_add _ (herror l t ht x k)
        rw [abs_mul]
        exact (mul_le_mul (hχb x) hQ (abs_nonneg Q) (by norm_num)).trans_eq (one_mul _)
      _ ≤ (C₀ + ∑ q, C₁ q) * t := by
        nlinarith [mul_le_mul_of_nonneg_right hCl ht.1.le]
  · rw [heatNormalCutoffParametrix_residual_zero E χ t x hx]
    rw [abs_zero]
    exact mul_nonneg (add_nonneg hC₀ (Finset.sum_nonneg fun q _ => hC₁ q)) ht.1.le

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compactly supported actual normal parametrix whose full residual
is uniformly O(t), including the annulus where the cutoff varies. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalOneCutoffParametrix_bound_of_support {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ R > (0 : ℝ), ∀ (χ : FourSpace → ℝ), ContDiff ℝ 2 χ → HasCompactSupport χ →
      tsupport χ ⊆ ball 0 R → (∀ x, |χ x| ≤ 1) →
      ∀ r > (0 : ℝ), (∀ x ∈ ball 0 r, χ x = 1) →
      ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
        |deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t +
          fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
            (fun y q => heatNormalOneCutoffParametrix E χ t y q l) x k| ≤ C * t := by
  obtain ⟨R₀, hR₀, C₀, hC₀, hbound⟩ :=
    heatNormalOneParametrix_residual_uniform_linear E hRic he
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), x ∈ ball 0 R₀ ∧
      E.base.a x = (heatNormalMetric g o e x)⁻¹ ∧ E.base.b x = heatNormalDrift g o e x ∧
      E.B x = heatNormalOneFirst D x ∧ E.C x = heatNormalOneZero D x := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) hR₀, E.base.a_near, E.base.b_near,
      E.B_near, E.C_near] with x hx ha hb hB hC
    exact ⟨hx, ha, hb, hB, hC⟩
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨R, hR, ?_⟩
  intro χ hχ hχc hχs hχb r hr hinner
  let u (l : Fin 4) : Fin 4 → FourSpace → Fin 4 → ℝ := fun m y q => E.amplitude m y q l
  have hu (l : Fin 4) (m : Fin 4) (q : Fin 4) : ContDiff ℝ 2 (fun y => u l m y q) :=
    (E.amplitude_regular m (by omega) q l).of_le (by norm_num)
  have herror (l : Fin 4) := fourHeatOneScaledCommutator_gaussian_bound
    E.base.a E.base.b E.B χ (u l)
    (fun i j => (E.base.a_regular i j).continuous)
    (fun i => (E.base.b_regular i).continuous)
    (fun i k q => (E.B_regular i k q).continuous)
    hχ hχc (hu l) r hr hinner
  choose C₁ hC₁ herror using herror
  refine ⟨C₀ + ∑ l, C₁ l, add_nonneg hC₀ (Finset.sum_nonneg fun l _ => hC₁ l), ?_⟩
  intro t ht x k l
  by_cases hx : x ∈ tsupport χ
  · obtain ⟨hx₀, ha, hb, hB, hC⟩ := hball (hχs hx)
    have hsym (i j : Fin 4) : E.base.a x i j = E.base.a x j i := by
      rw [ha]
      exact congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    let Q := deriv (fun s => heatNormalOneParametrix E s x k l) t +
      fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
        (fun y q => heatNormalOneParametrix E t y q l) x k
    have hQ : |Q| ≤ C₀ * t := by
      dsimp only [Q]
      rw [ha, hb, hB, hC]
      exact hbound x hx₀ t ht.1 k l
    have hid := heatNormalOneCutoffParametrix_residual_identity E χ t ht.1 x hχ.contDiffAt
      (E.base.a x) (E.base.b x) (E.B x) (E.C x) hsym k l
    have hscaled := fourHeatOneScaledCommutator_identity E.base.a E.base.b E.B χ (u l)
      (hu l) t ht.1 x k
    have hid' : deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t +
        fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
          (fun y q => heatNormalOneCutoffParametrix E χ t y q l) x k =
        χ x * Q + (fourHeatGaussian t x / t) *
          fourHeatOneScaledCommutator E.base.a E.base.b E.B χ (u l) t x k := by
      rw [← hscaled, hid]
      dsimp only [Q, heatNormalOneParametrix, u]
      ring
    rw [hid']
    have hCl : C₁ l ≤ ∑ q, C₁ q :=
      Finset.single_le_sum (fun q _ => hC₁ q) (Finset.mem_univ l)
    calc
      _ ≤ |χ x * Q| + |(fourHeatGaussian t x / t) *
          fourHeatOneScaledCommutator E.base.a E.base.b E.B χ (u l) t x k| := abs_add_le _ _
      _ ≤ C₀ * t + C₁ l * t := by
        apply add_le_add _ (herror l t ht x k)
        rw [abs_mul]
        exact (mul_le_mul (hχb x) hQ (abs_nonneg Q) (by norm_num)).trans_eq (one_mul _)
      _ ≤ (C₀ + ∑ q, C₁ q) * t := by
        nlinarith [mul_le_mul_of_nonneg_right hCl ht.1.le]
  · rw [heatNormalOneCutoffParametrix_residual_zero E χ t x hx]
    rw [abs_zero]
    exact mul_nonneg (add_nonneg hC₀ (Finset.sum_nonneg fun q _ => hC₁ q)) ht.1.le

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

local instance instCompactSpaceFrameBundle_27_rc90d1f_1 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormHeatWeight_half_sq (t : ℝ≥0) (i : OneFormEigenIndex hRic d) :
    oneFormHeatWeight hRic d (t / 2) i ^ 2 = oneFormHeatWeight hRic d t i := by
  simp only [oneFormHeatWeight, pow_two, ← Real.exp_add, NNReal.coe_div, NNReal.coe_ofNat]
  congr 1
  ring

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.quadratic_zero (D : HeatNormalFrameData g o c e)
    (a : FourSpace → Mat4) : heatNormalConnectionQuadratic (D := D) a 0 = 0 := by
  simp only [heatNormalConnectionQuadratic, D.twoForm_connection_zero,
    Matrix.trace_zero, mul_zero, Finset.sum_const_zero]

theorem HeatNormalFrameData.quadratic_partial_zero (D : HeatNormalFrameData g o c e)
    (a : FourSpace → Mat4) (ha : ∀ r s, ContDiffAt ℝ 2 (fun x => a x r s) 0)
    (i : Fin 4) : partialDeriv (heatNormalConnectionQuadratic (D := D) a) i 0 = 0 := by
  have hA (r : Fin 4) (k l : Fin 6) :
      ContDiffAt ℝ 2 (fun x => heatTwoFormConnection g c D.point r x k l) 0 :=
    (D.twoForm_connection_regular r k l).of_le (by norm_num)
  have hr (r s : Fin 4) : ContDiffAt ℝ 2 (fun x => a x r s *
      (twoFormHodgeMatrix * heatTwoFormConnection g c D.point s x *
        heatTwoFormConnection g c D.point r x).trace) 0 :=
    (ha r s).mul (heat_trace_product_regular _ _ _ (hA s) (hA r))
  unfold heatNormalConnectionQuadratic
  rw [heat_partial_finite_sum _ 0 (fun r =>
    (ContDiffAt.sum (fun s _ => hr r s)).differentiableAt (by norm_num)) i]
  simp_rw [heat_partial_finite_sum _ 0 (fun s => (hr _ s).differentiableAt (by norm_num)) i]
  simp_rw [heat_weighted_trace_partial_zero _ _ _ _ (ha _ _) (hA _) (hA _)
    (D.twoForm_connection_zero _) (D.twoForm_connection_zero _) i]
  simp only [Finset.sum_const_zero]

theorem HeatNormalFrameData.quadratic_second (D : HeatNormalFrameData g o c e)
    (a : FourSpace → Mat4) (ha : ∀ r s, ContDiffAt ℝ 2 (fun x => a x r s) 0)
    (ha0 : a 0 = 1) (i : Fin 4) :
    partialDeriv (partialDeriv (heatNormalConnectionQuadratic (D := D) a) i) i 0 =
      ∑ r, (twoFormHodgeMatrix *
        (heatSixPartial (heatTwoFormConnection g c D.point r) i 0 *
          heatSixPartial (heatTwoFormConnection g c D.point r) i 0 +
        heatSixPartial (heatTwoFormConnection g c D.point r) i 0 *
          heatSixPartial (heatTwoFormConnection g c D.point r) i 0)).trace := by
  have hA (r : Fin 4) (k l : Fin 6) :
      ContDiffAt ℝ 2 (fun x => heatTwoFormConnection g c D.point r x k l) 0 :=
    (D.twoForm_connection_regular r k l).of_le (by norm_num)
  have hr (r s : Fin 4) : ContDiffAt ℝ 2 (fun x => a x r s *
      (twoFormHodgeMatrix * heatTwoFormConnection g c D.point s x *
        heatTwoFormConnection g c D.point r x).trace) 0 :=
    (ha r s).mul (heat_trace_product_regular _ _ _ (hA s) (hA r))
  unfold heatNormalConnectionQuadratic
  rw [heat_partial_second_finite_sum _ 0 (fun r => ContDiffAt.sum (fun s _ => hr r s)) i i]
  simp_rw [heat_partial_second_finite_sum _ 0 (fun s => hr _ s) i i]
  simp_rw [heat_weighted_trace_second_zero _ _ _ _ (ha _ _) (hA _) (hA _)
    (D.twoForm_connection_zero _) (D.twoForm_connection_zero _) i i]
  simp only [ha0, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, if_true]

end
end PositiveEinsteinFour.Geometry
end


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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instIsProbabilityMeasureNormalizedVolume_3
omit [PreconnectedSpace M] in
theorem oneFormEigenSection_norm_integral (i : OneFormEigenIndex hRic d) :
    (∫ x, covariantFieldNormSq g (oneFormEigenSection hRic d i).val x ∂normalizedVolume g) = 1 := by
  rw [← smoothOneFormL2Pairing_self (o := o), ← smoothOneFormL2Linear_inner,
    oneFormEigenSection_L2, real_inner_self_eq_norm_sq,
    (oneFormEigenvector_orthonormal hRic d).1 i, one_pow]

omit [PreconnectedSpace M] in
theorem oneFormEigenSection_norm_nonneg (i : OneFormEigenIndex hRic d) (x : M) :
    0 ≤ covariantFieldNormSq g (oneFormEigenSection hRic d i).val x := by
  rw [show x = (frameAt g x).base from rfl, covariantFieldNormSq_eq_frame _ (frameAt g x),
    oneForm_squareNorm]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compact C4 normal amplitude and its actual coefficient image lie
in the global L2 space, and the former belongs to the Hodge generator domain. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.compact_hodge_domain_near
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∃ r > (0 : ℝ), ∀ (C : OpenPartialHomeomorph FourSpace M)
      (_hE : EqOn C (frameExponential g o e) C.source)
      (hCt : C.target ⊆ (chartAt FourSpace c).source)
      (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
      (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 4 a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ C.source), tsupport a ⊆ Metric.ball 0 r →
      ∃ hf : heatNormalAmplitudeL2 D C hCt hP hD a (ha.of_le (by norm_num)) hc hs ∈
          twoFormHodgeDomain hRic,
        twoFormHodgeGenerator hRic ⟨heatNormalAmplitudeL2 D C hCt hP hD a
          (ha.of_le (by norm_num)) hc hs, hf⟩ = heatNormalHodgeImage E C hCt hP hD a ha hc hs := by
  obtain ⟨r, hr, hgreen⟩ := E.compact_green_near he hRic
  refine ⟨r, hr, ?_⟩
  intro C hE hCt hP hD a ha hc hs hsmall
  apply twoFormHodgeDomain_of_distribution hRic
  intro v
  have hleft := heatNormalAmplitudeL2_pairing_normal D C hE hCt hP hD a
    (ha.of_le (by norm_num)) hc hs (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o)
  have hright := heatNormalAmplitudeL2_pairing_normal D C hE hCt hP hD
    (heatNormalOperatorAmplitude E a) (heatNormalOperatorAmplitude_regular E a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOperatorAmplitude_support E a))
    ((heatNormalOperatorAmplitude_support E a).trans hs) (v : SmoothL2TwoForm o)
  exact hleft.trans ((congrArg ((normalizedChartFactor g).toReal * ·)
    (hgreen a (ha.of_le (by norm_num)) hc hsmall v)).trans hright.symm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed Hessian of the actual first heat amplitude at the center.
Only the curvature-square contribution survives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.quadratic_second_curvature
    {f : OrthonormalFrame g c} (D : HeatNormalFrameData g o c ⟨c, f⟩)
    (a : FourSpace → Mat4) (ha : ∀ r s, ContDiffAt ℝ 2 (fun x => a x r s) 0)
    (ha0 : a 0 = 1) (i : Fin 4) :
    partialDeriv (partialDeriv (heatNormalConnectionQuadratic (D := D) a) i) i 0 =
      (1 / 2 : ℝ) * ∑ r, (twoFormHodgeMatrix *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i r *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i r).trace := by
  rw [D.quadratic_second a ha ha0 i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hm : heatSixPartial (heatTwoFormConnection g c D.point r) i 0 =
      (1 / 2 : ℝ) • twoFormConnectionCurvatureMatrix
        (twoFormMetricCurvatureTensor g ⟨c, f⟩) i r := by
    ext k l
    exact D.twoForm_connection_half_curvature i r k l
  rw [hm]
  simp only [Matrix.mul_add, Matrix.trace_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  ring

theorem HeatNormalBundleExtension.first_amplitude_signed_second
    {f : OrthonormalFrame g c} {D : HeatNormalFrameData g o c ⟨c, f⟩}
    (E : HeatNormalBundleExtension D) (i : Fin 4) :
    partialDeriv (partialDeriv (fun x => (twoFormHodgeMatrix * E.amplitude 1 x).trace) i) i 0 =
      (1 / 6 : ℝ) * ∑ r, (twoFormHodgeMatrix *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i r *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i r).trace := by
  let F := fun x => (twoFormHodgeMatrix * E.firstSource x).trace
  let Q := heatNormalConnectionQuadratic (D := D) E.base.a
  have hF : ContDiff ℝ 2 F := by
    exact heatSignedTraceLinear.toContinuousLinearMap.contDiff.comp
      (contDiff_pi.mpr (fun k => contDiff_pi.mpr (fun l => E.firstSource_regular k l)))
  have hU : ContDiff ℝ 2 E.base.U := E.base.U_regular.of_le (by norm_num)
  have hU0 : ∀ x, E.base.U x ≠ 0 := fun x => (E.base.U_pos x).ne'
  have hU1 : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o ⟨c, f⟩)
  have hQ : (fun x => F x / E.base.U x) =ᶠ[𝓝 0] Q := by
    filter_upwards [E.firstSource_signed_near] with x hx
    change (twoFormHodgeMatrix * E.firstSource x).trace / E.base.U x = Q x
    rw [hx]
    exact mul_div_cancel_left₀ _ (hU0 x)
  have ha (r s : Fin 4) : ContDiffAt ℝ 2 (fun x => E.base.a x r s) 0 :=
    ((E.base.a_regular r s).of_le (by norm_num)).contDiffAt
  have ha0 : E.base.a 0 = 1 := by
    rw [E.base.a_near.self_of_nhds]
    change (heatNormalMetric g o ⟨c, f⟩ 0)⁻¹ = 1
    rw [heatNormalMetric_zero]
    simp
  have he : (fun x => (twoFormHodgeMatrix * E.amplitude 1 x).trace) =
      fourHeatWeightedRadialAverage 0 E.base.U F :=
    funext E.first_amplitude_signed_radial
  rw [he, fourHeatWeightedRadialAverage_second_of_vanishing_jet 0 E.base.U F Q hU hF hU0 hU1 hQ
    (D.quadratic_zero E.base.a) (D.quadratic_partial_zero E.base.a ha) i i,
    D.quadratic_second_curvature E.base.a ha ha0 i]
  norm_num
  ring

theorem HeatNormalBundleExtension.first_amplitude_signed_partial
    {D : HeatNormalFrameData g o c e} (E : HeatNormalBundleExtension D) (i : Fin 4) :
    partialDeriv (fun x => (twoFormHodgeMatrix * E.amplitude 1 x).trace) i 0 = 0 := by
  let F := fun x => (twoFormHodgeMatrix * E.firstSource x).trace
  let Q := heatNormalConnectionQuadratic (D := D) E.base.a
  have hF : ContDiff ℝ 2 F :=
    heatSignedTraceLinear.toContinuousLinearMap.contDiff.comp
      (contDiff_pi.mpr (fun k => contDiff_pi.mpr (fun l => E.firstSource_regular k l)))
  have hU : ContDiff ℝ 2 E.base.U := E.base.U_regular.of_le (by norm_num)
  have hU0 : ∀ x, E.base.U x ≠ 0 := fun x => (E.base.U_pos x).ne'
  have hQ : (fun x => F x / E.base.U x) =ᶠ[𝓝 0] Q := by
    filter_upwards [E.firstSource_signed_near] with x hx
    change (twoFormHodgeMatrix * E.firstSource x).trace / E.base.U x = Q x
    rw [hx]
    exact mul_div_cancel_left₀ _ (hU0 x)
  have hv : F 0 / E.base.U 0 = 0 := hQ.self_of_nhds.trans (D.quadratic_zero E.base.a)
  have hp : partialDeriv (fun x => F x / E.base.U x) i 0 = 0 :=
    (fourHeat_partial_germ hQ i).trans (D.quadratic_partial_zero E.base.a
      (fun r s => ((E.base.a_regular r s).of_le (by norm_num)).contDiffAt) i)
  have he : (fun x => (twoFormHodgeMatrix * E.amplitude 1 x).trace) =
      fourHeatWeightedRadialAverage 0 E.base.U F := funext E.first_amplitude_signed_radial
  rw [he, fourHeatWeightedRadialAverage_partial_zero 0 E.base.U F hU hF hU0 i, hv, hp]
  simp only [zero_div, mul_zero, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constructed compact parametrix columns, including their precise
probability-measure normalization, belong to the actual Hodge domain. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.parametrix_domain_near
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∃ r > (0 : ℝ), ∀ (C : OpenPartialHomeomorph FourSpace M)
      (_hE : EqOn C (frameExponential g o e) C.source)
      (hCt : C.target ⊆ (chartAt FourSpace c).source)
      (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
      (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (hc : HasCompactSupport χ)
      (hs : tsupport χ ⊆ C.source), tsupport χ ⊆ Metric.ball 0 r → ∀ (t : ℝ) (l : Fin 6),
      ∃ hf : heatNormalGlobalParametrixColumn E C hCt hP hD χ
          (hχ.of_le (by norm_num)) hc hs t l ∈ twoFormHodgeDomain hRic,
        twoFormHodgeGenerator hRic ⟨heatNormalGlobalParametrixColumn E C hCt hP hD χ
          (hχ.of_le (by norm_num)) hc hs t l, hf⟩ =
          heatNormalHodgeImage E C hCt hP hD (heatNormalCutoffColumn E χ t l)
            (heatNormalCutoffColumn_regular_four E χ hχ t l)
            (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalCutoffColumn_support E χ t l))
            ((heatNormalCutoffColumn_support E χ t l).trans hs) := by
  obtain ⟨r, hr, hdomain⟩ := E.compact_hodge_domain_near he hRic
  refine ⟨r, hr, ?_⟩
  intro C hE hCt hP hD χ hχ hc hs hsmall t l
  exact hdomain C hE hCt hP hD (heatNormalCutoffColumn E χ t l)
    (heatNormalCutoffColumn_regular_four E χ hχ t l)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalCutoffColumn_support E χ t l))
    ((heatNormalCutoffColumn_support E χ t l).trans hs)
    ((heatNormalCutoffColumn_support E χ t l).trans hsmall)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single genuine normal chart and compact cutoff for the time-dependent
parametrix. Its existence simultaneously enforces the domain and residual bounds. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {D : HeatNormalFrameData g o c e}

theorem exists_heatNormalParametrixData (E : HeatNormalBundleExtension D)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g) (hepos : e ∈ o.positive) :
    ∃ P : HeatNormalParametrixData D,
      (∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
        twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l) ∧
      ∃ B ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
        |deriv (fun s => heatNormalCutoffParametrix E P.cutoff s x k l) t +
          fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
            (fun y q => heatNormalCutoffParametrix E P.cutoff t y q l) x k| ≤ B * t := by
  obtain ⟨r₀, C, hr₀, hC, hE, _hInv, hCt, hP, hD⟩ := exists_heatNormalFrameChart D he
  obtain ⟨rd, hrd, hdomain⟩ := E.parametrix_domain_near he hRic
  obtain ⟨rb, hrb, hbound⟩ := heatNormalCutoffParametrix_bound_of_support E hRic hepos
  let R := min r₀ (min rd rb)
  have hR : 0 < R := lt_min hr₀ (lt_min hrd hrb)
  let χ : FourSpace → ℝ := heatNormalChartBump R hR
  have hsR : tsupport χ ⊆ ball 0 R := by
    rw [(heatNormalChartBump R hR).tsupport_eq]
    exact closedBall_subset_ball (by change R / 2 < R; linarith)
  have hR₀ : R ≤ r₀ := min_le_left _ _
  have hRd : R ≤ rd := (min_le_right _ _).trans (min_le_left _ _)
  have hRb : R ≤ rb := (min_le_right _ _).trans (min_le_right _ _)
  have hsC : tsupport χ ⊆ C.source := by
    rw [hC]
    exact hsR.trans (ball_subset_ball hR₀)
  let P : HeatNormalParametrixData D := {
    chart := C
    exponential := hE
    in_chart := hCt
    point_regular := hP.of_le (by norm_num)
    inside_radius := hD
    cutoff := χ
    cutoff_regular := (heatNormalChartBump R hR).contDiff
    cutoff_compact := (heatNormalChartBump R hR).hasCompactSupport
    cutoff_support := hsC
    cutoff_zero := (heatNormalChartBump R hR).one_of_mem_closedBall
      (mem_closedBall_self (by change 0 ≤ R / 4; positivity)) }
  refine ⟨P, ?_, ?_⟩
  · intro t l
    exact hdomain C hE hCt P.point_regular hD χ P.cutoff_regular P.cutoff_compact
      hsC (hsR.trans (ball_subset_ball hRd)) t l
  · apply hbound χ (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact
      (hsR.trans (ball_subset_ball hRb))
    · intro x
      rw [abs_of_nonneg (heatNormalChartBump R hR).nonneg]
      exact (heatNormalChartBump R hR).le_one
    · exact div_pos hR (by norm_num : (0 : ℝ) < 4)
    · intro x hx
      exact (heatNormalChartBump R hR).one_of_mem_closedBall (ball_subset_closedBall hx)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact normal-frame signed polynomial and its first jet. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.signedFirst_zero (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (he : e.base ∈ (chartAt FourSpace c).source) : E.signedFirst χ 0 = 0 := by
  simp [HeatNormalBundleExtension.signedFirst, E.first_amplitude_signed_trace he]

theorem HeatNormalBundleExtension.signedFirst_fderiv_zero (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiffAt ℝ 2 χ 0)
    (he : e.base ∈ (chartAt FourSpace c).source) : fderiv ℝ (E.signedFirst χ) 0 = 0 := by
  apply fourHeat_fderiv_zero_of_partial
  intro i
  change partialDeriv (fun x =>
    (frameExponentialJacobian g o e x * χ x ^ 2 * E.base.U x) *
      (twoFormHodgeMatrix * E.amplitude 1 x).trace) i 0 = 0
  rw [scalar_partial_product]
  · rw [E.first_amplitude_signed_trace he, E.first_amplitude_signed_partial]
    ring
  · exact ((((frameExponentialJacobian_smoothAt_zero g o e).of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞)).mul
      (hχ.pow 2)).mul
        (E.base.U_regular.of_le (by norm_num)).contDiffAt).differentiableAt (by norm_num)
  · exact (E.signed_amplitude_regular 1 (by norm_num)).differentiable two_ne_zero 0

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed second transport coefficient is the actual signature
curvature polynomial. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {f : OrthonormalFrame g c} {D : HeatNormalFrameData g o c ⟨c, f⟩}

theorem HeatNormalBundleExtension.first_amplitude_signed_scalar
    (E : HeatNormalBundleExtension D) :
    (twoFormHodgeMatrix * heatMatrixScalarOperator (E.base.a 0) (E.base.b 0)
      (E.amplitude 1) 0).trace =
      -(1 / 6 : ℝ) * ∑ i, ∑ j, (twoFormHodgeMatrix *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i j *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i j).trace := by
  rw [heatMatrixScalarOperator_signed_trace _ _ _ 0
    (fun k l => ((E.amplitude_regular 1 (by norm_num) k l).of_le (by norm_num)).contDiffAt)]
  have ha : E.base.a 0 = 1 := by
    rw [E.base.a_near.self_of_nhds]
    change (heatNormalMetric g o ⟨c, f⟩ 0)⁻¹ = 1
    rw [heatNormalMetric_zero]
    simp
  rw [ha]
  unfold fourHeatLocalOperator
  simp only [E.first_amplitude_signed_partial, mul_zero, Finset.sum_const_zero, add_zero,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  simp_rw [E.first_amplitude_signed_second, ← Finset.mul_sum]
  ring

theorem HeatNormalBundleExtension.second_amplitude_signature_polynomial
    (E : HeatNormalBundleExtension D) :
    (twoFormHodgeMatrix * E.amplitude 2 0).trace =
      (twoFormHodgeMatrix * twoFormPotentialMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) *
        twoFormPotentialMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩)).trace / 2 +
      (∑ i, ∑ j, (twoFormHodgeMatrix *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i j *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i j).trace) / 12 := by
  have h := E.second_amplitude_signed_trace (mem_chart_source FourSpace c)
  rw [E.first_amplitude_signed_scalar] at h
  linarith

theorem HeatNormalBundleExtension.second_amplitude_signature_density
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) :
    (twoFormHodgeMatrix * E.amplitude 2 0).trace / (16 * Real.pi ^ 2) =
      curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, f⟩) := by
  rw [E.second_amplitude_signature_polynomial]
  exact actual_hodgeSignatureTracePolynomial hRic ⟨c, f⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first signed coefficient is a joint C2 family, with a uniform
quadratic zero at every actual normal center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem heatUniformSignedFirst_quadratic (E : HeatFamilySmoothCoefficients) (r : ℝ) (hr : 0 < r)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hχs : tsupport χ ⊆ ball 0 r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonNormalMember g o c E r e),
      frameCoordinateState g c e ∈ K → ∀ x, ‖N.extension.signedFirst χ x‖ ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := heatFamily_quadratic_bound (heatFamilySignedFirst E χ)
    (heatFamilySignedFirst_regular E χ hχ) r K hK
  refine ⟨C, hC, ?_⟩
  intro e N hq x
  have hec : e.base ∈ (chartAt FourSpace c).source := by
    simpa only [frameExponential_zero] using N.exponential_source 0 (mem_ball_self hr)
  have hfun : (fun y => heatFamilySignedFirst E χ (y, frameCoordinateState g c e)) =
      N.extension.signedFirst χ := by
    funext y
    exact (N.signedFirst_family χ hχs y).symm
  by_cases hx : x ∈ closedBall (0 : FourSpace) r
  · rw [← hfun]
    apply hb _ hq _ _ x hx
    · exact (congrFun hfun 0).trans (N.extension.signedFirst_zero χ hec)
    · rw [hfun]
      exact N.extension.signedFirst_fderiv_zero χ hχ.contDiffAt hec
  · have hxs : x ∉ tsupport χ := fun hs => hx (ball_subset_closedBall (hχs hs))
    have hz := image_eq_zero_of_notMem_tsupport hxs
    simp only [HeatNormalBundleExtension.signedFirst, hz, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_mul, norm_zero]
    positivity

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual global residual retains the local cancellation and has
an L2 bound of order t for the constructed chart and cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.residual_eq (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) :
    P.residual E t l = P.timeColumn E t l + P.operatorColumn E t l := by
  exact heatNormalAmplitudeL2_add P.chart P.in_chart P.point_regular P.inside_radius
    (heatNormalTimeColumn E P.cutoff t l)
    (heatNormalOperatorAmplitude E (heatNormalCutoffColumn E P.cutoff t l))
    (heatNormalTimeColumn_regular E P.cutoff (P.cutoff_regular.of_le (by norm_num)) t l)
    (heatNormalOperatorAmplitude_regular E _ (heatNormalCutoffColumn_regular_four E P.cutoff P.cutoff_regular t l))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (heatNormalTimeColumn_support E P.cutoff t l))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      ((heatNormalOperatorAmplitude_support E _).trans (heatNormalCutoffColumn_support E P.cutoff t l)))
    ((heatNormalTimeColumn_support E P.cutoff t l).trans P.cutoff_support)
    (((heatNormalOperatorAmplitude_support E _).trans
      (heatNormalCutoffColumn_support E P.cutoff t l)).trans P.cutoff_support)

theorem exists_heatNormalGlobalResidual (E : HeatNormalBundleExtension D)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g) (hepos : e ∈ o.positive) :
    ∃ P : HeatNormalParametrixData D,
      (∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
        twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l) ∧
      ∃ B ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t := by
  obtain ⟨P, hP, B, hB, hb⟩ := exists_heatNormalParametrixData E he hRic hepos
  exact ⟨P, hP, 6 * B, by positivity,
    fun t ht l => P.residual_norm_le E t ht.1 B hB (hb t ht) l⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two coefficients that survive the signed Gaussian limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.first_amplitude_signed_gram
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source) :
    heatSignedGram (E.amplitude 1 0) (E.amplitude 1 0) =
      (twoFormHodgeMatrix * twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) *
        twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)).trace := by
  rw [E.first_amplitude_intrinsic_center he]
  exact heatSignedGram_scalar_sub _ _ (heat_actual_potential_symmetric e)
    (heat_actual_potential_signed_trace e)

theorem HeatNormalBundleExtension.signedFirst_second (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiffAt ℝ 2 χ 0) (hχ0 : χ 0 = 1)
    (he : e.base ∈ (chartAt FourSpace c).source) (i : Fin 4) :
    partialDeriv (partialDeriv (E.signedFirst χ) i) i 0 =
      partialDeriv (partialDeriv (fun x => (twoFormHodgeMatrix * E.amplitude 1 x).trace) i) i 0 := by
  let W := fun x => frameExponentialJacobian g o e x * χ x ^ 2 * E.base.U x
  have hW : ContDiffAt ℝ 2 W 0 :=
    (((frameExponentialJacobian_smoothAt_zero g o e).of_le (by norm_num)).mul
      (hχ.pow 2)).mul (E.base.U_regular.of_le (by norm_num)).contDiffAt
  have hU : E.base.U 0 = 1 := E.base.U_near.self_of_nhds.trans
    (heatNormalLeadingAmplitude_zero g o e)
  change partialDeriv (partialDeriv (fun x => W x *
    (twoFormHodgeMatrix * E.amplitude 1 x).trace) i) i 0 = _
  rw [scalar_partial_second_product_at _ _ 0 hW
    (E.signed_amplitude_regular 1 (by norm_num)).contDiffAt,
    E.first_amplitude_signed_trace he, E.first_amplitude_signed_partial]
  simp [W, frameExponentialJacobian_zero, hχ0, hU]

theorem HeatNormalBundleExtension.signedFirst_hessian_trace
    {f : OrthonormalFrame g c} {D : HeatNormalFrameData g o c ⟨c, f⟩}
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ)
    (hχ : ContDiffAt ℝ 2 χ 0) (hχ0 : χ 0 = 1) :
    (∑ i, fderiv ℝ (fderiv ℝ (E.signedFirst χ)) 0 (coordinateVector i) (coordinateVector i)) =
      (1 / 6 : ℝ) * ∑ i, ∑ j, (twoFormHodgeMatrix *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i j *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i j).trace := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← fourHeat_second_partial_eq_fderiv _ (E.signedFirst_regular χ hχ) i i,
    E.signedFirst_second χ hχ hχ0 (mem_chart_source FourSpace c), E.first_amplitude_signed_second]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Common actual parametrices have their Hodge generator identity and
one global L2 residual bound, uniformly in the nearby initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

theorem exists_heatActualUniformParametrix (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) :
    ∃ E : HeatFamilySmoothCoefficients, ∃ r : ℝ, ∃ hr : 0 < r,
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧
      ∃ B ≥ (0 : ℝ), ∀ e' ∈ U,
        ∃ N : HeatCommonNormalMember g o e.base E r e',
          (∀ t l, ∃ hf : (N.parametrixData hr).column N.extension t l ∈ twoFormHodgeDomain hRic,
            twoFormHodgeGenerator hRic ⟨(N.parametrixData hr).column N.extension t l, hf⟩ =
              (N.parametrixData hr).operatorColumn N.extension t l) ∧
          (e' ∈ o.positive → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
            ‖(N.parametrixData hr).residual N.extension t l‖ ≤ B * t) := by
  obtain ⟨E, r, hr, U, hU, heU, B, hB, hN⟩ := exists_heatActualUniformResidual g o hRic e
  refine ⟨E, r, hr, U, hU, heU, 6 * B, by positivity, ?_⟩
  intro e' he'
  obtain ⟨N, hb⟩ := hN e' he'
  refine ⟨N, N.parametrixData_generator hr hRic, ?_⟩
  intro hepos t ht l
  apply (N.parametrixData hr).residual_norm_le N.extension t ht.1 B hB _ l
  simpa only [N.parametrixData_cutoff hr] using hb hepos t ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual signed normal-parametrix Gaussian integral has the
signature curvature density as its limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.signed_reduced_gaussian_limit
    {f : OrthonormalFrame g c} {D : HeatNormalFrameData g o c ⟨c, f⟩}
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ)
    (hχ : ContDiff ℝ 4 χ) (hc : HasCompactSupport χ) (hχ0 : χ 0 = 1)
    (hRic : RicciThree g) :
    Tendsto (fun t : ℝ => ∫ x : FourSpace, fourHeatGaussian t x ^ 2 *
      (2 * t * E.signedFirst χ x + t ^ 2 * E.signedTail χ t x))
      (𝓝[>] 0) (𝓝 (curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, f⟩))) := by
  have hχ2 : ContDiffAt ℝ 2 χ 0 := (hχ.of_le (by norm_num)).contDiffAt
  have he := mem_chart_source FourSpace c
  obtain ⟨C, hC⟩ := (E.signedFirst_compact χ hc).exists_bound_of_continuous
    (E.signedFirst_continuous χ hχ.continuous)
  obtain ⟨B, _, hB⟩ := E.signedTail_bound χ hχ.continuous hc
  have h := fourHeat_signed_gaussian_limit (E.signedFirst χ)
    (E.signedFirst_continuous χ hχ.continuous) (E.signedFirst_regular χ hχ2)
    (E.signedFirst_zero χ he) (E.signedFirst_fderiv_zero χ hχ2 he) C hC
    (E.signedTail χ) (E.signedTail_continuous χ hχ.continuous) B 1 zero_lt_one hB
  have hval : (1 / (64 * Real.pi ^ 2)) *
      ((∑ i, fderiv ℝ (fderiv ℝ (E.signedFirst χ)) 0 (coordinateVector i) (coordinateVector i)) +
        E.signedTail χ 0 0) = curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, f⟩) := by
    rw [E.signedFirst_hessian_trace χ hχ2 hχ0, E.signedTail_zero χ hχ0,
      E.first_amplitude_signed_gram he, ← E.second_amplitude_signature_density hRic]
    have ha := E.second_amplitude_signature_polynomial
    field_simp
    linarith only [ha]
  rwa [hval] at h

theorem HeatNormalBundleExtension.signed_gaussian_limit
    {f : OrthonormalFrame g c} {D : HeatNormalFrameData g o c ⟨c, f⟩}
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ)
    (hχ : ContDiff ℝ 4 χ) (hc : HasCompactSupport χ) (hχ0 : χ 0 = 1)
    (hRic : RicciThree g) :
    Tendsto (fun t : ℝ => ∫ x : FourSpace, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o ⟨c, f⟩ x * χ x ^ 2 *
        heatSignedGram (heatNormalMatrixPolynomial E t x) (heatNormalMatrixPolynomial E t x)))
      (𝓝[>] 0) (𝓝 (curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, f⟩))) := by
  simpa only [heatNormalMatrixPolynomial_signed] using
    E.signed_reduced_gaussian_limit χ hχ hc hχ0 hRic

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal parametrix solves the weak Hodge evolution equation
with its constructed, small L2 residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.operator_pairing
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (t : ℝ) (l : Fin 6)
    (hf : P.column E t l ∈ twoFormHodgeDomain hRic)
    (hgen : twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (v : smoothTwoForms o) :
    inner ℝ (P.operatorColumn E t l) (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) =
      inner ℝ (P.column E t l)
        (smoothTwoFormToL2 (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o)) := by
  have h := twoFormHodgeGenerator_symmetric hRic ⟨P.column E t l, hf⟩
    ⟨smoothTwoFormToL2 (v : SmoothL2TwoForm o), smoothTwoForm_mem_hodgeDomain hRic v⟩
  rw [hgen, twoFormHodgeGenerator_smooth] at h
  exact h

theorem HeatNormalParametrixData.weak_evolution
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (t : ℝ) (ht : 0 < t) (l : Fin 6)
    (hf : P.column E t l ∈ twoFormHodgeDomain hRic)
    (hgen : twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (v : smoothTwoForms o) :
    HasDerivAt (fun s => inner ℝ (P.column E s l) (smoothTwoFormToL2 (v : SmoothL2TwoForm o)))
      (inner ℝ (P.residual E t l) (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) -
        inner ℝ (P.column E t l)
          (smoothTwoFormToL2 (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o))) t := by
  have hd := heatNormalGlobalParametrixColumn_weak_deriv E P.chart P.exponential
    P.in_chart P.point_regular P.inside_radius P.cutoff
    (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact P.cutoff_support t ht l
    (v : SmoothL2TwoForm o)
  have hp := P.operator_pairing E hRic t l hf hgen v
  have hr : inner ℝ (P.residual E t l) (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) -
      inner ℝ (P.column E t l)
        (smoothTwoFormToL2 (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o)) =
      inner ℝ (P.timeColumn E t l) (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) := by
    rw [P.residual_eq E t l, inner_add_left, hp]
    ring
  rw [hr]
  exact hd

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory11
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Each actual smooth Hodge eigenmode satisfies the scalar forced heat
equation for the constructed normal parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.eigen_evolution
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (t : ℝ) (ht : 0 < t) (l : Fin 6)
    (hf : P.column E t l ∈ twoFormHodgeDomain hRic)
    (hgen : twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (i : TwoFormEigenIndex (o := o) hRic) :
    HasDerivAt (fun s => inner ℝ (P.column E s l) (twoFormEigenvector hRic i))
      (inner ℝ (P.residual E t l) (twoFormEigenvector hRic i) -
        (i.1.val⁻¹ - 1) * inner ℝ (P.column E t l) (twoFormEigenvector hRic i)) t := by
  obtain ⟨v, hv, hLv⟩ := twoFormEigenvector_smooth hRic i
  have hL : smoothTwoFormToL2 (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o) =
      (i.1.val⁻¹ - 1) • twoFormEigenvector hRic i := by
    have heq : (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o) =
        (i.1.val⁻¹ - 1) • (v : SmoothL2TwoForm o) := hLv
    calc
      _ = smoothTwoFormToL2 ((i.1.val⁻¹ - 1) • (v : SmoothL2TwoForm o)) :=
        congrArg smoothTwoFormToL2 heq
      _ = (i.1.val⁻¹ - 1) • smoothTwoFormToL2 (v : SmoothL2TwoForm o) := map_smul _ _ _
      _ = _ := congrArg ((i.1.val⁻¹ - 1) • ·) hv.symm
  have h := P.weak_evolution E hRic t ht l hf hgen v
  rw [hL, real_inner_smul_right, ← hv] at h
  exact h

theorem HeatNormalParametrixData.normalized_eigen_evolution
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (t : ℝ) (ht : 0 < t) (l : Fin 6)
    (hf : P.column E t l ∈ twoFormHodgeDomain hRic)
    (hgen : twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (i : TwoFormEigenIndex (o := o) hRic) :
    HasDerivAt (fun s => inner ℝ (P.normalizedColumn E s l) (twoFormEigenvector hRic i))
      (inner ℝ (P.normalizedResidual E t l) (twoFormEigenvector hRic i) -
        (i.1.val⁻¹ - 1) * inner ℝ (P.normalizedColumn E t l) (twoFormEigenvector hRic i)) t := by
  have h := (P.eigen_evolution E hRic t ht l hf hgen i).const_mul ((normalizedChartFactor g).toReal)⁻¹
  simpa only [HeatNormalParametrixData.normalizedColumn, heatNormalizedParametrixColumn,
    HeatNormalParametrixData.column, HeatNormalParametrixData.normalizedResidual,
    real_inner_smul_left, mul_sub, mul_left_comm] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form heat residual is combined before taking its L2 norm. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.oneResidual_norm_le
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (B : ℝ) (hB : 0 ≤ B) (t : ℝ) (ht : 0 < t)
    (h : ∀ x k l, |deriv (fun s => heatNormalOneCutoffParametrix E P.cutoff s x k l) t +
      fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
        (fun y q => heatNormalOneCutoffParametrix E P.cutoff t y q l) x k| ≤ B * t)
    (l : Fin 4) : ‖P.oneResidual E t l‖ ≤ 4 * B * t := by
  rw [P.oneResidual_as_amplitude E t l]
  apply (heatNormalOneAmplitudeL2_norm_le P.chart P.exponential P.in_chart P.point_regular
    P.inside_radius _ _ _ _ (4 * (B * t)) (by positivity)
    (fun x => heatNormalOneResidualColumn_bound E P.cutoff t ht B h l x)).trans_eq
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact scalar parametrix satisfies the forced heat ODE
in every eigenmode. Its forcing is its genuine time-minus-Laplacian residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

variable [SecondCountableTopology M]
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarEvolution_probability
theorem HeatScalarChartData.normalized_initial_eigen (P : HeatScalarChartData D)
    (i : ScalarBaseEigenIndex g o d) :
    Tendsto (fun t => inner ℝ (P.normalizedColumn t) (scalarBaseEigenvector g o d i))
      (𝓝[Set.Ioi 0] 0) (𝓝 ((scalarBaseEigenfunction g o d i).val e.base)) := by
  let f : C(M, ℝ) := ⟨(scalarBaseEigenfunction g o d i).val,
    (scalarBaseEigenfunction g o d i).property.continuous⟩
  have hf : ContinuousMap.toLp 2 (normalizedVolume g) ℝ f = scalarBaseEigenvector g o d i :=
    (scalarBaseEigenfunction_L2 g o d i).symm
  change Tendsto _ _ (𝓝 (f e.base))
  simpa only [hf] using P.normalizedColumn_initial f

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single bound for the actual signed local Gaussian integral over a
compact family of initial frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformSignedIntegral_bound (E : HeatFamilySmoothCoefficients) (r : ℝ) (hr : 0 < r)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ ball 0 r) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ D ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonNormalMember g o c E r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖∫ x : FourSpace, fourHeatGaussian t x ^ 2 *
        (frameExponentialJacobian g o e x * χ x ^ 2 *
          heatSignedGram (heatNormalMatrixPolynomial N.extension t x)
            (heatNormalMatrixPolynomial N.extension t x))‖ ≤ D := by
  obtain ⟨C, hC, hb⟩ := heatUniformSignedFirst_quadratic (g := g) (o := o) (c := c)
    E r hr χ hχ hχs K hK
  obtain ⟨B, hB, ht⟩ := heatFamilySignedTail_bound E χ hχ.continuous hc K hK
  refine ⟨(32 * C + B) / (64 * Real.pi ^ 2), by positivity, ?_⟩
  intro e N hq t htt
  simp_rw [heatNormalMatrixPolynomial_signed]
  apply fourHeat_signed_gaussian_bound _ _ C B t hC hB htt.1 (hb e N hq)
  intro x
  rw [N.signedTail_family χ hχs t x]
  exact ht _ hq t ⟨htt.1.le, htt.2⟩ x

end
end PositiveEinsteinFour.Geometry
end


section

/-! One O(t) cutoff-residual constant works for every actual normal frame
in a compact coordinate neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformOneCutoffResidual (E : HeatFamilyOneCoefficients) (r : ℝ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ ball 0 r) (hχb : ∀ x, |χ x| ≤ 1)
    (s : ℝ) (hs : 0 < s) (hinner : ∀ x ∈ ball 0 s, χ x = 1)
    (hRic : RicciThree g) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c E r e),
      frameCoordinateState g c e ∈ K → e ∈ o.positive →
      ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
        |deriv (fun v => heatNormalOneCutoffParametrix N.one χ v x k l) t +
          fourHeatOneOperator (N.one.base.a x) (N.one.base.b x)
            (N.one.B x) (N.one.C x)
            (fun y q => heatNormalOneCutoffParametrix N.one χ t y q l) x k| ≤ B * t := by
  obtain ⟨C₀, hC₀, hb⟩ := E.lastCoefficient_compact_bound (tsupport χ ×ˢ K) (hc.prod hK)
  obtain ⟨C₁, hC₁, hcom⟩ := heatFamilyOneCommutator_gaussian_bound E χ hχ hc K hK s hs hinner
  let B₀ := C₀ / (16 * Real.pi ^ 2)
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  refine ⟨B₀ + C₁, add_nonneg hB₀ hC₁, ?_⟩
  intro e N hq he t ht x k l
  let A := N.one
  let q := frameCoordinateState g c e
  let u : Fin 4 → FourSpace → Fin 4 → ℝ := fun m y a => A.amplitude m y a l
  have hu (m : Fin 4) (a : Fin 4) : ContDiff ℝ 2 (fun y => u m y a) :=
    (A.amplitude_regular m (by omega) a l).of_le (by norm_num)
  by_cases hx : x ∈ tsupport χ
  · have hxr := hχs hx
    have hsym (i j : Fin 4) : A.base.a x i j = A.base.a x j i := by
      rw [N.one_base, (N.normal.actual x hxr).1]
      exact congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    let Q := deriv (fun v => heatNormalOneParametrix A v x k l) t +
      fourHeatOneOperator (A.base.a x) (A.base.b x) (A.B x) (A.C x)
        (fun y a => heatNormalOneParametrix A t y a l) x k
    have hQ : |Q| ≤ B₀ * t := by
      have hres := N.one_parametrix_residual hRic he x hxr t ht.1 k l
      change Q = fourHeatGaussian t x * t ^ 3 * E.lastCoefficient (x, q) k l at hres
      rw [hres, abs_mul, abs_mul, abs_of_pos (fourHeatGaussian_pos t ht.1 x),
        abs_of_pos (pow_pos ht.1 3)]
      calc
        _ ≤ (fourHeatGaussian t x * t ^ 3) * C₀ :=
          mul_le_mul_of_nonneg_left (hb (x, q) ⟨hx, hq⟩ k l)
            (mul_nonneg (fourHeatGaussian_pos t ht.1 x).le (pow_nonneg ht.1.le 3))
        _ ≤ (fourHeatGaussian t 0 * t ^ 3) * C₀ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (fourHeatGaussian_le_diagonal t ht.1 x)
              (pow_nonneg ht.1.le 3)) hC₀
        _ = C₀ * (t ^ (1 + 2) * fourHeatGaussian t 0) := by ring
        _ = B₀ * t := by rw [fourHeatGaussian_diagonal_power 1 t ht.1, pow_one]; dsimp [B₀]; ring
    have hid := heatNormalOneCutoffParametrix_residual_identity A χ t ht.1 x hχ.contDiffAt
      (A.base.a x) (A.base.b x) (A.B x) (A.C x) hsym k l
    have hscaled := fourHeatOneScaledCommutator_identity A.base.a A.base.b A.B χ u hu t ht.1 x k
    have hfamily : fourHeatOneScaledCommutator A.base.a A.base.b A.B χ u t x k =
        heatFamilyOneCommutator E χ t (x, q) k l := by
      have hu' : u = fun (m : Fin 4) y a => E.amplitude m (y, q) a l := by
        funext m y a
        exact congrArg (fun f : FourSpace → Mat4 => f y a l)
          (N.one_amplitude_family m (by omega))
      rw [hu']
      change fourHeatOneScaledCommutator N.one.base.a N.one.base.b N.one.B χ _ t x k = _
      rw [N.one_base, N.normal.a_family, N.normal.b_family, N.one_B_family]
      rfl
    have hid' : deriv (fun v => heatNormalOneCutoffParametrix A χ v x k l) t +
        fourHeatOneOperator (A.base.a x) (A.base.b x) (A.B x) (A.C x)
          (fun y a => heatNormalOneCutoffParametrix A χ t y a l) x k =
        χ x * Q + (fourHeatGaussian t x / t) * heatFamilyOneCommutator E χ t (x, q) k l := by
      rw [← hfamily, ← hscaled, hid]
      dsimp only [Q, heatNormalOneParametrix, u]
      ring
    change |deriv (fun v => heatNormalOneCutoffParametrix A χ v x k l) t + _| ≤ _
    rw [hid']
    calc
      _ ≤ |χ x * Q| + |(fourHeatGaussian t x / t) * heatFamilyOneCommutator E χ t (x, q) k l| :=
        abs_add_le _ _
      _ ≤ B₀ * t + C₁ * t := by
        apply add_le_add _ (hcom q hq t ht x k l)
        rw [abs_mul]
        exact (mul_le_mul (hχb x) hQ (abs_nonneg Q) (by norm_num)).trans_eq (one_mul _)
      _ = _ := by ring
  · rw [heatNormalOneCutoffParametrix_residual_zero N.one χ t x hx, abs_zero]
    exact mul_nonneg (add_nonneg hB₀ hC₁) ht.1.le

end
end PositiveEinsteinFour.Geometry
end


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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.heatEulerCommon_probability
theorem exists_heatEulerCommonChart (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g)
    (hepos : e ∈ o.positive) :
    ∃ P : HeatEulerChartData D,
      (∀ x ∈ tsupport P.scalar.cutoff, P.scalar.extension.a x = (heatNormalMetric g o e x)⁻¹) ∧
      (∀ x ∈ tsupport P.scalar.cutoff, P.scalar.extension.b x = heatNormalDrift g o e x) ∧
      (∀ x ∈ tsupport P.scalar.cutoff, 0 < (heatNormalMetric g o e x).det) ∧
      (∃ B ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.scalar.residual t‖ ≤ B * t) ∧
      (∀ t l (v : smoothCovariantFields M 1),
        inner ℝ (P.normal.oneColumn P.bundle.oneCompanion t l)
          (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.normal.oneOperatorColumn P.bundle.oneCompanion t l) (smoothOneFormL2Linear v)) ∧
      (∃ B ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
        ‖P.normal.oneResidual P.bundle.oneCompanion t l‖ ≤ B * t) ∧
      (∀ t l, ∃ hf : P.normal.column P.bundle t l ∈ twoFormHodgeDomain hRic,
        twoFormHodgeGenerator hRic ⟨P.normal.column P.bundle t l, hf⟩ =
          P.normal.operatorColumn P.bundle t l) ∧
      (∃ B ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
        ‖P.normal.residual P.bundle t l‖ ≤ B * t) := by
  obtain ⟨S⟩ := exists_heatNormalExtension 10 g o e
  obtain ⟨E₀⟩ := exists_heatNormalBundleExtension D
  let E : HeatNormalBundleExtension D := { E₀ with base := S }
  obtain ⟨rT, hrT, hT⟩ := S.scalarParametrix_residual hRic hepos
  obtain ⟨r₂, hr₂, h₂⟩ := E.parametrix_domain_near he hRic
  obtain ⟨b₂, hb₂, hbound₂⟩ := heatNormalCutoffParametrix_bound_of_support E hRic hepos
  obtain ⟨r₁, hr₁, h₁⟩ := E.oneCompanion.compact_operator_pairing_near he hRic
  obtain ⟨b₁, hb₁, hbound₁⟩ := heatNormalOneCutoffParametrix_bound_of_support
    E.oneCompanion hRic hepos
  have hdet : ContDiffAt ℝ ∞ (fun x => (heatNormalMetric g o e x).det) 0 := by
    simp only [Matrix.det_apply']
    exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul
      (contDiffAt_prod fun i _ => heatNormalMetric_smoothAt_zero g o e (σ i) i)
  have hpos : ∀ᶠ x in 𝓝 (0 : FourSpace), 0 < (heatNormalMetric g o e x).det :=
    hdet.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds (show
      (0 : ℝ) < (heatNormalMetric g o e 0).det from by
      rw [heatNormalMetric_zero, Matrix.det_one]; exact zero_lt_one))
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), S.a x = (heatNormalMetric g o e x)⁻¹ ∧
      S.b x = heatNormalDrift g o e x ∧ 0 < (heatNormalMetric g o e x).det ∧
      x ∈ ball 0 rT ∧ x ∈ ball 0 r₂ ∧ x ∈ ball 0 b₂ ∧
      x ∈ ball 0 r₁ ∧ x ∈ ball 0 b₁ := by
    filter_upwards [S.a_near, S.b_near, hpos, ball_mem_nhds (0 : FourSpace) hrT,
      ball_mem_nhds (0 : FourSpace) hr₂, ball_mem_nhds (0 : FourSpace) hb₂,
      ball_mem_nhds (0 : FourSpace) hr₁, ball_mem_nhds (0 : FourSpace) hb₁]
      with x ha hb hd hT h₂ hb₂ h₁ hb₁
    exact ⟨ha, hb, hd, hT, h₂, hb₂, h₁, hb₁⟩
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨rC, C, hrC, hC, hE, hI, hCt, hP, hD⟩ := exists_heatNormalFrameChart D he
  let R := min r₀ rC
  have hR : 0 < R := lt_min hr₀ hrC
  let χ := heatNormalChartBump R hR
  have hsR : tsupport χ ⊆ ball (0 : FourSpace) R := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by change R / 2 < R; linarith)
  have hsC : tsupport χ ⊆ C.source := by
    rw [hC]
    exact hsR.trans (ball_subset_ball (min_le_right _ _))
  let N : HeatNormalParametrixData D := {
    chart := C, exponential := hE, in_chart := hCt,
    point_regular := hP.of_le (by norm_num), inside_radius := hD,
    cutoff := χ, cutoff_regular := χ.contDiff, cutoff_compact := χ.hasCompactSupport,
    cutoff_support := hsC, cutoff_zero := χ.one_of_mem_closedBall
      (mem_closedBall_self (by change 0 ≤ R / 4; positivity)) }
  let P : HeatEulerChartData D := {
    base := S, prototype := E₀, normal := N,
    point_regular := hP, inverse_regular := hI }
  have hnear (x : FourSpace) (hx : x ∈ tsupport χ) :=
    hball ((ball_subset_ball (min_le_left r₀ rC)) (hsR hx))
  have ha : ∀ x ∈ tsupport P.scalar.cutoff,
      P.scalar.extension.a x = (heatNormalMetric g o e x)⁻¹ := fun x hx => (hnear x hx).1
  have hb : ∀ x ∈ tsupport P.scalar.cutoff,
      P.scalar.extension.b x = heatNormalDrift g o e x := fun x hx => (hnear x hx).2.1
  have hd : ∀ x ∈ tsupport P.scalar.cutoff,
      0 < (heatNormalMetric g o e x).det := fun x hx => (hnear x hx).2.2.1
  have hχ : ∀ x, |χ x| ≤ 1 := fun x => by
    rw [abs_of_nonneg χ.nonneg]; exact χ.le_one
  have hi : ∀ x ∈ ball 0 (R / 4), χ x = 1 :=
    fun x hx => χ.one_of_mem_closedBall (ball_subset_closedBall hx)
  refine ⟨P, ha, hb, hd, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨B, hB, hbound⟩ := P.scalar.residualAmplitude_bound ha hχ (R / 4)
      (by positivity) hi (fun x hx t ht => hT x (hnear x hx).2.2.2.1 t ht)
    refine ⟨‖ContinuousMap.toLp (E := ℝ) 2 (normalizedVolume g) ℝ‖ * B,
      mul_nonneg (norm_nonneg _) hB, fun t ht => ?_⟩
    exact (P.scalar.residual_norm_le ha hb hd t (B * t) (mul_nonneg hB ht.1.le)
      (hbound t ht)).trans_eq (mul_assoc _ _ _).symm
  · intro t l v
    exact h₁ C hE hCt N.point_regular hD (heatNormalOneCutoffColumn E.oneCompanion χ t l)
      (heatNormalOneCutoffColumn_regular E.oneCompanion χ N.cutoff_regular t l)
      (N.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
        (heatNormalOneCutoffColumn_support E.oneCompanion χ t l))
      ((heatNormalOneCutoffColumn_support E.oneCompanion χ t l).trans hsC)
      ((heatNormalOneCutoffColumn_support E.oneCompanion χ t l).trans
        (fun x hx => (hnear x hx).2.2.2.2.2.2.1)) v
  · obtain ⟨B, hB, hbound⟩ := hbound₁ χ (N.cutoff_regular.of_le (by norm_num))
      N.cutoff_compact (fun x hx => (hnear x hx).2.2.2.2.2.2.2) hχ
      (R / 4) (by positivity) hi
    exact ⟨4 * B, by positivity, fun t ht l =>
      N.oneResidual_norm_le E.oneCompanion B hB t ht.1 (hbound t ht) l⟩
  · intro t l
    exact h₂ C hE hCt N.point_regular hD χ N.cutoff_regular N.cutoff_compact hsC
      (fun x hx => (hnear x hx).2.2.2.2.1) t l
  · obtain ⟨B, hB, hbound⟩ := hbound₂ χ (N.cutoff_regular.of_le (by norm_num))
      N.cutoff_compact (fun x hx => (hnear x hx).2.2.2.2.2.1) hχ
      (R / 4) (by positivity) hi
    exact ⟨6 * B, by positivity, fun t ht l =>
      N.residual_norm_le E t ht.1 B hB (hbound t ht) l⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal parametrix has the exact Duhamel formula in every
smooth Hodge eigenmode, with its proved delta initial value. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.normalized_eigen_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (he : e.base ∈ (chartAt FourSpace c).source)
    (hgen : ∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 6)
    (i : TwoFormEigenIndex (o := o) hRic) :
    inner ℝ (P.normalizedColumn E t l) (twoFormEigenvector hRic i) =
      Real.exp (-(i.1.val⁻¹ - 1) * t) *
        twoFormFrameValue o (twoFormEigenSection hRic i).val e l +
      ∫ s in (0 : ℝ)..t, Real.exp (-(i.1.val⁻¹ - 1) * (t - s)) *
        inner ℝ (P.normalizedResidualZero E s l) (twoFormEigenvector hRic i) := by
  apply heat_forced_scalar_formula _ _ _ _ t ht.1
  · exact ((P.normalizedResidualZero_continuous E B hB l).mono
      (Icc_subset_Icc le_rfl ht.2)).inner continuousOn_const
  · have h := P.normalized_initial E he l (twoFormEigenSection hRic i : SmoothL2TwoForm o)
    simpa only [twoFormEigenSection_L2] using h
  · intro s hs
    obtain ⟨hf, hgf⟩ := hgen s l
    rw [P.normalizedResidualZero_eq E s hs l]
    exact P.normalized_eigen_evolution E hRic s hs l hf hgf i

end
end PositiveEinsteinFour.Geometry
end


section

/-! The genuine scalar spectral heat column equals the constructed
normal parametrix minus its actual Bochner forcing convolution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalar_eq_of_eigen_pairing (v w : Lp ℝ 2 (normalizedVolume g))
    (h : ∀ i : ScalarBaseEigenIndex g o d,
      inner ℝ v (scalarBaseEigenvector g o d i) = inner ℝ w (scalarBaseEigenvector g o d i)) :
    v = w := by
  apply (scalarBaseEigenbasis g o d).repr.injective
  apply lp.ext
  funext i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, scalarBaseEigenbasis_apply]
  exact (real_inner_comm _ _).trans ((h i).trans (real_inner_comm _ _))

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common O(t) bound for the genuine scalar cutoff residual. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformScalarCutoffResidual (F : HeatFamilyOneCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) (hRic : RicciThree g) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → e ∈ o.positive → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
        |(N.scalarData hr).residualAmplitude t x| ≤ B * t := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  obtain ⟨A, hApos, hA⟩ := F.base.scalarLastCoefficient_compact_bound
    (tsupport χ ×ˢ K) ((heatNormalChartBump r hr).hasCompactSupport.prod hK)
  obtain ⟨B₁, hB₁, hb₁⟩ := heatFamilyScalarCommutator_gaussian_bound F.base χ
    (heatNormalChartBump r hr).contDiff
    (heatNormalChartBump r hr).hasCompactSupport K hK (r / 4) (by positivity)
    (fun x hx => (heatNormalChartBump r hr).one_of_mem_closedBall (ball_subset_closedBall hx))
  let B₀ := A / (16 * Real.pi ^ 2)
  have hB₀ : 0 ≤ B₀ := by positivity
  refine ⟨B₀ + B₁, add_nonneg hB₀ hB₁, ?_⟩
  intro e N hq he t ht x
  let P := N.scalarData hr
  let E := P.extension
  let u : Fin 4 → FourSpace → Fin 6 → ℝ := fun m y _ => E.scalarAmplitude m y
  have hu (m : Fin 4) (q : Fin 6) : ContDiff ℝ 2 (fun y => u m y q) :=
    (E.scalarAmplitude_regular m (by omega)).of_le (by norm_num)
  have hs : tsupport P.cutoff ⊆ ball 0 r := by
    exact P.cutoff_support.trans (by
      rw [show P.chart = (N.normal.parametrixData hr).chart from rfl, N.normal.parametrixData_source hr])
  by_cases hx : x ∈ tsupport P.cutoff
  · have hsym (i j : Fin 4) : E.a x i j = E.a x j i := by
      rw [(N.scalarData_actual hr).1 x hx]
      exact congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    have hQ : |deriv (fun v => E.scalarParametrix v x) t +
        fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x| ≤ B₀ * t := by
      have hres := N.scalar_parametrix_residual hRic he x (hs hx) t ht.1
      change deriv (fun v => E.scalarParametrix v x) t +
        fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x = _ at hres
      rw [hres, abs_mul, abs_mul,
        abs_of_pos (fourHeatGaussian_pos t ht.1 x), abs_of_pos (pow_pos ht.1 3)]
      have hFx := hA (x, frameCoordinateState g c e) ⟨hx, hq⟩
      calc
        _ ≤ (fourHeatGaussian t x * t ^ 3) * A :=
          mul_le_mul_of_nonneg_left hFx
            (mul_nonneg (fourHeatGaussian_pos t ht.1 x).le (pow_nonneg ht.1.le 3))
        _ ≤ (fourHeatGaussian t 0 * t ^ 3) * A :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (fourHeatGaussian_le_diagonal t ht.1 x)
              (pow_nonneg ht.1.le 3)) hApos
        _ = B₀ * t := by
          have hg := fourHeatGaussian_diagonal_power 1 t ht.1
          norm_num only [Nat.reduceAdd, pow_one] at hg
          dsimp only [B₀]
          calc
            _ = A * (t ^ 3 * fourHeatGaussian t 0) := by ring
            _ = _ := by rw [hg]; ring
    have hcut := fourHeatLocalOperator_cutoff (E.a x) (E.b x) P.cutoff
      (E.scalarParametrix t) x hsym (P.cutoff_regular.contDiffAt.of_le (by norm_num))
      ((E.scalarParametrix_regular t).contDiffAt.of_le (by norm_num))
    have hscaled := fourHeatScaledCommutator_identity E.a E.b (fun _ => 0)
      P.cutoff u hu t ht.1 x 0
    have hz (i : Fin 4) (q : Fin 6) : (0 : Fin 4 → HeatMat6) i 0 q = 0 := rfl
    simp only [fourHeatBundlePolynomial, u, hz, zero_mul,
      Finset.sum_const_zero, add_zero] at hscaled
    have hdt : deriv (fun v => E.scalarParametrix v x) t =
        fourHeatGaussianPolynomialTime (fun m => E.scalarAmplitude m) t x :=
      (fourHeatGaussianPolynomial_hasDerivAt
        (fun m => E.scalarAmplitude m) t ht.1 x).deriv
    have hid : P.residualAmplitude t x =
        P.cutoff x * (deriv (fun v => E.scalarParametrix v x) t +
          fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x) +
        (fourHeatGaussian t x / t) *
          fourHeatScaledCommutator E.a E.b (fun _ => 0) P.cutoff u t x 0 := by
      change P.cutoff x * fourHeatGaussianPolynomialTime
        (fun m => E.scalarAmplitude m) t x +
        fourHeatLocalOperator (E.a x) (E.b x) 0
          (fun y => P.cutoff y * E.scalarParametrix t y) x = _
      rw [hcut, hdt]
      change fourHeatLocalOperator (E.a x) (E.b x) 0 P.cutoff x * E.scalarParametrix t x -
        2 * (∑ i, ∑ j, E.a x i j * partialDeriv P.cutoff i x *
          partialDeriv (E.scalarParametrix t) j x) = _ at hscaled
      linarith [hscaled]
    rw [hid]
    calc
      _ ≤ |P.cutoff x * (deriv (fun v => E.scalarParametrix v x) t +
          fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x)| +
          |(fourHeatGaussian t x / t) *
            fourHeatScaledCommutator E.a E.b (fun _ => 0) P.cutoff u t x 0| := abs_add_le _ _
      _ ≤ B₀ * t + B₁ * t := by
        apply add_le_add
        · rw [abs_mul]
          have hχ : |P.cutoff x| ≤ 1 := by
            change |(heatNormalChartBump r hr) x| ≤ 1
            rw [abs_of_nonneg (heatNormalChartBump r hr).nonneg]
            exact (heatNormalChartBump r hr).le_one
          exact (mul_le_mul hχ hQ (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
        · have hfamily : fourHeatScaledCommutator E.a E.b (fun _ => 0) P.cutoff u t x 0 =
              heatFamilyScalarCommutator F.base χ t (x, frameCoordinateState g c e) := by
            have hu' : u = fun (m : Fin 4) y _ => F.base.scalarAmplitude m (y, frameCoordinateState g c e) := by
              funext m y k
              exact congrFun (N.scalar_amplitude_family m (by omega)) y
            rw [hu']
            change fourHeatScaledCommutator N.normal.extension.base.a N.normal.extension.base.b _ _ _ _ _ _ = _
            rw [N.normal.a_family, N.normal.b_family]
            rfl
          rw [hfamily]
          exact hb₁ _ hq t ht x

      _ = _ := by ring
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (P.residualAmplitude_support t h)),
      abs_zero]
    exact mul_nonneg (add_nonneg hB₀ hB₁) ht.1.le


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

/-! In the unit-Weyl branch, actual self-dual harmonic forms are parallel.
The conclusion is derived from the global Bochner identity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance parallelHarmonicAddGroup_rc90d1f_1 : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _
local instance parallelPositiveAddGroup_rc90d1f_1 (hRic : RicciThree g) :
    AddCommGroup (smoothHarmonicPositive (o := o) hRic) := Submodule.addCommGroup _
theorem halfFlat_positive_harmonic_covariantEnergy_zero (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1) (u : smoothHarmonicPositive (o := o) hRic) :
    smoothTwoFormCovariantEnergy u.val.val u.val.val = 0 := by
  have hstar (x : M) : twoFormHodge (u.val.val.val x) = u.val.val.val x :=
    congrArg (fun v : smoothHarmonicTwoForms (o := o) => v.val.val x)
      (smoothHarmonicPositive_star hRic u)
  have hC : smoothTwoFormL2Inner (smoothTwoFormCurvature u.val.val) u.val.val ≤
      3 * smoothTwoFormL2Inner u.val.val u.val.val := by
    rw [smoothTwoFormL2Inner, smoothTwoFormL2Inner, ← integral_const_mul]
    apply integral_mono (smoothTwoForm_pairing_integrable _ _)
      ((smoothTwoForm_pairing_integrable u.val.val u.val.val).const_mul 3)
    intro x
    change inner ℝ (twoFormCurvatureAction (twoFormMetricCurvatureTensor g ⟨x,o.frame x⟩)
      (u.val.val.val x)) (u.val.val.val x) ≤ 3 * inner ℝ (u.val.val.val x) (u.val.val.val x)
    rw [real_inner_comm]
    exact halfFlat_unit_curvature_bound hRic hminus hnorm x _ (hstar x)
  have hE := smoothTwoForm_Weitzenbock hRic u.val.val
  rw [smoothHarmonicTwoForm_energy_zero u.val.val u.val.property] at hE
  have hnonneg := smoothTwoFormCovariantEnergy_nonneg u.val.val
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The dimension-one half-flat branch has an actual global parallel
self-dual two-form of norm sqrt(2), constructed from its harmonic space. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.unitFormHarmonicAddGroup
local instance unitFormPositiveAddGroup (hRic : RicciThree g) :
    AddCommGroup (smoothHarmonicPositive (o := o) hRic) := Submodule.addCommGroup _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The curvature eigenvalue of an actual parallel two-form. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem parallel_twoForm_curvature_eigenvalue (hRic : RicciThree g)
    (u : smoothTwoForms o)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o u.val e = 0)
    (e : FrameBundle g) :
    twoFormCurvatureAction (twoFormMetricCurvatureTensor g e)
      (twoFormFrameValue o u.val e) = (3 : ℝ) • twoFormFrameValue o u.val e := by
  have hzero := (smoothHodgeLaplacian_eq_zero_iff hRic u).mpr
    (parallel_twoForm_harmonic u hz)
  have h := smoothHodgeLaplacian_framed hRic u e
  rw [hzero, parallel_twoForm_roughTrace_zero u hz e, sub_zero] at h
  have hv : twoFormFramedValue o (0 : smoothTwoForms o).val e = 0 := by
    rw [twoFormFramedValue_eq]
    change twoFormTensorLinear (twoFormFrameActionLinear _ 0) = 0
    rw [map_zero, map_zero]
  have hc := twoFormCurvatureField_frame (o := o) u.val e
  change twoFormFrameValue o (smoothTwoFormCurvature u).val e = _ at hc
  rw [hv, twoFormFramedValue_eq, twoFormFramedValue_eq, hc] at h
  apply twoFormTensor_injective
  change twoFormTensorLinear _ = twoFormTensorLinear ((3 : ℝ) • _)
  rw [map_smul]
  ext a
  have ha := congrFun h a
  simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ha
  change twoFormTensor (twoFormCurvatureAction (twoFormMetricCurvatureTensor g e)
      (twoFormFrameValue o u.val e)) a = 3 * twoFormTensor (twoFormFrameValue o u.val e) a
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The unit parallel form determines the actual remaining Weyl block. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular TraceHessian Matrix
open scoped BigOperators Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem halfFlat_parallel_form_weyl (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    let a := twoFormFrameValue o w.val e
    plusWeyl g e.base e.frame =
      (3 : ℝ) • Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2] - 1 := by
  let a := twoFormFrameValue o w.val e
  let T := plusWeyl g e.base e.frame
  let v : Fin 3 → ℝ := ![a 0,a 1,a 2]
  have hs : twoFormHodge a = a := by
    dsimp only [a]
    rw [← twoFormFrameValue_hodge o w.val e he]
    congr 1
    exact funext hstar
  have ha : ‖a‖ ^ 2 = 2 := by rw [twoFormFrameValue_norm, hw]
  have h3 : a 3 = a 2 := congrArg (fun b : TwoFormFour => b 2) hs
  have h4 : a 4 = -a 1 := by
    have h := congrArg (fun b : TwoFormFour => b 1) hs
    change -a 4 = a 1 at h
    linarith
  have h5 : a 5 = a 0 := congrArg (fun b : TwoFormFour => b 0) hs
  have hv : dotProduct v v = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq a
    simp [Fin.sum_univ_succ, h3, h4, h5] at h
    simp [v, dotProduct, Fin.sum_univ_succ]
    nlinarith only [h,ha]
  have hlast : ∀ i j k l, twoFormMetricCurvatureTensor g e ![i,j,l,k] =
      -twoFormMetricCurvatureTensor g e ![i,j,k,l] := by
    intro i j k l
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_lastSkew e.frame i j k l
  have hm : minusWeyl g e.base e.frame = 0 := by
    apply (normalizedBlockNorm_eq_zero_iff _).mp
    rw [← actual_minusNorm_frame o e he]
    exact (minusNorm_eq_zero_iff o e.base).mpr (hminus e.base)
  have hR : twoFormMetricCurvatureTensor g e = fun b =>
      einsteinCurvatureTensor T 0 (b 0) (b 1) (b 2) (b 3) := by
    funext b
    have hb : b = ![b 0,b 1,b 2,b 3] := by ext i; fin_cases i <;> rfl
    rw [hb]
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    rw [actual_einstein_decomposition e.frame hRic, hm]
    rfl
  have hEig := parallel_twoForm_curvature_eigenvalue hRic w hz e
  change twoFormCurvatureAction (twoFormMetricCurvatureTensor g e) a = (3 : ℝ) • a at hEig
  rw [← twoFormCurvatureMatrix_apply _ hlast, hR] at hEig
  change twoFormMatrixMul (twoFormCurvatureMatrix (fun b =>
    einsteinCurvatureTensor T 0 (b 0) (b 1) (b 2) (b 3))) a = (3 : ℝ) • a at hEig
  rw [halfFlat_curvature_matrix_positive T a hs] at hEig
  have hIv : (1 + T) *ᵥ v = (3 : ℝ) • v := by
    ext i
    fin_cases i
    · exact congrArg (fun b : TwoFormFour => b 0) hEig
    · exact congrArg (fun b : TwoFormFour => b 1) hEig
    · exact congrArg (fun b : TwoFormFour => b 2) hEig
  have hTv : T *ᵥ v = (2 : ℝ) • v := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at hIv
    ext i
    have h := congrFun hIv i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
    linarith
  exact unitWeylProjection_eq_vector T (actual_weyl_symmetric e.frame).1
    (actual_weyl_traceFree e.frame hRic).1 (actual_unit_weyl_polynomial hRic hnorm e he) v hv hTv

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

theorem actualJacobiCurvature_parallel_form (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    let a := twoFormFrameValue o w.val e
    actualJacobiCurvature g e t = (1 / 2 : ℝ) • (1 : NormalMatrix) +
      (3 / 2 : ℝ) • Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2] := by
  let f := parallelFrameFlowMap g 0 t e
  have hf : f ∈ o.positive := (canonicalParallelMetricData_orientation o hRic 0 t e).mpr he
  have hP := halfFlat_parallel_form_weyl hRic hminus hnorm w hstar hw hz f hf
  dsimp only at hP
  rw [parallel_twoForm_frameValue_along_flow w hz e 0 t] at hP
  have hM : minusWeyl g f.base f.frame = 0 := by
    apply (normalizedBlockNorm_eq_zero_iff _).mp
    rw [← actual_minusNorm_frame o f hf]
    exact (minusNorm_eq_zero_iff o f.base).mpr (hminus f.base)
  change 1 + normalCurvatureDeviation g f.base f.frame firstDirection = _
  rw [normalCurvatureDeviation_eq_of_decomposition g f.base f.frame
    (actual_einstein_decomposition f.frame hRic), hP, hM]
  simp only [normalDeviation, rotated, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Jacobi fields and first conjugate radius in the parallel
complex-curvature branch. No model identification is used. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix Jacobi
open scoped BigOperators Manifold ContDiff Matrix.Norms.L2Operator
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualJacobi_parallel_form (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    let a := twoFormFrameValue o w.val e
    let P := Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2]
    (actualJacobiSolution g hRic e).J = complexJacobiPosition P ∧
      (actualJacobiSolution g hRic e).V = complexJacobiVelocity P := by
  let a := twoFormFrameValue o w.val e
  let v : Fin 3 → ℝ := ![a 0,a 1,a 2]
  have hv : dotProduct v v = 1 := unitSelfDual_frame_firstThree w hstar hw e he
  have hP : Matrix.vecMulVec v v * Matrix.vecMulVec v v = Matrix.vecMulVec v v := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hv, one_smul]
  exact (actualJacobiSolution g hRic e).eq_complex_projection _ hP
    (fun t => actualJacobiCurvature_parallel_form hRic hminus hnorm w hstar hw hz e he t)

theorem actualFirstConjugateTime_parallel_form (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    actualFirstConjugateTime g hRic e = complexJacobiRadius := by
  let a := twoFormFrameValue o w.val e
  let v : Fin 3 → ℝ := ![a 0,a 1,a 2]
  have hv : dotProduct v v = 1 := unitSelfDual_frame_firstThree w hstar hw e he
  have hJ : (actualJacobiSolution g hRic e).J =
      complexJacobiPosition (Matrix.vecMulVec v v) :=
    (actualJacobi_parallel_form hRic hminus hnorm w hstar hw hz e he).1
  apply le_antisymm
  · by_contra hnot
    have hc : complexJacobiRadius < actualFirstConjugateTime g hRic e := lt_of_not_ge hnot
    have hu := actualJacobi_isUnit_before_firstConjugate g hRic e _ complexJacobiRadius_pos hc
    rw [hJ] at hu
    have hn := (Matrix.isUnit_iff_isUnit_det _).mp hu
    exact hn.ne_zero (complexJacobiPosition_det_radius v hv)
  · by_contra hnot
    have hc : actualFirstConjugateTime g hRic e < complexJacobiRadius := lt_of_not_ge hnot
    apply actualFirstConjugateTime_singular g hRic e
    rw [hJ]
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    exact isUnit_iff_ne_zero.mpr
      (complexJacobiPosition_det_pos v hv (actualFirstConjugateTime_pos g hRic e) hc).ne'

end
end PositiveEinsteinFour.Geometry
end


section

/-! The complex line tangent is in the actual exponential kernel at the
first conjugate radius. -/

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped BigOperators Manifold ContDiff Matrix.Norms.L2Operator
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_normal_kernel (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (c : M)
    (hc : (parallelFrameFlowMap g 0 complexJacobiRadius e).base ∈ (chartAt FourSpace c).source) :
    let a := twoFormFrameValue o w.val e
    fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z))
      (complexJacobiRadius • coordinateVector 0)
      (WithLp.toLp 2 (Fin.cons 0 ![a 0,a 1,a 2])) = 0 := by
  let a := twoFormFrameValue o w.val e
  let v : Fin 3 → ℝ := ![a 0,a 1,a 2]
  have hv : dotProduct v v = 1 := unitSelfDual_frame_firstThree w hstar hw e he
  have hJ := (actualJacobi_parallel_form hRic hminus hnorm w hstar hw hz e he).1
  rw [(frameExponential_hasFDerivAt g o hRic c e he complexJacobiRadius
    complexJacobiRadius_pos hc).fderiv, hJ]
  change WithLp.toLp 2 ((frameChartMatrix g c (parallelFrameFlowMap g 0 complexJacobiRadius e) *
    jacobiBlockMatrix 1 (complexJacobiRadius⁻¹ •
      complexJacobiPosition (Matrix.vecMulVec v v) complexJacobiRadius)) *ᵥ Fin.cons 0 v) = 0
  rw [← Matrix.mulVec_mulVec, jacobiBlockMatrix_mulVec]
  simp only [Fin.cons_zero, Fin.cons_succ, mul_zero]
  rw [Matrix.smul_mulVec, complexJacobiPosition_radius_mulVec v hv, smul_zero]
  have hzvec : (Fin.cons 0 (0 : Fin 3 → ℝ) : Fin 4 → ℝ) = 0 := by
    ext i
    fin_cases i <;> rfl
  rw [hzvec, Matrix.mulVec_zero, WithLp.toLp_zero]

theorem frameExponential_complex_first_kernel (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (c : M)
    (hc : (parallelFrameFlowMap g 0 complexJacobiRadius e).base ∈ (chartAt FourSpace c).source) :
    fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z))
      (complexJacobiRadius • coordinateVector 0)
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (twoFormMatrix (twoFormFrameValue o w.val e)) (coordinateVector 0)) = 0 := by
  let a := twoFormFrameValue o w.val e
  have hvec : Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (twoFormMatrix a) (coordinateVector 0) =
      -(WithLp.toLp 2 (Fin.cons 0 ![a 0,a 1,a 2])) := by
    ext i
    change ((twoFormMatrix a) *ᵥ Pi.single 0 1) i = _
    rw [Matrix.mulVec_single_one]
    fin_cases i <;> simp [Matrix.col, twoFormMatrix]
  rw [hvec, map_neg, frameExponential_complex_normal_kernel hRic hminus hnorm w hstar hw hz e he c hc,
    neg_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual exponential charts throughout the open complex normal ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_localChart (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : ‖v‖ < complexJacobiRadius) :
    ∃ C : OpenPartialHomeomorph FourSpace M,
      v ∈ C.source ∧ EqOn C (frameExponential g o e) C.source := by
  by_cases hzero : v = 0
  · subst v
    exact frameExponential_localChart g o e
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hzero)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hzero),one_smul]
  have hf : e.rotate (orientedToOrthogonal (directionOrientedMatrix q)) ∈ o.positive :=
    frameRotate_oriented_positive o e he (directionOrientedMatrix q)
  have hp : (q, ‖v‖) ∈ framePolarDomain g hRic e := by
    refine ⟨norm_pos_iff.mpr hzero, ?_⟩
    rw [actualFirstConjugateTime_parallel_form hRic hminus hnorm W hstar hw hz _ hf]
    exact hv
  obtain ⟨C,hC,heq⟩ := frameExponential_polar_localChart g o hRic e he q ‖v‖ hp
  exact ⟨C,hrad ▸ hC,heq⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact minimizing-domain radial mass in the complex-curvature branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}
variable (hRic : RicciThree g) (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
  (hnorm : ∀ x, plusNorm o x = 1)
  (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
  (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
  (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)

include hRic hminus hnorm w hstar hw hz

omit [PreconnectedSpace M] in
theorem actualJacobi_det_parallel_form (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    ((actualJacobiSolution g hRic e).J t).det = complexRadialDensity t := by
  let a := twoFormFrameValue o w.val e
  let v : Fin 3 → ℝ := ![a 0,a 1,a 2]
  have hv : dotProduct v v = 1 := unitSelfDual_frame_firstThree w hstar hw e he
  have hJ : (actualJacobiSolution g hRic e).J =
      complexJacobiPosition (Matrix.vecMulVec v v) :=
    (actualJacobi_parallel_form hRic hminus hnorm w hstar hw hz e he).1
  rw [hJ, complexJacobiPosition_det v hv]
  rfl

theorem parallel_form_cut_le_radius (e : FrameBundle g) (he : e ∈ o.positive) :
    actualCutTime g e ≤ complexJacobiRadius := by
  rw [← actualFirstConjugateTime_parallel_form hRic hminus hnorm w hstar hw hz e he]
  exact actualCutTime_le_firstConjugateTime g hRic e

theorem complex_actual_cut_mass (e : FrameBundle g) (he : e ∈ o.positive) :
    (∫⁻ r : Ioi (0 : ℝ),
      (if r.val ≤ actualCutTime g e then
        ENNReal.ofReal |((actualJacobiSolution g hRic e).J r.val).det| else 0)
      ∂((volume : Measure ℝ).comap Subtype.val)) = complexRadialMass (actualCutTime g e) := by
  let F : ℝ → ℝ≥0∞ := fun r => if r ≤ actualCutTime g e then
    ENNReal.ofReal |((actualJacobiSolution g hRic e).J r).det| else 0
  change (∫⁻ r : Ioi (0 : ℝ), F r.val
    ∂((volume : Measure ℝ).comap Subtype.val)) = _
  rw [lintegral_subtype_comap measurableSet_Ioi F,
    ← lintegral_indicator measurableSet_Ioi]
  rw [complexRadialMass, ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro r
  dsimp only [F]
  by_cases hr : 0 < r
  · rw [Set.indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr)]
    by_cases hc : r ≤ actualCutTime g e
    · rw [ite_eq_left hc,
        Set.indicator_of_mem (show r ∈ Ioc (0 : ℝ) (actualCutTime g e) from ⟨hr,hc⟩),
        actualJacobi_det_parallel_form hRic hminus hnorm w hstar hw hz e he r,
        abs_of_nonneg (complexRadialDensity_nonneg
          ⟨hr.le,hc.trans (parallel_form_cut_le_radius hRic hminus hnorm w hstar hw hz e he)⟩)]
    · rw [ite_eq_right hc, Set.indicator_of_notMem (fun h => hc h.2)]
  · rw [Set.indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from hr),
      Set.indicator_of_notMem (fun h => hr h.1)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full actual pullback metric in the parallel complex-curvature branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem heatNormalMetric_first_parallel_form (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t) :
    let a := twoFormFrameValue o w.val e
    let P := Matrix.vecMulVec ![a 0,a 1,a 2] ![a 0,a 1,a 2]
    heatNormalMetric g o e (t • coordinateVector 0) =
      jacobiBlockMatrix 1 ((t⁻¹ * t⁻¹) • complexJacobiGram P t) := by
  let f := parallelFrameFlowMap g 0 t e
  let c := f.base
  have hf : f.base ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace c
  have hx : frameExponential g o e (t • coordinateVector 0) = f.base :=
    frameExponential_first_ray g o e he t ht
  let E := frameChartMatrix g c f
  let H := metricInChart g c (chartAt FourSpace c f.base)
  let B := jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t)
  have hN : Eᵀ * H * E = 1 := frameChartMatrix_normalizes g c f hf
  have hD := (frameExponential_hasFDerivAt g o hRic c e he t ht hf).fderiv
  have hcol (i : Fin 4) :
      WithLp.ofLp (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (E * B)
        (coordinateVector i)) = fun k => (E * B) k i := by
    change (E * B) *ᵥ Pi.single i 1 = _
    exact Matrix.mulVec_single_one _ _
  have hGram : heatNormalMetric g o e (t • coordinateVector 0) = Bᵀ * B := by
    ext i j
    rw [heatNormalMetric_chart_pairing g o e c _ (hx ▸ hf), hD]
    rw [hcol, hcol]
    rw [hx, ← heat_matrix_congruence_pairing]
    change ((E * B)ᵀ * H * (E * B)) i j = (Bᵀ * B) i j
    have hmat : (E * B)ᵀ * H * (E * B) = Bᵀ * B := by
      rw [Matrix.transpose_mul]
      calc
        _ = Bᵀ * (Eᵀ * H * E) * B := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hN, Matrix.mul_one]
    exact congrArg (fun A : Mat4 => A i j) hmat
  rw [hGram, jacobiBlockMatrix_transpose_mul]
  simp only [one_pow]
  rw [(actualJacobi_parallel_form hRic hminus hnorm w hstar hw hz e he).1]
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 2
  apply complexJacobiPosition_transpose_mul
  · ext i j
    let v : Fin 3 → ℝ := ![(twoFormFrameValue o w.val e) 0,
      (twoFormFrameValue o w.val e) 1,(twoFormFrameValue o w.val e) 2]
    change v j * v i = v i * v j
    exact mul_comm _ _
  · rw [Matrix.vecMulVec_mul_vecMulVec,
      unitSelfDual_frame_firstThree w hstar hw e he, one_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual inverse of the complex normal exponential is C1 before the first conjugate radius. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_mfderiv_isUnit (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : v ≠ 0) (hR : ‖v‖ < complexJacobiRadius) :
    IsUnit (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o e) v) := by
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  let Q := directionOrientedMatrix q
  let L := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property).toContinuousLinearEquiv
  let f := e.rotate (orientedToOrthogonal Q)
  let x := ‖v‖ • coordinateVector 0
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  have hpoint : L x = v := by
    change L (‖v‖ • coordinateVector 0) = v
    rw [map_smul]
    exact (congrArg (fun z => ‖v‖ • z) (directionRotation_first q)).trans hrad
  let d := (parallelFrameFlowMap g 0 ‖v‖ f).base
  have hd : d ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hexp : frameExponential g o f x = d :=
    frameExponential_first_ray g o f hf ‖v‖ (norm_pos_iff.mpr hv)
  have hunit : IsUnit (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o f) x) := by
    rw [← frameExponential_center_fderiv, hexp,
      (frameExponential_hasFDerivAt g o hRic d f hf ‖v‖ (norm_pos_iff.mpr hv) hd).fderiv]
    apply frameExponential_preconjugate_isUnit g hRic d f ‖v‖ (norm_pos_iff.mpr hv)
    · rw [actualFirstConjugateTime_parallel_form hRic hminus hnorm W hstar hw hz f hf]
      exact hR
    · exact hd
  have hD : (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o e) v) =
      (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o f) x) *
        (L.symm : FourSpace →L[ℝ] FourSpace) := by
    apply ContinuousLinearMap.ext
    intro w
    have h := frameExponential_rotate_mfderiv g o e Q x (L.symm w)
    change _ = mfderiv I4 I4 (frameExponential g o e) (L x) (L (L.symm w)) at h
    rw [hpoint, L.apply_symm_apply] at h
    exact h.symm
  rw [hD]
  exact hunit.mul L.symm.toUnit.isUnit

theorem frameExponential_complex_inverse_contMDiffAt (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : v ≠ 0) (hR : ‖v‖ < complexJacobiRadius)
    (C : OpenPartialHomeomorph FourSpace M) (hCv : v ∈ C.source)
    (hC : EqOn C (frameExponential g o e) C.source) :
    ContMDiffAt I4 I4 1 C.symm (frameExponential g o e v) := by
  apply frameExponential_local_inverse_contMDiffAt g o e v C hCv hC
  rw [frameExponential_center_fderiv]
  exact frameExponential_complex_mfderiv_isUnit hRic hminus hnorm W hstar hw hz e he v hv hR

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exponential kernel in the complex-circle direction at an
arbitrary initial unit vector. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_angular_kernel (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (q : Directions) (c : M)
    (hc : frameExponential g o e (complexJacobiRadius • q.val) ∈ (chartAt FourSpace c).source) :
    fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z))
      (complexJacobiRadius • q.val)
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (twoFormMatrix (twoFormFrameValue o w.val e)) q.val) = 0 := by
  let Q := directionOrientedMatrix q
  let L := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property).toContinuousLinearEquiv
  let f := e.rotate (orientedToOrthogonal Q)
  let F := fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z)
  let G := fun z : FourSpace => chartAt FourSpace c (frameExponential g o f z)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hLfirst : L (coordinateVector 0) = q.val := directionRotation_first q
  have hLpoint : L (complexJacobiRadius • coordinateVector 0) = complexJacobiRadius • q.val := by
    rw [map_smul, hLfirst]
  have hp : frameExponential g o e (complexJacobiRadius • q.val) =
      (parallelFrameFlowMap g 0 complexJacobiRadius f).base :=
    frameExponential_direction_ray g o e he q complexJacobiRadius
  have hfc : (parallelFrameFlowMap g 0 complexJacobiRadius f).base ∈ (chartAt FourSpace c).source := hp ▸ hc
  have hF := (frameExponential_chart_contDiffAt g o c e (complexJacobiRadius • q.val) hc).differentiableAt
    one_ne_zero
  rw [← hLpoint] at hF
  have hcomp := hF.hasFDerivAt.comp (complexJacobiRadius • coordinateVector 0)
    (L : FourSpace →L[ℝ] FourSpace).hasFDerivAt
  have heq : (fun z : FourSpace => F (L z)) = G := by
    funext z
    exact congrArg (chartAt FourSpace c) (frameExponential_rotate g o e Q z).symm
  change HasFDerivAt (fun z => F (L z))
    ((fderiv ℝ F (L (complexJacobiRadius • coordinateVector 0))).comp
      (L : FourSpace →L[ℝ] FourSpace)) (complexJacobiRadius • coordinateVector 0) at hcomp
  rw [heq, hLpoint] at hcomp
  have hvel : L (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      (twoFormMatrix (twoFormFrameValue o w.val f)) (coordinateVector 0)) =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (twoFormMatrix (twoFormFrameValue o w.val e)) q.val := by
    have h := twoForm_operator_rotate (o := o) w.val e (orientedToOrthogonal Q) (coordinateVector 0)
    change L (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
      (twoFormMatrix (twoFormFrameValue o w.val f)) (coordinateVector 0)) =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (twoFormMatrix (twoFormFrameValue o w.val e)) (L (coordinateVector 0)) at h
    rwa [hLfirst] at h
  have hk := frameExponential_complex_first_kernel hRic hminus hnorm w hstar hw hz f hf c hfc
  change fderiv ℝ G (complexJacobiRadius • coordinateVector 0) _ = 0 at hk
  rw [hcomp.fderiv] at hk
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hvel] using hk

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential identifies each complex circle at the boundary
of the minimizing ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_boundary_circle (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (q : Directions) (t : ℝ) :
    frameExponential g o e (complexJacobiRadius • complexCircleVector
      (twoFormMatrix (twoFormFrameValue o w.val e)) q.val t) =
        frameExponential g o e (complexJacobiRadius • q.val) := by
  let J := twoFormMatrix (twoFormFrameValue o w.val e)
  have hs : J * J = -(1 : Mat4) := (unit_selfDual_frame_complex w hstar hw e he).1
  have hsk : Jᵀ = -J := twoFormMatrix_skew _
  let F := fun s : ℝ => frameExponential g o e (complexJacobiRadius • complexCircleVector J q.val s)
  have hcircle : Continuous (complexCircleVector J q.val) :=
    continuous_iff_continuousAt.mpr (fun s => (complexCircleVector_hasDerivAt J hs q.val s).continuousAt)
  have hF : Continuous F := (frameExponential_continuous g o e).comp
    (hcircle.const_smul complexJacobiRadius)
  have hD (s : ℝ) (c : M) (hc : F s ∈ (chartAt FourSpace c).source) :
      HasDerivAt (fun r => chartAt FourSpace c (F r)) (0 : FourSpace) s := by
    let p : Directions := ⟨complexCircleVector J q.val s,
      (complexCircleVector_norm J hsk hs q.val s).trans q.property⟩
    have hd := (complexCircleVector_hasDerivAt J hs q.val s).const_smul complexJacobiRadius
    have hE := (frameExponential_chart_contDiffAt g o c e
      (complexJacobiRadius • p.val) hc).differentiableAt one_ne_zero
    have h := hE.hasFDerivAt.comp_hasDerivAt s hd
    change HasDerivAt (fun r => chartAt FourSpace c (F r))
      (fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z))
        (complexJacobiRadius • p.val)
        (complexJacobiRadius • Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) J p.val)) s at h
    rw [map_smul, frameExponential_complex_angular_kernel hRic hminus hnorm w hstar hw hz e he p c hc,
      smul_zero] at h
    exact h
  have h := zero_chart_curve_constant F hF hD t 0
  simpa only [F, complexCircleVector_zero] using h

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

/-! The three exact metric factors in a standard complex normal frame. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped Manifold ContDiff BigOperators
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem heatNormalMetric_first_standard (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (t : ℝ) (ht : 0 < t) :
    heatNormalMetric g o e (t • coordinateVector 0) = Matrix.diagonal
      ![1,(complexJacobiFast t / t)^2,(complexJacobiSlow t / t)^2,(complexJacobiSlow t / t)^2] := by
  rw [heatNormalMetric_first_parallel_form hRic hminus hnorm w hstar hw hz e he t ht,hstd]
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · simp [jacobiBlockMatrix,Matrix.diagonal,Ne.symm (Fin.succ_ne_zero j)]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [jacobiBlockMatrix,Matrix.diagonal]
    · simp only [jacobiBlockMatrix,Fin.cons_succ]
      fin_cases i <;> fin_cases j <;>
        simp [complexJacobiGram,standardSelfDualForm,Matrix.vecMulVec_apply,
          Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.diagonal,div_pow]
      all_goals ring

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_first_pairing (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (t : ℝ) (ht : 0 < t) (u v : FourSpace) :
    g.inner (frameExponential g o e (t • coordinateVector 0))
      (mfderiv I4 I4 (frameExponential g o e) (t • coordinateVector 0) u)
      (mfderiv I4 I4 (frameExponential g o e) (t • coordinateVector 0) v) =
        (complexJacobiSlow t / t)^2 * inner ℝ u v +
          (1-(complexJacobiSlow t / t)^2)*u 0*v 0 +
          ((complexJacobiFast t / t)^2-(complexJacobiSlow t / t)^2)*u 1*v 1 := by
  have hp := heatNormalMetric_pairing g o e (t • coordinateVector 0)
    (WithLp.ofLp u) (WithLp.ofLp v)
  simp only [WithLp.toLp_ofLp] at hp
  rw [← hp,heatNormalMetric_first_standard hRic hminus hnorm w hstar hw hz e he hstd t ht]
  exact complex_diagonal_pairing _ _ u v

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_pairing (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (q : Directions) (t : ℝ) (ht : 0 < t) (w z : FourSpace) :
    g.inner (frameExponential g o e (t • q.val))
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) w)
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) z) =
        (complexJacobiSlow t / t)^2 * inner ℝ w z +
          (1-(complexJacobiSlow t / t)^2)*inner ℝ q.val w * inner ℝ q.val z +
          ((complexJacobiFast t / t)^2-(complexJacobiSlow t / t)^2)*
            inner ℝ (complexCompanion q) w * inner ℝ (complexCompanion q) z := by
  let Q := directionOrientedMatrix q
  let L := orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property
  let f := e.rotate (orientedToOrthogonal Q)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hfirst : L (coordinateVector 0) = q.val := directionRotation_first q
  have hpoint : L (t • coordinateVector 0) = t • q.val := by rw [map_smul, hfirst]
  have hbase : frameExponential g o f (t • coordinateVector 0) =
      frameExponential g o e (t • q.val) := by
    rw [frameExponential_rotate]
    exact congrArg (frameExponential g o e) hpoint
  have hD (u : FourSpace) :
      mfderiv I4 I4 (frameExponential g o f) (t • coordinateVector 0) u =
        mfderiv I4 I4 (frameExponential g o e) (t • q.val) (L u) := by
    have h := frameExponential_rotate_mfderiv g o e Q (t • coordinateVector 0) u
    change _ = mfderiv I4 I4 (frameExponential g o e) (L (t • coordinateVector 0)) (L u) at h
    rwa [hpoint] at h
  have hzero (u : FourSpace) : (L.symm u) 0 = inner ℝ q.val u := by
    have h := L.inner_map_map (coordinateVector 0) (L.symm u)
    rw [hfirst, L.apply_symm_apply] at h
    simpa [PiLp.inner_apply, coordinateVector] using h.symm
  have hsecond : L (coordinateVector 1) = complexCompanion q := by
    change WithLp.toLp 2 ((directionFrameMatrix q) *ᵥ Pi.single 1 1) = _
    rw [Matrix.mulVec_single_one]
    ext i
    fin_cases i <;> rfl
  have hone (u : FourSpace) : (L.symm u) 1 = inner ℝ (complexCompanion q) u := by
    have h := L.inner_map_map (coordinateVector 1) (L.symm u)
    rw [hsecond,L.apply_symm_apply] at h
    simpa [PiLp.inner_apply,coordinateVector] using h.symm
  have hinner : inner ℝ (L.symm w) (L.symm z) = inner ℝ w z := by
    simpa only [L.apply_symm_apply] using
      (L.inner_map_map (L.symm w) (L.symm z)).symm
  have hfstd : twoFormFrameValue o W.val f = standardSelfDualForm :=
    twoFormFrameValue_direction_standard W.val e hstd q
  have h := frameExponential_complex_first_pairing hRic hminus hnorm W hstar hw hz
    f hf hfstd t ht (L.symm w) (L.symm z)
  let B₁ : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ :=
    g.inner (frameExponential g o f (t • coordinateVector 0))
  let B₂ : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ :=
    g.inner (frameExponential g o e (t • q.val))
  let D₁ : FourSpace →L[ℝ] FourSpace :=
    mfderiv I4 I4 (frameExponential g o f) (t • coordinateVector 0)
  let D₂ : FourSpace →L[ℝ] FourSpace :=
    mfderiv I4 I4 (frameExponential g o e) (t • q.val)
  have hB : B₁ = B₂ := by
    dsimp only [B₁, B₂]
    rw [hbase]
  have hD' (u : FourSpace) : D₁ u = D₂ (L u) := hD u
  change B₁ (D₁ (L.symm w)) (D₁ (L.symm z)) = _ at h
  change B₂ (D₂ w) (D₂ z) = _
  rw [hB, hD', hD', L.apply_symm_apply, L.apply_symm_apply, hinner,
    hzero, hzero, hone, hone] at h
  exact h

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_eq_of_projective_polar_eq (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) complexJacobiRadius)
    (hs : s ∈ Icc (0 : ℝ) complexJacobiRadius) (q p : Directions)
    (heq : complexProjectivePolar t q = complexProjectivePolar s p) :
    frameExponential g o e (t • q.val) = frameExponential g o e (s • p.val) := by
  have hts := complexProjectivePolar_radius_eq ht hs q p heq
  subst s
  by_cases h0 : t = 0
  · simp [h0]
  by_cases hR : t = complexJacobiRadius
  · subst t
    obtain ⟨r,hr⟩ := complexProjectivePolar_boundary_circle q p heq
    rw [hr]
    symm
    simpa only [hstd] using frameExponential_complex_boundary_circle
      hRic hminus hnorm w hstar hw hz e he q r
  · have hqp := complexProjectivePolar_interior_injective
      ⟨lt_of_le_of_ne ht.1 (Ne.symm h0),lt_of_le_of_ne ht.2 hR⟩ q p heq
    rw [hqp]

theorem actualComplexProjectiveMap_polar (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) complexJacobiRadius) (q : Directions) :
    actualComplexProjectiveMap g o e (complexProjectivePolar t q) =
      frameExponential g o e (t • q.val) := by
  let D := complexProjectivePolarData (complexProjectivePolar t q)
  exact frameExponential_eq_of_projective_polar_eq hRic hminus hnorm w hstar hw hz
    e he hstd D.time_mem ht D.direction q D.point_eq

end
end PositiveEinsteinFour.Geometry
end


section

/-! Equality between the genuine metric and the horizontal homogeneous metric. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
open scoped Manifold ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_metric_eq_horizontal (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (q : Directions) (t : ℝ) (ht : 0 < t) (v : FourSpace) :
    g.inner (frameExponential g o e (t • q.val))
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) v)
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) v) =
        2 * (‖complexPolarLiftDifferential t q v‖^2 -
          ‖inner ℂ (complexPolarLift t q) (complexPolarLiftDifferential t q v)‖^2) := by
  rw [frameExponential_complex_pairing hRic hminus hnorm W hstar hw hz e he hstd q t ht,
    complex_projective_differential_gram,real_inner_self_eq_norm_sq]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The speed of the actual exponential curve in homogeneous coordinates. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
open scoped Manifold ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_complex_curve_speed (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    {c : ℝ → FourSpace} {s t : ℝ} (hc : DifferentiableAt ℝ c s)
    (ht : 0 < t) (q : Directions) (hcs : c s = t • q.val) :
    Real.sqrt 2 * Real.sqrt (‖deriv (fun r => complexNormalLift (c r)) s‖^2 -
      ‖inner ℂ (complexNormalLift (c s)) (deriv (fun r => complexNormalLift (c r)) s)‖^2) =
        metricTangentNorm g (frameExponential g o e (c s))
          (mfderiv 𝓘(ℝ, ℝ) I4 (fun r => frameExponential g o e (c r)) s 1) := by
  have hlift := complexNormalLift_hasDerivAt hc.hasDerivAt ht q hcs
  have hm := mfderiv_comp s
    ((frameExponential_contMDiff g o e).mdifferentiable one_ne_zero (c s)) hc.mdifferentiableAt
  have hDc : mfderiv 𝓘(ℝ, ℝ) I4 c s 1 = deriv c s := by
    simpa only [mfderiv_eq_fderiv] using! (fderiv_apply_one_eq_deriv (f := c) (x := s))
  have hD : mfderiv 𝓘(ℝ, ℝ) I4 (fun r => frameExponential g o e (c r)) s 1 =
      mfderiv I4 I4 (frameExponential g o e) (c s) (deriv c s) := by
    have h := congrArg (fun D : ℝ →L[ℝ] FourSpace => D 1) hm
    exact h.trans (congrArg (mfderiv I4 I4 (frameExponential g o e) (c s)) hDc)
  rw [hD,metricTangentNorm_eq_sqrt,hlift.deriv]
  let v : FourSpace := deriv c s
  change Real.sqrt 2 * Real.sqrt (‖complexPolarLiftDifferential t q v‖^2 -
    ‖inner ℂ (complexNormalLift (c s)) (complexPolarLiftDifferential t q v)‖^2) =
    Real.sqrt (g.inner (frameExponential g o e (c s))
      (mfderiv I4 I4 (frameExponential g o e) (c s) v)
      (mfderiv I4 I4 (frameExponential g o e) (c s) v))
  rw [hcs,complexNormalLift_radial t ht q,
    frameExponential_complex_metric_eq_horizontal hRic hminus hnorm W hstar hw hz e he hstd q t ht,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


