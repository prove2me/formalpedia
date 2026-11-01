-- Prove2me | Definitions.Def_OAIQ091C034
-- name    : OAIQ091C034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T19:41:09.154648+00:00
-- url     : https://prove2.me/theorems/76940509-8180-4602-8d1f-da16cd85ab15
-- title:
--   Definitions bundle OAIQ091C034 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 44 declarations of OpenAI's Lean: 2 definitions and 42 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.actualComplexHomeomorph`, `OAI.PositiveEinsteinFour.Geometry.actualRoundHomeomorph`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry06.lean), [`EinsteinFour_GeodesicGeometry11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry11.lean), [`EinsteinFour_GeodesicGeometry12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry12.lean), [`EinsteinFour_GeodesicGeometry13`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry13.lean), [`EinsteinFour_GeodesicGeometry14`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry14.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C032` and `OAIQ091C033` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C052`, `OAIQ091C053` and `OAIQ091C059`; the proofs of `OAI.PositiveEinsteinFour.Geometry.actual_derdzinski_hitchin`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C032
import Definitions.Def_OAIQ091C033

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual polar volume bound at a fixed positive orthonormal frame.
The minimizing radial cutoff is bounded by the first conjugate time, and
the metric volume normalization is bounded by its sharp Euclidean value. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem volumeMeasure_le_sphericalJacobi_lintegral (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    volumeMeasure g univ ≤ ENNReal.ofReal (2 * Real.pi ^ 2) *
      ∫⁻ q : Directions, ∫⁻ r in Icc (0 : ℝ) Real.pi,
        ENNReal.ofReal (actualRegularJacobi g hRic
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) r).truncatedDensity
        ∂volume ∂sphereMeasure := by
  have h := volumeMeasure_le_integral_exponentialJacobian g o hRic e he
  rw [minimizing_exponential_integral_radial g o hRic e he] at h
  calc
    volumeMeasure g univ ≤ riemannianChartFactor *
        (polarAngularMass * ∫⁻ q : Directions, ∫⁻ r : Ioi (0 : ℝ),
          (if r.val ≤ actualCutTime g
              (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) then
            ENNReal.ofReal |((actualJacobiSolution g hRic
              (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det|
            else 0) ∂((volume : Measure ℝ).comap Subtype.val) ∂sphereMeasure) := h
    _ ≤ 1 * (polarAngularMass * ∫⁻ q : Directions, ∫⁻ r : Ioi (0 : ℝ),
          (if r.val ≤ actualCutTime g
              (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) then
            ENNReal.ofReal |((actualJacobiSolution g hRic
              (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det|
            else 0) ∂((volume : Measure ℝ).comap Subtype.val) ∂sphereMeasure) := by
      gcongr
      exact riemannianChartFactor_le_one
    _ ≤ ENNReal.ofReal (2 * Real.pi ^ 2) *
        ∫⁻ q : Directions, ∫⁻ r in Icc (0 : ℝ) Real.pi,
          ENNReal.ofReal (actualRegularJacobi g hRic
            (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) r).truncatedDensity
          ∂volume ∂sphereMeasure := by
      rw [one_mul, polarAngularMass_eq]
      gcongr
      exact actualJacobi_cutoff_lintegral_le g hRic _ _
        (actualCutTime_le_firstConjugateTime g hRic _)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
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

variable [SecondCountableTopology M] [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instIsProbabilityMeasureDirectionsSphereMeasure_5
theorem volumeMeasure_le_canonicalRadialMass (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    volumeMeasure g univ ≤ ENNReal.ofReal (2 * Real.pi ^ 2) *
      ∫⁻ e, actualRadialMass g hRic e ∂canonicalFrameMeasure g o := by
  have h := lintegral_mono_ae ((canonicalFrameMeasure_supported g o).mono
    (fun e he => volumeMeasure_le_sphericalJacobi_lintegral g o hRic e he))
  change (∫⁻ _e, volumeMeasure g univ ∂canonicalFrameMeasure g o) ≤
    ∫⁻ e, ENNReal.ofReal (2 * Real.pi ^ 2) *
      (∫⁻ q : Directions,
        actualRadialMass g hRic (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))
        ∂sphereMeasure) ∂canonicalFrameMeasure g o at h
  simpa only [lintegral_const, measure_univ, mul_one,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    canonicalFrame_lintegral_sphere_rotations g o _ (measurable_actualRadialMass g hRic)] using h

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

variable [SecondCountableTopology M] [PreconnectedSpace M]

theorem totalVolume_le_actualJacobiIntegral (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    totalVolume g ≤ (2 * Real.pi ^ 2) *
      ∫ r in (0 : ℝ)..Real.pi,
        ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
          ∂canonicalFrameMeasure g o := by
  have h := volumeMeasure_le_canonicalRadialMass g o hRic
  rw [canonical_actualRadialMass_eq, ← ENNReal.ofReal_mul (by positivity)] at h
  have hn : 0 ≤ (2 * Real.pi ^ 2) *
      ∫ r in Icc (0 : ℝ) Real.pi, ∫ e,
        (actualRegularJacobi g hRic e r).truncatedDensity ∂canonicalFrameMeasure g o := by
    apply mul_nonneg (by positivity)
    apply setIntegral_nonneg measurableSet_Icc
    intro r hr
    exact actualJacobi_average_nonneg g o hRic r hr.1
  have hreal := ENNReal.toReal_le_of_le_ofReal hn h
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
    at hreal
  exact hreal

theorem actualJacobiPolarInput_proved (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) : ActualJacobiPolarInput g o hRic := by
  let F : ℝ → ℝ := fun r => ∫ e,
    (actualRegularJacobi g hRic e r).truncatedDensity ∂canonicalFrameMeasure g o
  have hvolume : totalVolume g ≤ (2 * Real.pi ^ 2) * ∫ r in (0 : ℝ)..Real.pi, F r :=
    totalVolume_le_actualJacobiIntegral g o hRic
  have hscale : (∫ r in (0 : ℝ)..Real.pi, F r) =
      Real.pi * ∫ u in (0 : ℝ)..1, F (Real.pi * u) := by
    have h := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1) F Real.pi
    simpa only [smul_eq_mul, mul_zero, mul_one] using h.symm
  rw [hscale] at hvolume
  have hsplit : (∫ u in (0 : ℝ)..1, F (Real.pi * u)) =
      (∫ u in (0 : ℝ)..(5 / 8), F (Real.pi * u)) +
        ∫ u in (5 / 8 : ℝ)..1, F (Real.pi * u) := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (actualJacobiDensity_intervalIntegrable g o hRic 0 (5 / 8) (by norm_num))
      (actualJacobiDensity_intervalIntegrable g o hRic (5 / 8) 1 (by norm_num))
  rw [hsplit] at hvolume
  change totalVolume g / (8 * Real.pi ^ 2 / 3) ≤ _
  apply (div_le_iff₀ (by positivity : 0 < 8 * Real.pi ^ 2 / 3)).mpr
  convert hvolume using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [F]
  ring

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry11
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Retain the actual chart-volume factor throughout polar integration.
It is the same positive factor as in the Euler and signature integrals. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

omit [Nonempty M] in
theorem volumeMeasure_le_normalized_sphericalJacobi (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    volumeMeasure g univ ≤ riemannianChartFactor *
      (ENNReal.ofReal (2 * Real.pi ^ 2) * ∫⁻ q : Directions,
        actualRadialMass g hRic
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) ∂sphereMeasure) := by
  have h := volumeMeasure_le_integral_exponentialJacobian g o hRic e he
  rw [minimizing_exponential_integral_radial g o hRic e he, polarAngularMass_eq] at h
  refine h.trans ?_
  gcongr
  exact actualJacobi_cutoff_lintegral_le g hRic _ _
    (actualCutTime_le_firstConjugateTime g hRic _)

theorem volumeMeasure_le_normalized_canonicalRadialMass (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    volumeMeasure g univ ≤ riemannianChartFactor *
      (ENNReal.ofReal (2 * Real.pi ^ 2) *
        ∫⁻ e, actualRadialMass g hRic e ∂canonicalFrameMeasure g o) := by
  have h := lintegral_mono_ae ((canonicalFrameMeasure_supported g o).mono
    (fun e he => volumeMeasure_le_normalized_sphericalJacobi g o hRic e he))
  have hk : riemannianChartFactor ≠ ⊤ := by
    unfold riemannianChartFactor
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  simpa only [lintegral_const, measure_univ, mul_one,
    lintegral_const_mul' _ _ hk,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    canonicalFrame_lintegral_sphere_rotations g o _ (measurable_actualRadialMass g hRic)] using h

theorem normalized_totalVolume_le_actualJacobiIntegral (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    totalVolume g / riemannianChartFactor.toReal ≤ (2 * Real.pi ^ 2) *
      ∫ r in (0 : ℝ)..Real.pi,
        ∫ e, (actualRegularJacobi g hRic e r).truncatedDensity
          ∂canonicalFrameMeasure g o := by
  have h := volumeMeasure_le_normalized_canonicalRadialMass g o hRic
  rw [canonical_actualRadialMass_eq, ← ENNReal.ofReal_mul (by positivity)] at h
  have hk : riemannianChartFactor ≠ ⊤ := by
    unfold riemannianChartFactor
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hk ENNReal.ofReal_ne_top) h
  have hn : 0 ≤ (2 * Real.pi ^ 2) *
      ∫ r in Icc (0 : ℝ) Real.pi, ∫ e,
        (actualRegularJacobi g hRic e r).truncatedDensity ∂canonicalFrameMeasure g o := by
    apply mul_nonneg (by positivity)
    apply setIntegral_nonneg measurableSet_Icc
    intro r hr
    exact actualJacobi_average_nonneg g o hRic r hr.1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hn,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le] at hreal
  exact (div_le_iff₀ riemannianChartFactor_toReal_pos).mpr (by
    simpa only [totalVolume, mul_comm] using hreal)

theorem normalized_actualJacobiPolar (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) :
    volumeRatio g / riemannianChartFactor.toReal ≤ (3 * Real.pi / 4) *
      ((∫ u in (0 : ℝ)..(5 / 8), ∫ e,
          (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity
            ∂canonicalFrameMeasure g o) +
        ∫ u in (5 / 8 : ℝ)..1, ∫ e,
          (actualRegularJacobi g hRic e (Real.pi * u)).truncatedDensity
            ∂canonicalFrameMeasure g o) := by
  let F : ℝ → ℝ := fun r => ∫ e,
    (actualRegularJacobi g hRic e r).truncatedDensity ∂canonicalFrameMeasure g o
  have hvolume := normalized_totalVolume_le_actualJacobiIntegral g o hRic
  change totalVolume g / riemannianChartFactor.toReal ≤
    (2 * Real.pi ^ 2) * ∫ r in (0 : ℝ)..Real.pi, F r at hvolume
  have hscale : (∫ r in (0 : ℝ)..Real.pi, F r) =
      Real.pi * ∫ u in (0 : ℝ)..1, F (Real.pi * u) := by
    have h := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1) F Real.pi
    simpa only [smul_eq_mul, mul_zero, mul_one] using h.symm
  rw [hscale] at hvolume
  have hsplit : (∫ u in (0 : ℝ)..1, F (Real.pi * u)) =
      (∫ u in (0 : ℝ)..(5 / 8), F (Real.pi * u)) +
        ∫ u in (5 / 8 : ℝ)..1, F (Real.pi * u) := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals
      (actualJacobiDensity_intervalIntegrable g o hRic 0 (5 / 8) (by norm_num))
      (actualJacobiDensity_intervalIntegrable g o hRic (5 / 8) 1 (by norm_num))
  rw [hsplit] at hvolume
  unfold volumeRatio
  rw [div_right_comm]
  apply (div_le_iff₀ (by positivity : 0 < 8 * Real.pi ^ 2 / 3)).mpr
  convert hvolume using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [F]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual curvature-energy volume deficit in the normalization used
by the proved Euler and signature integrals. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix MeasureTheory Angular
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.normalizedGeometricVolumeNorm
local instance normalizedGeometricVolumeSpace_r98c9a2_1 : NormedSpace ℝ Mat3 :=
  Matrix.frobeniusNormedSpace
theorem normalized_volume_ratio_upper (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g) :
    volumeRatio g / riemannianChartFactor.toReal ≤ 1 - (3 / 40) *
      (∫ c, plusNorm o c ^ 2 + minusNorm o c ^ 2 ∂normalizedVolume g) := by
  let d := (canonicalParallelMetricData g o hRic).toMetricGreenData
  have hp : ParallelReflection d := actualParallelMetricData_reflection g
    (canonicalFrameMeasure g o) (parallelFrameFlowMap_measurePreserving g o) hRic
  let op := d.oppositeData hp hRic
  let j := (actualJacobiRealizationData g o hRic
    (actualJacobiPolarInput_proved g o hRic)).toParallelJacobiData op hRic
  let w := canonicalFrameMeasure_energy g o
  let : CompactSpace (FrameBundle g) := j.compact
  have hnorm := (actual_orientedNormRegularity o).toPetersenInput
  have hvol := actual_finitePositiveVolume g
  have hCi := (j.curvatureContinuous.norm.pow 2).integrable_of_hasCompactSupport
    (μ := canonicalFrameMeasure g o) (HasCompactSupport.of_compactSpace _)
  have hDi := (j.derivativeContinuous.norm.pow 2).integrable_of_hasCompactSupport
    (μ := canonicalFrameMeasure g o) (HasCompactSupport.of_compactSpace _)
  apply normalized_volume_ratio_upper_of_frame_flow g j.flow j.curvatureContinuous
    j.derivativeContinuous j.derivative
    (w.curvature_energy actual_follandMoments hRic hnorm hvol hCi)
    (w.derivative_energy d op hp actual_follandMoments hRic hpositive hnorm hvol hDi)
    j.jacobi j.curvature
  · intro u e r
    rw [j.curvature]
    exact actual_jacobi_posSemidef hpositive _
  · intro u e r
    rw [j.curvature]
    exact frameCurvatureField_add_one_trace g _ (actual_einstein_decomposition _ hRic)
      (actual_weyl_traceFree _ hRic).1 (actual_weyl_traceFree _ hRic).2
  · exact j.densityIntegrable
  · exact j.firstIntegral
  · exact j.secondIntegral
  · exact normalized_actualJacobiPolar g o hRic

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual harmonic dimensions give both integer identities with the
common chart-volume factor divided out. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]

theorem normalized_hodge_counts (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) :
    ∃ n m : ℕ,
      2 + (n : ℝ) + (m : ℝ) = 2 * (volumeRatio g / riemannianChartFactor.toReal) *
        (1 + (∫ c, plusNorm o c ^ 2 ∂normalizedVolume g) +
          ∫ c, minusNorm o c ^ 2 ∂normalizedVolume g) ∧
      (n : ℝ) - (m : ℝ) = (4 / 3 : ℝ) *
        (volumeRatio g / riemannianChartFactor.toReal) *
        ((∫ c, plusNorm o c ^ 2 ∂normalizedVolume g) -
          ∫ c, minusNorm o c ^ 2 ∂normalizedVolume g) := by
  have he := hodgeComplexEuler_curvature_counts hRic (canonicalParallelMetricData g o hRic)
  have hs := deRhamSignature_curvature_counts (o := o) hRic
  rw [hodgeComplexEuler_hodge hRic] at he
  rw [deRhamSignature_hodge hRic] at hs
  push_cast at he hs
  refine ⟨Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic),
    Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic), ?_, ?_⟩
  · field_simp [riemannianChartFactor_toReal_pos.ne']
    nlinarith only [he]
  · field_simp [riemannianChartFactor_toReal_pos.ne']
    nlinarith only [hs]

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

/-! The actual index identities force equality in the normalized volume
bound when both Weyl blocks vanish. The common chart factor is retained. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem round_normalized_volume_eq_one (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0) :
    volumeRatio g / riemannianChartFactor.toReal = 1 := by
  have hp : ∀ c, plusNorm o c = 0 := fun c => (plusNorm_eq_zero_iff o c).mpr (hplus c)
  have hm : ∀ c, minusNorm o c = 0 := fun c => (minusNorm_eq_zero_iff o c).mpr (hminus c)
  have hu := normalized_volume_ratio_upper g o hRic hpositive
  obtain ⟨n, m, hc, _⟩ := normalized_hodge_counts g o hRic
  simp only [hp, hm, zero_pow (by decide : 2 ≠ 0), add_zero, integral_zero,
    mul_zero, sub_zero, mul_one] at hu hc
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem round_normalized_totalVolume (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0) :
    totalVolume g / riemannianChartFactor.toReal = 8 * Real.pi ^ 2 / 3 := by
  have h := round_normalized_volume_eq_one hRic hpositive hplus hminus
  unfold volumeRatio at h
  rw [div_right_comm] at h
  exact (div_eq_one_iff_eq (by positivity : (8 * Real.pi ^ 2 / 3 : ℝ) ≠ 0)).mp h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual minimizing-domain integral retains the cut radius exactly
in the constant-curvature branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable [SecondCountableTopology M]

theorem round_volume_le_cut_mass (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    volumeMeasure g univ ≤ riemannianChartFactor *
      (ENNReal.ofReal (2 * Real.pi ^ 2) * ∫⁻ q : Directions,
        roundRadialMass (actualCutTime g
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))) ∂sphereMeasure) := by
  have h := volumeMeasure_le_integral_exponentialJacobian g o hRic e he
  rw [minimizing_exponential_integral_radial g o hRic e he, polarAngularMass_eq] at h
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply lintegral_congr
  intro q
  exact (round_actual_cut_mass hRic hplus hminus _
    (frameRotate_oriented_positive o e he (directionOrientedMatrix q))).symm

theorem round_volumeMeasure (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0) :
    volumeMeasure g univ = riemannianChartFactor * ENNReal.ofReal (8 * Real.pi ^ 2 / 3) := by
  have h := (div_eq_iff riemannianChartFactor_toReal_pos.ne').mp
    (round_normalized_totalVolume hRic hpositive hplus hminus)
  have hk : riemannianChartFactor ≠ ⊤ := by
    unfold riemannianChartFactor
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  calc
    volumeMeasure g univ = ENNReal.ofReal (totalVolume g) :=
      (ENNReal.ofReal_toReal (ne_of_lt (actual_finitePositiveVolume g).finite)).symm
    _ = ENNReal.ofReal ((8 * Real.pi ^ 2 / 3) * riemannianChartFactor.toReal) := congrArg _ h
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hk, mul_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Equality in the actual polar volume formula rules out all early cut
points. Upper semicontinuity upgrades the almost-everywhere conclusion to
all directions, using the full support of the actual sphere measure. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem round_cut_time_all_directions (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (q : Directions) :
    actualCutTime g (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) = Real.pi := by
  let : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability
  let : Measure.IsOpenPosMeasure sphereMeasure := sphereMeasure_openPos
  let R := fun q : Directions => e.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  let F := fun q : Directions => roundRadialMass (actualCutTime g (R q))
  let K := roundRadialMass Real.pi
  have hK : K = ENNReal.ofReal (4 / 3 : ℝ) := roundRadialMass_pi
  have hKfin : K ≠ ⊤ := hK ▸ ENNReal.ofReal_ne_top
  have hle (q : Directions) : F q ≤ K :=
    roundRadialMass_le_pi _ (actualCutTime_le_pi g hRic _)
  have hupper : (∫⁻ q, F q ∂sphereMeasure) ≤ K := by
    calc
      _ ≤ ∫⁻ _q : Directions, K ∂sphereMeasure := lintegral_mono hle
      _ = K := by simp
  have hlower : K ≤ ∫⁻ q, F q ∂sphereMeasure := by
    have h := round_volume_le_cut_mass hRic hplus hminus e he
    rw [round_volumeMeasure hRic hpositive hplus hminus] at h
    have hfactor : ENNReal.ofReal (8 * Real.pi ^ 2 / 3) =
        ENNReal.ofReal (2 * Real.pi ^ 2) * K := by
      rw [hK, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    rw [hfactor] at h
    have hk := ENNReal.toReal_pos_iff.mp riemannianChartFactor_toReal_pos
    have hcancel := (ENNReal.mul_le_mul_iff_right hk.1.ne' hk.2.ne).mp h
    exact (ENNReal.mul_le_mul_iff_right (by positivity : ENNReal.ofReal (2 * Real.pi ^ 2) ≠ 0)
      ENNReal.ofReal_ne_top).mp hcancel
  have hInt : (∫⁻ q, F q ∂sphereMeasure) = K := le_antisymm hupper hlower
  have hae : F =ᵐ[sphereMeasure] (fun _ => K) := by
    exact ae_eq_of_ae_le_of_lintegral_le (Filter.Eventually.of_forall hle) (hInt ▸ hKfin)
      aemeasurable_const (by first | (simp [hInt]; done) | simpa using hInt.ge)
  have haec : ∀ᵐ q : Directions ∂sphereMeasure, Real.pi ≤ actualCutTime g (R q) := by
    filter_upwards [hae] with q hq
    by_contra hn
    have hr : R q ∈ o.positive := frameRotate_oriented_positive o e he (directionOrientedMatrix q)
    exact (roundRadialMass_lt_pi _ ⟨(actualCutTime_pos g o hRic (R q) hr).le,
      lt_of_not_ge hn⟩).ne hq
  have hR : Continuous R := (continuous_frameRotate g).comp
    (continuous_const.prodMk (continuous_orientedToOrthogonal.comp continuous_directionOrientedMatrix))
  have hclosed : IsClosed {q : Directions | Real.pi ≤ actualCutTime g (R q)} :=
    ((actualCutTime_upperSemicontinuous g).isClosed_preimage Real.pi).preimage hR
  have hdense := Measure.dense_of_ae haec
  have hall : {q : Directions | Real.pi ≤ actualCutTime g (R q)} = univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  apply le_antisymm (actualCutTime_le_pi g hRic _)
  have hq : q ∈ {q : Directions | Real.pi ≤ actualCutTime g (R q)} := by rw [hall]; exact mem_univ q
  exact hq

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every radial segment through length pi is minimizing in the round
branch. The conclusion follows from the actual cut-time equality. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_round_minimizing (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hv : ‖v‖ ≤ Real.pi) :
    metricDistance g e.base (frameExponential g o e v) = ‖v‖ := by
  by_cases hz : v = 0
  · subst v
    rw [frameExponential_zero, norm_zero]
    exact (metricDistance_eq_zero_iff g _ _).mpr rfl
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hm : ‖v‖ • q.val ∈ actualMinimizingTangentDomain g o e := by
    apply (actualMinimizingTangentDomain_ray_iff g o e he q ‖v‖ (norm_nonneg _)).mpr
    rw [round_cut_time_all_directions hRic hpositive hplus hminus e he q]
    exact hv
  rwa [hrad] at hm

theorem roundSphereMap_radial_distance (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (p : RoundSphere4) :
    metricDistance g e.base (roundSphereMap g o e p) = Real.arccos (p.val 0) := by
  change metricDistance g e.base (frameExponential g o e (roundLog p)) = _
  rw [frameExponential_round_minimizing hRic hpositive hplus hminus e he _
    (by rw [roundLog_norm]; exact Real.arccos_le_pi _), roundLog_norm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Once every geodesic minimizes up to pi, the no-corner lemma rules out
multiple radial directions meeting before pi. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem round_direction_injective (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (q p : Directions)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) Real.pi)
    (hqp : frameExponential g o e (t • q.val) = frameExponential g o e (t • p.val)) : q = p := by
  let s := (Real.pi - t) / 2
  have hs : 0 < s := by dsimp [s]; linarith [ht.2]
  have hsum : t + s < Real.pi := by dsimp [s]; linarith [ht.2]
  let f := e.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  let F := parallelFrameFlowMap g 0 (-s) f
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he _
  have hF : F ∈ o.positive := parallelFrameFlowMap_positive g o f hf (-s)
  have hbase : F.base = frameExponential g o e ((-s) • q.val) :=
    (frameExponential_direction_ray g o e he q (-s)).symm
  have hend : frameExponential g o F ((t + s) • coordinateVector 0) =
      frameExponential g o e (t • p.val) := by
    rw [frameExponential_shift_first g o f hf (t + s) (-s),
      show t + s + -s = t by ring]
    exact (frameExponential_direction_ray g o e he q t).symm.trans hqp
  have hnorm : ‖(t + s) • (coordinateVector 0 : FourSpace)‖ = t + s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos ht.1 hs)]
    simp [coordinateVector]
  have hmin := frameExponential_round_minimizing hRic hpositive hplus hminus F hF
    ((t + s) • coordinateVector 0) (by rw [hnorm]; exact hsum.le)
  rw [hbase, hend, hnorm] at hmin
  have hd := (metricDistance_eq_iff g _ _ (add_pos ht.1 hs).le).mp hmin
  rw [add_comm t s] at hd
  exact Subtype.ext (frameExponential_no_minimizing_corner g o e q.val p.val
    q.property p.property s t hs ht.1 hd)

theorem frameExponential_round_injOn_ball (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    InjOn (frameExponential g o e) (Metric.ball 0 Real.pi) := by
  intro v hv w hw heq
  have hvπ : ‖v‖ < Real.pi := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hwπ : ‖w‖ < Real.pi := by simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hn : ‖v‖ = ‖w‖ := by
    rw [← frameExponential_round_minimizing hRic hpositive hplus hminus e he v hvπ.le,
      ← frameExponential_round_minimizing hRic hpositive hplus hminus e he w hwπ.le, heq]
  by_cases hz : v = 0
  · subst v
    have hwzero : w = 0 := norm_eq_zero.mp (by simpa only [norm_zero] using hn.symm)
    exact hwzero.symm
  have hwz : w ≠ 0 := fun h => hz (norm_eq_zero.mp (by simpa only [h, norm_zero] using hn))
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
  let p : Directions := ⟨‖w‖⁻¹ • w, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hwz)]⟩
  have hq : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  have hp : ‖v‖ • p.val = w := by
    change ‖v‖ • (‖w‖⁻¹ • w) = w
    rw [hn, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hwz), one_smul]
  have hqp : q = p := round_direction_injective hRic hpositive hplus hminus e he q p
    ‖v‖ ⟨norm_pos_iff.mpr hz, hvπ⟩ (by rwa [hq, hp])
  rw [← hq, hqp, hp]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The round sphere map is globally bijective, hence a homeomorphism. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem roundSphereMap_injective (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    Function.Injective (roundSphereMap g o e) := by
  intro p q hpq
  have hn : ‖roundLog p‖ = ‖roundLog q‖ := by
    rw [roundLog_norm, roundLog_norm,
      ← roundSphereMap_radial_distance hRic hpositive hplus hminus e he p,
      ← roundSphereMap_radial_distance hRic hpositive hplus hminus e he q, hpq]
  have hsouth : ‖roundLog (antipode roundNorth)‖ = Real.pi := by
    rw [roundLog_norm]
    simp [antipode, roundNorth]
  by_cases hp : p = antipode roundNorth
  · subst p
    by_cases hq : q = antipode roundNorth
    · exact hq.symm
    · have hlt := roundLog_norm_lt_pi hq
      rw [← hn, hsouth] at hlt
      exact False.elim ((lt_irrefl _) hlt)
  by_cases hq : q = antipode roundNorth
  · subst q
    have hlt := roundLog_norm_lt_pi hp
    rw [hn, hsouth] at hlt
    exact False.elim ((lt_irrefl _) hlt)
  have hlog : roundLog p = roundLog q :=
    frameExponential_round_injOn_ball hRic hpositive hplus hminus e he
      (by simpa only [Metric.mem_ball, dist_zero_right] using roundLog_norm_lt_pi hp)
      (by simpa only [Metric.mem_ball, dist_zero_right] using roundLog_norm_lt_pi hq) hpq
  have h := congrArg roundSphereExponential hlog
  simpa only [roundSphereExponential_log] using h

def actualRoundHomeomorph (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) : RoundSphere4 ≃ₜ M := by
  let : CompactSpace RoundSphere4 := isCompact_iff_compactSpace.mp roundSphere_compact
  let E := Equiv.ofBijective (roundSphereMap g o e)
    ⟨roundSphereMap_injective hRic hpositive hplus hminus e he,
      roundSphereMap_surjective hRic hplus hminus e he⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := E)
    (roundSphereMap_continuous hRic hplus hminus e he)

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

/-! Actual normal coordinates for every point strictly before the complex cut locus. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_complex_interior_coordinates (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (e : FrameBundle g) (he : e ∈ o.positive) (x : M)
    (hR : metricDistance g e.base x < complexJacobiRadius) (hx : x ≠ e.base) :
    ∃ v : FourSpace, v ≠ 0 ∧ ‖v‖ < complexJacobiRadius ∧ frameExponential g o e v = x := by
  have hx' : x ∈ frameExponential g o e '' Metric.closedBall 0 complexJacobiRadius := by
    rw [frameExponential_complex_closedBall_image hRic hminus hdim e he]
    trivial
  obtain ⟨v,hv,hvx⟩ := hx'
  have hvR : ‖v‖ ≤ complexJacobiRadius := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  have hdist := frameExponential_complex_minimizing hRic hminus hdim e he v hvR
  rw [hvx] at hdist
  refine ⟨v,?_,by rwa [← hdist],hvx⟩
  intro hz
  rw [hz,frameExponential_zero] at hvx
  exact hx hvx.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact radial distance and uniqueness of the actual projective map
away from the cut locus. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_distance_from_center (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (p : ComplexProjective2) :
    metricDistance g e.base (actualComplexProjectiveMap g o e p) =
      Real.sqrt 2 * fubiniStudyDistance complexProjectiveNorth p := by
  obtain ⟨t,ht,q,hq⟩ := complexProjectivePolar_surjective p
  rw [← hq,actualComplexProjectiveMap_radial hRic hminus hdim w hstar hw hz e he hstd t ht q,
    fubiniStudyDistance_north_polar t ht q]
  field_simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal homogeneous lift represents the actual projective quotient map. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi
open scoped Manifold ContDiff
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_normal (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (w : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (w.val x) = w.val x)
    (hw : ∀ x, ‖w.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o w.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o w.val e = standardSelfDualForm)
    (v : FourSpace) (hv : v ≠ 0) (hr : ‖v‖ ≤ complexJacobiRadius) :
    actualComplexProjectiveMap g o e (complexNormalPoint v) = frameExponential g o e v := by
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul]
  rw [← hrad,complexNormalPoint_radial ‖v‖ (norm_pos_iff.mpr hv)]
  exact actualComplexProjectiveMap_polar hRic hminus
    (halfFlat_dimension_one_norm hRic hminus hdim) w hstar hw hz e he hstd
    ‖v‖ ⟨norm_nonneg _,hr⟩ q

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual smooth curves admit projective lifts with the exact horizontal speed in the open normal ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_local_curve_lift (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    {γ : ℝ → M} {s : ℝ} (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I4 1 γ s)
    (v : FourSpace) (hv : v ≠ 0) (hR : ‖v‖ < complexJacobiRadius)
    (hpoint : frameExponential g o e v = γ s) :
    ∃ (u : ℝ → UnitSphere CP2Vector) (w : CP2Vector),
      (u s).val = complexNormalLift v ∧
      HasDerivAt (fun t => (u t).val) w s ∧
      (fun t => actualComplexProjectiveMap g o e (complexSphereProjection (u t))) =ᶠ[𝓝 s] γ ∧
      Real.sqrt 2 * ‖complexHorizontalPart (u s).val w‖ =
        metricTangentNorm g (γ s) (mfderiv 𝓘(ℝ, ℝ) I4 γ s 1) := by
  have hnorm := halfFlat_dimension_one_norm hRic hminus hdim
  obtain ⟨C,hCv,hC⟩ := frameExponential_complex_localChart hRic hminus hnorm W hstar hw hz e he v hR
  have hCt : C v = γ s := (hC hCv).trans hpoint
  have hy : γ s ∈ C.target := hCt ▸ C.map_source hCv
  let α : ℝ → FourSpace := fun t => C.symm (γ t)
  have hαs : α s = v := by
    change C.symm (γ s) = v
    rw [← hCt]
    exact C.left_inv hCv
  have hα : ContDiffAt ℝ 1 α s := by
    have hi := frameExponential_complex_inverse_contMDiffAt hRic hminus hnorm
      W hstar hw hz e he v hv hR C hCv hC
    rw [hpoint] at hi
    exact (hi.comp s hγ).contDiffAt
  have hn : ∀ᶠ t in 𝓝 s, γ t ∈ C.target :=
    hγ.continuousAt.preimage_mem_nhds (C.open_target.mem_nhds hy)
  have hEq : (fun t => frameExponential g o e (α t)) =ᶠ[𝓝 s] γ := by
    filter_upwards [hn] with t ht
    exact (hC (C.map_target ht)).symm.trans (C.right_inv ht)
  let u : ℝ → UnitSphere CP2Vector := fun t => ⟨complexNormalLift (α t),complexNormalLift_norm _⟩
  let q : Directions := ⟨‖v‖⁻¹ • v,by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  have hrad : α s = ‖v‖ • q.val := by
    rw [hαs]
    change v = ‖v‖ • (‖v‖⁻¹ • v)
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul]
  let w := complexPolarLiftDifferential ‖v‖ q (deriv α s)
  have hd : HasDerivAt (fun t => (u t).val) w s :=
    complexNormalLift_hasDerivAt (hα.differentiableAt one_ne_zero).hasDerivAt
      (norm_pos_iff.mpr hv) q hrad
  have hnear0 : ∀ᶠ t in 𝓝 s, α t ≠ 0 :=
    hα.continuousAt.eventually_ne (by rwa [hαs])
  have hnearR : ∀ᶠ t in 𝓝 s, ‖α t‖ < complexJacobiRadius :=
    hα.continuousAt.norm.eventually_lt continuousAt_const (by rwa [hαs])
  have hlift : (fun t => actualComplexProjectiveMap g o e (complexSphereProjection (u t))) =ᶠ[𝓝 s] γ := by
    filter_upwards [hEq,hnear0,hnearR] with t ht ht0 htR
    exact (actualComplexProjectiveMap_normal hRic hminus hdim W hstar hw hz e he hstd
      (α t) ht0 htR.le).trans ht
  have hspeed := frameExponential_complex_curve_speed hRic hminus hnorm W hstar hw hz e he hstd
    (hα.differentiableAt one_ne_zero) (norm_pos_iff.mpr hv) q hrad
  have hder : deriv (fun t => complexNormalLift (α t)) s = w := hd.deriv
  rw [hder,← complexHorizontalPart_norm_sq _ _ (complexNormalLift_norm (α s)),
    Real.sqrt_sq (norm_nonneg _)] at hspeed
  exact ⟨u,w,by change complexNormalLift (α s) = _; rw [hαs],hd,hlift,
    hspeed.trans (metric_curve_speed_congr hEq)⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual distance along a projective great circle, including affine exceptions. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_greatCircle_distance_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (p q : CP2Vector) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : inner ℂ p q = 0)
    (hhead : p 0 ≠ 0 ∨ q 0 ≠ 0) (d : ℝ) (hd : d ∈ Icc 0 (Real.pi/2)) :
    metricDistance g
      (actualComplexProjectiveMap g o e (complexSphereProjection (complexGreatCircleUnit p q hp hq hpq 0)))
      (actualComplexProjectiveMap g o e (complexSphereProjection (complexGreatCircleUnit p q hp hq hpq d))) ≤
        Real.sqrt 2 * d := by
  let u := complexGreatCircleUnit p q hp hq hpq
  let γ : ℝ → M := fun t => actualComplexProjectiveMap g o e (complexSphereProjection (u t))
  obtain ⟨E,hE⟩ := complexGreatCircle_regular_off_finite p q hp hq hpq hhead
  have hcont : Continuous γ :=
    (actualComplexProjectiveMap_unit_continuous hRic hminus hdim W hstar hw hz e he hstd).comp
      (complexGreatCircleUnit_continuous p q hp hq hpq)
  have hreg (t : ℝ) (ht : t ∈ Ioo 0 d) (hexc : t ∉ E) :
      (u t).val 0 ≠ 0 ∧ complexVectorAffine (u t).val ≠ 0 :=
    hE t ⟨ht.1,ht.2.trans_le hd.2⟩ hexc
  have hbound := metricDistance_le_of_speed_bound_off_finite g E hd.1
    (Real.sqrt_nonneg 2) hcont
    (fun t ht hexc => actualComplexProjectiveMap_lift_contMDiffAt hRic hminus hdim
      W hstar hw hz e he hstd (complexGreatCircle_contDiff p q).contDiffAt
      (hreg t ht hexc).1 (hreg t ht hexc).2)
    (fun t ht hexc => ?_)
  · simpa only [sub_zero] using hbound
  · have hspeed := actualComplexProjectiveMap_lift_speed hRic hminus hdim W hstar hw hz e he hstd
      (complexGreatCircle_hasDerivAt p q t) (hreg t ht hexc).1 (hreg t ht hexc).2
    have hn : ‖complexHorizontalPart (u t).val (complexGreatCircleVelocity p q t)‖ = 1 :=
      complexGreatCircle_horizontal_speed p q hp hq hpq t
    rw [hn,mul_one] at hspeed
    exact hspeed.symm.le

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

theorem actualComplexProjective_section_germ (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    {γ : ℝ → M} {u : ℝ → UnitSphere CP2Vector} {s : ℝ}
    (hγ : ContinuousAt γ s)
    (hmap : (fun t => actualComplexProjectiveMap g o e (complexSphereProjection (u t))) =ᶠ[𝓝 s] γ)
    (hR : metricDistance g e.base (γ s) < complexJacobiRadius) :
    (fun t => S (γ t)) =ᶠ[𝓝 s] (fun t => complexSphereProjection (u t)) := by
  have hr : ∀ᶠ t in 𝓝 s, metricDistance g e.base (γ t) < complexJacobiRadius :=
    ((metricDistance_continuous g).continuousAt.comp (continuousAt_const.prodMk hγ)).eventually_lt
      continuousAt_const hR
  filter_upwards [hmap,hr] with t ht htr
  exact actualComplexProjectiveMap_fiber_eq_of_radial_lt hRic hminus hdim W hstar hw hz e he hstd
    (S (γ t)) (complexSphereProjection (u t)) ((hS (γ t)).trans ht.symm)
    (by rwa [hS (γ t)])

end
end PositiveEinsteinFour.Geometry
end


section

/-! The global distance upper bound when the initial point is in the standard affine chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_distance_le_of_affine (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (P Q : ComplexProjective2) (hhead : cp2UnitRep P 0 ≠ 0) :
    metricDistance g (actualComplexProjectiveMap g o e P) (actualComplexProjectiveMap g o e Q) ≤
      Real.sqrt 2 * fubiniStudyDistance P Q := by
  by_cases hpq : P = Q
  · subst Q
    rw [(metricDistance_eq_zero_iff g _ _).mpr rfl,fubiniStudyDistance_eq_arccos,
      cp2Overlap_self,Real.arccos_one,mul_zero]
  have hc1 : cp2Overlap P Q < 1 := lt_of_le_of_ne (cp2Overlap_le_one P Q)
    (fun h => hpq ((cp2Overlap_eq_one_iff P Q).mp h))
  obtain ⟨v,hv,hvn,hvQ,hcv⟩ := cp2_aligned_unit_representative P Q
  obtain ⟨q,hqn,horth,hend⟩ := complex_aligned_circle (cp2UnitRep P) v (cp2UnitRep_norm P)
    hvn (cp2Overlap P Q) (cp2Overlap_nonneg P Q) hc1 hcv
  let d := Real.arccos (cp2Overlap P Q)
  let u := complexGreatCircleUnit (cp2UnitRep P) q (cp2UnitRep_norm P) hqn horth
  have hP : complexSphereProjection (u 0) = P := by
    change Projectivization.mk ℂ (complexGreatCircle (cp2UnitRep P) q 0) _ = P
    simpa only [complexGreatCircle,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero]
      using cp2UnitRep_mk P
  have hQ : complexSphereProjection (u d) = Q := by
    change Projectivization.mk ℂ (complexGreatCircle (cp2UnitRep P) q d) _ = Q
    simpa only [d,hend] using hvQ
  have h := actualComplexProjectiveMap_greatCircle_distance_le hRic hminus hdim W hstar hw hz e he hstd
    (cp2UnitRep P) q (cp2UnitRep_norm P) hqn horth (Or.inl hhead) d
    ⟨Real.arccos_nonneg _,Real.arccos_le_pi_div_two.mpr (cp2Overlap_nonneg P Q)⟩
  change metricDistance g (actualComplexProjectiveMap g o e (complexSphereProjection (u 0)))
    (actualComplexProjectiveMap g o e (complexSphereProjection (u d))) ≤ Real.sqrt 2*d at h
  rw [hP,hQ] at h
  simpa only [d,fubiniStudyDistance_eq_arccos] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local angular distance estimates for a section of the actual projective map. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjective_inverse_angle_derivative (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (P : ComplexProjective2) {γ : ℝ → M} {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I4 1 γ s)
    (v : FourSpace) (hv : v ≠ 0) (hR : ‖v‖ < complexJacobiRadius)
    (hpoint : frameExponential g o e v = γ s)
    (hc0 : 0 < cp2Overlap P (S (γ s))) (hc1 : cp2Overlap P (S (γ s)) < 1) :
    DifferentiableAt ℝ (fun t => fubiniStudyDistance P (S (γ t))) s ∧
      |deriv (fun t => fubiniStudyDistance P (S (γ t))) s| ≤
        (Real.sqrt 2)⁻¹ * metricTangentNorm g (γ s) (mfderiv 𝓘(ℝ, ℝ) I4 γ s 1) := by
  obtain ⟨u,w,_,hu,hmap,hspeed⟩ := actualComplexProjectiveMap_local_curve_lift
    hRic hminus hdim W hstar hw hz e he hstd hγ v hv hR hpoint
  have hrad : metricDistance g e.base (γ s) < complexJacobiRadius := by
    rw [← hpoint,frameExponential_complex_minimizing hRic hminus hdim e he v hR.le]
    exact hR
  have heq := actualComplexProjective_section_germ hRic hminus hdim W hstar hw hz e he hstd
    S hS hγ.continuousAt hmap hrad
  have heqs : S (γ s) = complexSphereProjection (u s) := heq.self_of_nhds
  have hval (t : ℝ) : cp2Overlap P (complexSphereProjection (u t)) =
      ‖inner ℂ (cp2UnitRep P) (u t).val‖ :=
    cp2Overlap_of_unit_representatives P (complexSphereProjection (u t))
      (cp2UnitRep P) (u t).val (cp2UnitRep_ne_zero P) (unitSphere_ne_zero _)
      (cp2UnitRep_norm P) (u t).property (cp2UnitRep_mk P) rfl
  have h0 : 0 < ‖inner ℂ (cp2UnitRep P) (u s).val‖ := by
    rw [← hval,← heqs]
    exact hc0
  have h1 : ‖inner ℂ (cp2UnitRep P) (u s).val‖ < 1 := by
    rw [← hval,← heqs]
    exact hc1
  have hdist : (fun t => fubiniStudyDistance P (S (γ t))) =ᶠ[𝓝 s]
      (fun t => Real.arccos ‖inner ℂ (cp2UnitRep P) (u t).val‖) := by
    filter_upwards [heq] with t ht
    rw [ht,fubiniStudyDistance_eq_arccos,hval]
  obtain ⟨hd,hb⟩ := complex_angle_derivative_bound ⟨cp2UnitRep P,cp2UnitRep_norm P⟩ hu h0 h1
  have hd' := hd.hasDerivAt.congr_of_eventuallyEq hdist
  refine ⟨hd'.differentiableAt,?_⟩
  rw [hd'.deriv]
  apply hb.trans
  rw [← hspeed,← mul_assoc,inv_mul_cancel₀ (by positivity : Real.sqrt 2 ≠ 0),one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual projective map decreases the scaled Fubini--Study distance everywhere. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_distance_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (P Q : ComplexProjective2) :
    metricDistance g (actualComplexProjectiveMap g o e P) (actualComplexProjectiveMap g o e Q) ≤
      Real.sqrt 2 * fubiniStudyDistance P Q := by
  by_cases hhead : cp2UnitRep P 0 ≠ 0
  · exact actualComplexProjectiveMap_distance_le_of_affine hRic hminus hdim W hstar hw hz e he hstd P Q hhead
  have hp0 : cp2UnitRep P 0 = 0 := not_ne_iff.mp hhead
  let n : CP2Vector := EuclideanSpace.single 0 1
  have hn : ‖n‖ = 1 := by simp [n]
  have hpn : inner ℂ (cp2UnitRep P) n = 0 := by
    simp [n,EuclideanSpace.inner_single_right,hp0]
  let u : ℝ → UnitSphere CP2Vector :=
    complexGreatCircleUnit (cp2UnitRep P) n (cp2UnitRep_norm P) hn hpn
  have hu : Continuous u := complexGreatCircleUnit_continuous _ _ _ _ _
  have hP : complexSphereProjection (u 0) = P := by
    change Projectivization.mk ℂ (complexGreatCircle (cp2UnitRep P) n 0) _ = P
    simpa only [complexGreatCircle,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero]
      using cp2UnitRep_mk P
  have hmap := actualComplexProjectiveMap_unit_continuous hRic hminus hdim W hstar hw hz e he hstd
  have hleft : Continuous (fun t : ℝ => metricDistance g
      (actualComplexProjectiveMap g o e (complexSphereProjection (u t)))
      (actualComplexProjectiveMap g o e Q)) :=
    (metricDistance_continuous g).comp ((hmap.comp hu).prodMk continuous_const)
  have hright : Continuous (fun t : ℝ => Real.sqrt 2 *
      fubiniStudyDistance (complexSphereProjection (u t)) Q) :=
    continuous_const.mul ((fubiniStudyDistance_sphere_continuous Q).comp hu)
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, metricDistance g
      (actualComplexProjectiveMap g o e (complexSphereProjection (u t)))
      (actualComplexProjectiveMap g o e Q) ≤ Real.sqrt 2 *
      fubiniStudyDistance (complexSphereProjection (u t)) Q := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by positivity : (0 : ℝ) < Real.pi))] with t ht htpi
    have hus : (u t).val 0 ≠ 0 := by
      change (Real.cos t : ℂ) * cp2UnitRep P 0 + (Real.sin t : ℂ) * n 0 ≠ 0
      rw [hp0,mul_zero,zero_add]
      have hn0 : n 0 = 1 := by simp [n]
      rw [hn0,mul_one,ne_eq,Complex.ofReal_eq_zero]
      exact (Real.sin_pos_of_pos_of_lt_pi ht htpi).ne'
    exact actualComplexProjectiveMap_distance_le_of_affine hRic hminus hdim W hstar hw hz e he hstd
      _ Q (cp2UnitRep_coordinate_ne_zero_of_unit (u t) 0 hus)
  have h := le_of_tendsto_of_tendsto
    ((hleft.tendsto 0).mono_left nhdsWithin_le_nhds)
    ((hright.tendsto 0).mono_left nhdsWithin_le_nhds) hev
  simpa only [hP] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual cut locus is covered by two Lipschitz images of closed complex disks. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjectiveMap_cut_iff (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm) (P : ComplexProjective2) :
    metricDistance g e.base (actualComplexProjectiveMap g o e P) = complexJacobiRadius ↔
      cp2UnitRep P 0 = 0 := by
  rw [actualComplexProjectiveMap_distance_from_center hRic hminus hdim W hstar hw hz e he hstd,
    fubiniStudyDistance_eq_arccos,cp2Overlap_north]
  have hs : Real.sqrt 2 * (Real.pi/2) = complexJacobiRadius := by
    unfold complexJacobiRadius
    apply (eq_div_iff (by positivity : Real.sqrt 2 ≠ 0)).mpr
    calc
      Real.sqrt 2 * (Real.pi/2) * Real.sqrt 2 = (Real.pi/2) * (Real.sqrt 2)^2 := by ring
      _ = Real.pi := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  rw [← hs]
  constructor
  · intro h
    exact norm_eq_zero.mp (Real.arccos_eq_pi_div_two.mp
      (mul_left_cancel₀ (by positivity : Real.sqrt 2 ≠ 0) h))
  · intro h
    rw [h,norm_zero,Real.arccos_zero]

theorem actual_complex_cut_disk_cover (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm) (x : M) :
    metricDistance g e.base x = complexJacobiRadius ↔
      ∃ (i : Fin 2) (z : ℂ), ‖z‖ ≤ 1 ∧ actualComplexProjectiveMap g o e (complexCutPoint i z) = x := by
  constructor
  · intro hx
    obtain ⟨P,rfl⟩ := actualComplexProjectiveMap_surjective hRic hminus hdim W hstar hw hz e he hstd x
    obtain ⟨i,z,hznorm,hP⟩ := complexCutPoint_covers P
      ((actualComplexProjectiveMap_cut_iff hRic hminus hdim W hstar hw hz e he hstd P).mp hx)
    exact ⟨i,z,hznorm,congrArg (actualComplexProjectiveMap g o e) hP⟩
  · rintro ⟨i,z,_,rfl⟩
    exact (actualComplexProjectiveMap_cut_iff hRic hminus hdim W hstar hw hz e he hstd _).mpr
      (cp2UnitRep_cut_head i z)

theorem actual_complex_cut_disk_distance_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm) (i : Fin 2) (z w : ℂ) :
    metricDistance g (actualComplexProjectiveMap g o e (complexCutPoint i z))
      (actualComplexProjectiveMap g o e (complexCutPoint i w)) ≤
      (Real.sqrt 2 * Real.pi)*‖z-w‖ := by
  exact (actualComplexProjectiveMap_distance_le hRic hminus hdim W hstar hw hz e he hstd _ _).trans
    ((mul_le_mul_of_nonneg_left (complexCutPoint_distance_le i z w) (Real.sqrt_nonneg 2)).trans_eq (by ring))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Inverse distance along an interior curve, including zero and maximal angular values. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
attribute [local instance] complexProjectiveTopology complexProjective_t2Space
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjective_inverse_interior_curve_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (γ : ℝ → M) (a b C : ℝ) (hab : a ≤ b) (hC : 0 ≤ C) (E : Finset ℝ)
    (hγ : ContinuousOn γ (Icc a b))
    (hR : ∀ t ∈ Icc a b, metricDistance g e.base (γ t) < complexJacobiRadius)
    (hd : ∀ t ∈ Ioo a b, t ∉ E → ContMDiffAt 𝓘(ℝ, ℝ) I4 1 γ t)
    (hs : ∀ t ∈ Ioo a b, t ∉ E →
      metricTangentNorm g (γ t) (mfderiv 𝓘(ℝ, ℝ) I4 γ t 1) ≤ C)
    (hx : ∀ t ∈ Ioo a b, t ∉ E → γ t ≠ e.base) :
    fubiniStudyDistance (S (γ a)) (S (γ b)) ≤ ((Real.sqrt 2)⁻¹*C)*(b-a) := by
  let P := S (γ a)
  let f : ℝ → ℝ := fun t => fubiniStudyDistance P (S (γ t))
  have hcont : ContinuousOn f (Icc a b) := by
    intro t ht
    exact (fubiniStudyDistance_left_continuous P).continuousAt.comp_continuousWithinAt
      ((actualComplexProjective_section_continuousAt hRic hminus hdim W hstar hw hz e he hstd
        S hS (γ t) (hR t ht)).comp_continuousWithinAt (hγ t ht))
  have hfa : f a = 0 := by simp [f,P,fubiniStudyDistance_eq_arccos]
  have hpos (t : ℝ) (_ : t ∈ Icc a b) : 0 ≤ f t := Real.arccos_nonneg _
  have hbound : f b ≤ Real.pi/2 := by
    change fubiniStudyDistance P (S (γ b)) ≤ _
    rw [fubiniStudyDistance_eq_arccos]
    exact Real.arccos_le_pi_div_two.mpr (cp2Overlap_nonneg _ _)
  have hD (t : ℝ) (ht : t ∈ Ioo a b) (hexc : t ∉ E) (h0 : 0 < f t) (h1 : f t < Real.pi/2) :
      DifferentiableAt ℝ f t ∧ deriv f t ≤ (Real.sqrt 2)⁻¹*C := by
    have hc0 : 0 < cp2Overlap P (S (γ t)) := by
      apply Real.arccos_lt_pi_div_two.mp
      simpa only [f,fubiniStudyDistance_eq_arccos] using h1
    have hc1 : cp2Overlap P (S (γ t)) < 1 := by
      apply Real.arccos_pos.mp
      simpa only [f,fubiniStudyDistance_eq_arccos] using h0
    obtain ⟨v,hv,hvR,hvx⟩ := exists_complex_interior_coordinates hRic hminus hdim e he
      (γ t) (hR t ⟨ht.1.le,ht.2.le⟩) (hx t ht hexc)
    obtain ⟨hD,hb⟩ := actualComplexProjective_inverse_angle_derivative hRic hminus hdim
      W hstar hw hz e he hstd S hS P (hd t ht hexc) v hv hvR hvx hc0 hc1
    exact ⟨hD,(le_abs_self _).trans (hb.trans (mul_le_mul_of_nonneg_left (hs t ht hexc)
      (inv_nonneg.mpr (Real.sqrt_nonneg 2))))⟩
  exact bounded_angle_le_of_deriv_le f a b (Real.pi/2) ((Real.sqrt 2)⁻¹*C) E hab
    (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2)) hC) hcont hfa hpos hbound
    (fun t ht he h0 h1 => (hD t ht he h0 h1).1)
    (fun t ht he h0 h1 => (hD t ht he h0 h1).2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact inverse length control for actual minimizing geodesics that remain before the cut locus. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem complex_frameGeodesic_radial_distance (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (f : FrameBundle g) (hf : f ∈ o.positive) (t : ℝ) (ht : t ∈ Icc 0 complexJacobiRadius) :
    metricDistance g f.base (frameGeodesic g 0 f t) = t := by
  have hn : ‖t • (coordinateVector 0 : FourSpace)‖ = t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    simp [coordinateVector]
  have hm := frameExponential_complex_minimizing hRic hminus hdim f hf
    (t • coordinateVector 0) (by rw [hn]; exact ht.2)
  rwa [frameExponential_first_ray_all g o f hf t,hn] at hm

theorem complex_frameGeodesic_injOn (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (f : FrameBundle g) (hf : f ∈ o.positive) :
    InjOn (frameGeodesic g 0 f) (Icc 0 complexJacobiRadius) := by
  intro s hs t ht heq
  have h := congrArg (metricDistance g f.base) heq
  rwa [complex_frameGeodesic_radial_distance hRic hminus hdim f hf s hs,
    complex_frameGeodesic_radial_distance hRic hminus hdim f hf t ht] at h

theorem actualComplexProjective_inverse_interior_geodesic_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ e : FrameBundle g, twoFormFramedCovariantDerivative o W.val e = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (f : FrameBundle g) (hf : f ∈ o.positive) (d : ℝ) (hd : d ∈ Icc 0 complexJacobiRadius)
    (hR : ∀ t ∈ Icc 0 d, metricDistance g e.base (frameGeodesic g 0 f t) < complexJacobiRadius) :
    fubiniStudyDistance (S (frameGeodesic g 0 f 0)) (S (frameGeodesic g 0 f d)) ≤ (Real.sqrt 2)⁻¹*d := by
  classical
  let γ := frameGeodesic g 0 f
  let B : Set ℝ := Ioo 0 d ∩ γ ⁻¹' {e.base}
  have hsub : B ⊆ Icc 0 complexJacobiRadius := fun _ ht =>
    ⟨ht.1.1.le,ht.1.2.le.trans hd.2⟩
  have hi : InjOn γ B := (complex_frameGeodesic_injOn hRic hminus hdim f hf).mono hsub
  have hmap : MapsTo γ B {e.base} := fun _ ht => ht.2
  have hB : B.Finite := (finite_singleton e.base).of_injOn hmap hi
  have hbad (t : ℝ) (ht : t ∈ Ioo 0 d) (hexc : t ∉ hB.toFinset) : γ t ≠ e.base := by
    intro hx
    exact hexc (hB.mem_toFinset.mpr ⟨ht,hx⟩)
  have h := actualComplexProjective_inverse_interior_curve_le hRic hminus hdim W hstar hw hz e he hstd
    S hS γ 0 d 1 hd.1 zero_le_one hB.toFinset
    (frameGeodesic_contMDiff g 0 f).continuous.continuousOn hR
    (fun _ _ _ => (frameGeodesic_contMDiff g 0 f).contMDiffAt)
    (fun t _ _ => (round_frameGeodesic_real_speed f t).le) hbad
  simpa only [mul_one,sub_zero] using h

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

theorem complexCutChartMap_locallyLipschitz (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (c : M) (A : FourSpace →L[ℝ] FourSpace) (i : Fin 2) :
    ∀ z ∈ complexCutChartDomain g o e c i, ∃ K : ℝ≥0, ∃ V ∈ 𝓝 z,
      LipschitzOnWith K (complexCutChartMap g o e c A i) V := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  let F : ℂ → M := fun z => actualComplexProjectiveMap g o e (complexCutPoint i z)
  let K : ℝ≥0 := ⟨Real.sqrt 2 * Real.pi,mul_nonneg (Real.sqrt_nonneg 2) Real.pi_pos.le⟩
  have hLip : LipschitzWith K F := by
    intro z w
    change metricEDistance g (F z) (F w) ≤ (K : ℝ≥0∞)*edist z w
    rw [← ofReal_metricDistance g,edist_dist,dist_eq_norm,← ENNReal.ofReal_coe_nnreal]
    calc
      _ ≤ ENNReal.ofReal ((K : ℝ)*‖z-w‖) := ENNReal.ofReal_le_ofReal
        (actual_complex_cut_disk_distance_le hRic hminus hdim W hstar hw hz e he hstd i z w)
      _ = _ := ENNReal.ofReal_mul K.property
  exact metric_chart_lipschitz_image g c A F hLip.continuous K (fun z w => hLip z w)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact local distance preservation throughout the actual open normal ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualComplexProjective_section_local_distance (hRic : RicciThree g)
    (hminus : ∀ z, minusWeyl g z (o.frame z) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ z, twoFormHodge (W.val z) = W.val z)
    (hw : ∀ z, ‖W.val z‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (x y : M) (hmargin : metricDistance g e.base x + metricDistance g x y < complexJacobiRadius) :
    Real.sqrt 2 * fubiniStudyDistance (S x) (S y) = metricDistance g x y := by
  have hupper : metricDistance g x y ≤ Real.sqrt 2 * fubiniStudyDistance (S x) (S y) := by
    simpa only [hS x,hS y] using actualComplexProjectiveMap_distance_le
      hRic hminus hdim W hstar hw hz e he hstd (S x) (S y)
  apply le_antisymm ?_ hupper
  by_cases hxy : y = x
  · subst y
    rw [fubiniStudyDistance_eq_arccos,cp2Overlap_self,Real.arccos_one,mul_zero]
    exact metricDistance_nonneg g x x
  let f : FrameBundle g := ⟨x,o.frame x⟩
  have hf : f ∈ o.positive := o.frame_positive x
  have hxyR : metricDistance g f.base y < complexJacobiRadius := by
    change metricDistance g x y < _
    linarith [metricDistance_nonneg g e.base x]
  obtain ⟨v,hv,hvR,hvy⟩ := exists_complex_interior_coordinates hRic hminus hdim f hf y hxyR hxy
  have hvdist : ‖v‖ = metricDistance g x y := by
    have h := frameExponential_complex_minimizing hRic hminus hdim f hf v hvR.le
    rw [hvy] at h
    exact h.symm
  let q : Directions := ⟨‖v‖⁻¹ • v,by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  let f' := f.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  have hf' : f' ∈ o.positive := frameRotate_oriented_positive o f hf _
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul]
  have hstart : frameGeodesic g 0 f' 0 = x := by
    simp only [frameGeodesic,parallelFrameFlowMap_zero]
    rfl
  have hend : frameGeodesic g 0 f' ‖v‖ = y := by
    rw [← frameExponential_direction_ray g o f hf q ‖v‖,hrad,hvy]
  have hstay (t : ℝ) (ht : t ∈ Icc 0 ‖v‖) :
      metricDistance g e.base (frameGeodesic g 0 f' t) < complexJacobiRadius := by
    have hdist := complex_frameGeodesic_radial_distance hRic hminus hdim f' hf' t
      ⟨ht.1,ht.2.trans hvR.le⟩
    change metricDistance g x (frameGeodesic g 0 f' t) = t at hdist
    have hh := metricDistance_triangle g e.base x (frameGeodesic g 0 f' t)
    rw [hdist] at hh
    rw [← hvdist] at hmargin
    linarith [ht.2]
  have hbound := actualComplexProjective_inverse_interior_geodesic_le hRic hminus hdim
    W hstar hw hz e he hstd S hS f' hf' ‖v‖ ⟨norm_nonneg _,hvR.le⟩ hstay
  rw [hstart,hend,hvdist] at hbound
  have h := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg 2)
  rwa [← mul_assoc,mul_inv_cancel₀ (by positivity : Real.sqrt 2 ≠ 0),one_mul] at h

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual cut locus equals the two chart images. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actual_complex_distance_le_radius (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (x : M) : metricDistance g e.base x ≤ complexJacobiRadius := by
  obtain ⟨P,rfl⟩ := actualComplexProjectiveMap_surjective hRic hminus hdim W hstar hw hz e he hstd x
  obtain ⟨t,ht,q,rfl⟩ := complexProjectivePolar_surjective P
  rw [actualComplexProjectiveMap_radial hRic hminus hdim W hstar hw hz e he hstd t ht q]
  exact ht.2

theorem complexCutChartImage_iff (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (c : M) (A : FourSpace ≃L[ℝ] FourSpace) (x : FourSpace)
    (hx : A x ∈ (chartAt FourSpace c).target) :
    x ∈ ⋃ i, complexCutChartMap g o e c A.symm.toContinuousLinearMap i ''
      complexCutChartDomain g o e c i ↔
    metricDistance g e.base ((chartAt FourSpace c).symm (A x)) = complexJacobiRadius := by
  constructor
  · intro h
    obtain ⟨i,z,hzdom,hcoord⟩ := mem_iUnion.mp h
    have hchart : chartAt FourSpace c (actualComplexProjectiveMap g o e (complexCutPoint i z)) = A x := by
      have hh := congrArg A hcoord
      simpa only [complexCutChartMap,ContinuousLinearEquiv.coe_coe,A.apply_symm_apply] using hh
    have hF : actualComplexProjectiveMap g o e (complexCutPoint i z) =
        (chartAt FourSpace c).symm (A x) := by
      rw [← hchart]
      exact ((chartAt FourSpace c).left_inv hzdom).symm
    rw [← hF]
    exact (actualComplexProjectiveMap_cut_iff hRic hminus hdim W hstar hw hz e he hstd _).mpr
      (cp2UnitRep_cut_head i z)
  · intro h
    obtain ⟨i,z,_,hF⟩ := (actual_complex_cut_disk_cover hRic hminus hdim W hstar hw hz e he hstd _).mp h
    refine mem_iUnion.mpr ⟨i,z,?_,?_⟩
    · change actualComplexProjectiveMap g o e (complexCutPoint i z) ∈ (chartAt FourSpace c).source
      rw [hF]
      exact (chartAt FourSpace c).map_target hx
    · change A.symm (chartAt FourSpace c (actualComplexProjectiveMap g o e (complexCutPoint i z))) = x
      rw [hF,(chartAt FourSpace c).right_inv hx,A.symm_apply_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual inverse-distance control on a chart, including detours around its cut locus. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

theorem actualComplexProjective_section_chart_distance_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (c : M) (A : FourSpace ≃L[ℝ] FourSpace) (V : Set FourSpace)
    (hV : IsOpen V) (hconv : Convex ℝ V) (hVT : ∀ x ∈ V, A x ∈ (chartAt FourSpace c).target)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ x ∈ V, ∀ y ∈ V,
      metricDistance g ((chartAt FourSpace c).symm (A x)) ((chartAt FourSpace c).symm (A y)) ≤ K*dist x y)
    (x y : FourSpace) (hx : x ∈ V) (hy : y ∈ V)
    (hxR : metricDistance g e.base ((chartAt FourSpace c).symm (A x)) < complexJacobiRadius)
    (hyR : metricDistance g e.base ((chartAt FourSpace c).symm (A y)) < complexJacobiRadius) :
    fubiniStudyDistance (S ((chartAt FourSpace c).symm (A x)))
      (S ((chartAt FourSpace c).symm (A y))) ≤ (Real.sqrt 2)⁻¹*K*dist x y := by
  let T : FourSpace → M := fun z => (chartAt FourSpace c).symm (A z)
  let p := complexCutChartMap g o e c A.symm.toContinuousLinearMap
  let U := complexCutChartDomain g o e c
  let G := V \ ⋃ i, p i '' U i
  have hgood (z : FourSpace) (hzG : z ∈ G) : metricDistance g e.base (T z) < complexJacobiRadius := by
    apply lt_of_le_of_ne (actual_complex_distance_le_radius hRic hminus hdim W hstar hw hz e he hstd (T z))
    intro heq
    exact hzG.2 ((complexCutChartImage_iff hRic hminus hdim W hstar hw hz e he hstd c A z (hVT z hzG.1)).mpr heq)
  have hT : ContinuousOn T V :=
    (chartAt FourSpace c).symm.continuousOn.comp A.continuous.continuousOn hVT
  have hcont : ContinuousOn (S ∘ T) G := by
    intro z hzG
    exact (actualComplexProjective_section_continuousAt hRic hminus hdim W hstar hw hz e he hstd
      S hS (T z) (hgood z hzG)).comp_continuousWithinAt ((hT z hzG.1).mono sdiff_subset)
  have hlocal (z : FourSpace) (hzG : z ∈ G) :
      ∀ᶠ w in 𝓝[G] z, dist ((S ∘ T) z) ((S ∘ T) w) ≤ ((Real.sqrt 2)⁻¹*K)*dist z w := by
    have hD : ContinuousWithinAt (fun w => metricDistance g (T z) (T w)) V z :=
      (metricDistance_continuous g).continuousAt.comp_continuousWithinAt
        (continuousWithinAt_const.prodMk (hT z hzG.1))
    have hzpos : 0 < complexJacobiRadius-metricDistance g e.base (T z) := sub_pos.mpr (hgood z hzG)
    have hD0 : metricDistance g (T z) (T z) = 0 := (metricDistance_eq_zero_iff g _ _).mpr rfl
    have hevent : ∀ᶠ w in 𝓝[V] z,
        metricDistance g (T z) (T w) < complexJacobiRadius-metricDistance g e.base (T z) := by
      exact hD.eventually (gt_mem_nhds (by
        change metricDistance g (T z) (T z) < _
        rwa [hD0]))
    filter_upwards [nhdsWithin_mono z (show G ⊆ V from sdiff_subset) hevent,
      self_mem_nhdsWithin] with w hwclose hwG
    have heq := actualComplexProjective_section_local_distance hRic hminus hdim W hstar hw hz e he hstd
      S hS (T z) (T w) (by linarith)
    change fubiniStudyDistance (S (T z)) (S (T w)) ≤ _
    calc
      _ = (Real.sqrt 2)⁻¹ * metricDistance g (T z) (T w) := by
        rw [← heq,← mul_assoc,inv_mul_cancel₀ (by positivity : Real.sqrt 2 ≠ 0),one_mul]
      _ ≤ (Real.sqrt 2)⁻¹ * (K * dist z w) :=
        mul_le_mul_of_nonneg_left (hbound z hzG.1 w hwG.1) (by positivity)
      _ = _ := by ring
  have hxG : x ∈ G := ⟨hx,fun hh => (ne_of_lt hxR)
    ((complexCutChartImage_iff hRic hminus hdim W hstar hw hz e he hstd c A x (hVT x hx)).mp hh)⟩
  have hyG : y ∈ G := ⟨hy,fun hh => (ne_of_lt hyR)
    ((complexCutChartImage_iff hRic hminus hdim W hstar hw hz e he hstd c A y (hVT y hy)).mp hh)⟩
  exact dist_le_of_complexThinSet (S ∘ T) p U
    (fun i => complexCutChartMap_locallyLipschitz hRic hminus hdim W hstar hw hz e he hstd c A.symm.toContinuousLinearMap i)
    V hV hconv ((Real.sqrt 2)⁻¹*K) (mul_nonneg (by positivity) hK) hcont hlocal x y hxG hyG

end
end PositiveEinsteinFour.Geometry
end


section

/-! Density and the actual chart distance estimate give singleton fibers at the cut locus. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

theorem actualComplexProjectiveMap_injective (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    : Function.Injective (actualComplexProjectiveMap g o e) := by
  let F := actualComplexProjectiveMap g o e
  have hsurj : Function.Surjective F := actualComplexProjectiveMap_surjective hRic hminus hdim W hstar hw hz e he hstd
  let S := actualComplexProjectiveSection g o e hsurj
  have hS : Function.RightInverse S F := actualComplexProjectiveSection_rightInverse e hsurj
  have hF : Continuous F := actualComplexProjectiveMap_continuous hRic hminus hdim W hstar hw hz e he hstd
  intro P Q hPQ
  change F P = F Q at hPQ
  let c := F P
  obtain ⟨u,hu,huP⟩ := exists_complexInterior_sequence P
  obtain ⟨v,hv,hvQ⟩ := exists_complexInterior_sequence Q
  have huR (n : ℕ) : metricDistance g e.base (F (u n)) < complexJacobiRadius :=
    actualComplexProjectiveMap_interior_distance_lt hRic hminus hdim W hstar hw hz e he hstd (hu n)
  have hvR (n : ℕ) : metricDistance g e.base (F (v n)) < complexJacobiRadius :=
    actualComplexProjectiveMap_interior_distance_lt hRic hminus hdim W hstar hw hz e he hstd (hv n)
  have huS (n : ℕ) : S (F (u n)) = u n :=
    actualComplexProjectiveMap_fiber_eq_of_radial_lt hRic hminus hdim W hstar hw hz e he hstd
      _ _ (hS _) (by change metricDistance g e.base (F (S (F (u n)))) < _; rw [hS]; exact huR n)
  have hvS (n : ℕ) : S (F (v n)) = v n :=
    actualComplexProjectiveMap_fiber_eq_of_radial_lt hRic hminus hdim W hstar hw hz e he hstd
      _ _ (hS _) (by change metricDistance g e.base (F (S (F (v n)))) < _; rw [hS]; exact hvR n)
  have huc : Tendsto (fun n => F (u n)) atTop (𝓝 c) := hF.continuousAt.tendsto.comp huP
  have hvc : Tendsto (fun n => F (v n)) atTop (𝓝 c) := by
    simpa only [c,← hPQ,Function.comp_def] using! hF.continuousAt.tendsto.comp hvQ
  let Z := chartAt FourSpace c
  have hcsrc : c ∈ Z.source := mem_chart_source FourSpace c
  have huchart : Tendsto (fun n => Z (F (u n))) atTop (𝓝 (Z c)) := (Z.continuousAt hcsrc).tendsto.comp huc
  have hvchart : Tendsto (fun n => Z (F (v n))) atTop (𝓝 (Z c)) := (Z.continuousAt hcsrc).tendsto.comp hvc
  obtain ⟨r,hr,K,hball,hbound⟩ := exists_metric_chart_bound g c
  let V := Metric.ball (Z c) r
  have hVT (z : FourSpace) (hzV : z ∈ V) : z ∈ Z.target := hball (Metric.ball_subset_closedBall hzV)
  have hb (x : FourSpace) (hx : x ∈ V) (y : FourSpace) (hy : y ∈ V) :
      metricDistance g (Z.symm x) (Z.symm y) ≤ (K : ℝ)*dist x y := by
    have hh := hbound x (Metric.ball_subset_closedBall hx) y (Metric.ball_subset_closedBall hy)
    rw [← ofReal_metricDistance g,edist_dist,← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (p := (K : ℝ)) K.property] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg K.property dist_nonneg)).mp hh
  have hboundSeq : ∀ᶠ n in atTop, fubiniStudyDistance (u n) (v n) ≤
      (Real.sqrt 2)⁻¹*(K : ℝ)*dist (Z (F (u n))) (Z (F (v n))) := by
    filter_upwards [huchart (Metric.ball_mem_nhds _ hr),hvchart (Metric.ball_mem_nhds _ hr),
      huc (Z.open_source.mem_nhds hcsrc),hvc (Z.open_source.mem_nhds hcsrc)] with n hun hvn hus hvs
    have hsu : (chartAt FourSpace c).symm (Z (F (u n))) = F (u n) := Z.left_inv hus
    have hsv : (chartAt FourSpace c).symm (Z (F (v n))) = F (v n) := Z.left_inv hvs
    have hh := actualComplexProjective_section_chart_distance_le hRic hminus hdim W hstar hw hz e he hstd
      S hS c (ContinuousLinearEquiv.refl ℝ FourSpace) V Metric.isOpen_ball (convex_ball _ _)
      hVT (K : ℝ) K.property hb (Z (F (u n))) (Z (F (v n))) hun hvn
      (by simpa only [ContinuousLinearEquiv.refl_apply,hsu] using huR n)
      (by simpa only [ContinuousLinearEquiv.refl_apply,hsv] using hvR n)
    simpa only [ContinuousLinearEquiv.refl_apply,hsu,hsv,huS,hvS] using hh
  have hleft : Tendsto (fun n => fubiniStudyDistance (u n) (v n)) atTop
      (𝓝 (fubiniStudyDistance P Q)) := continuous_dist.continuousAt.tendsto.comp (huP.prodMk_nhds hvQ)
  have hright : Tendsto (fun n => (Real.sqrt 2)⁻¹*(K : ℝ)*dist (Z (F (u n))) (Z (F (v n))))
      atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := (Real.sqrt 2)⁻¹*(K : ℝ))).mul
      (continuous_dist.continuousAt.tendsto.comp (huchart.prodMk_nhds hvchart))
    simpa only [Function.comp_def,dist_self,mul_zero] using! hh
  have hzero : fubiniStudyDistance P Q = 0 := le_antisymm
    (le_of_tendsto_of_tendsto hleft hright hboundSeq) (by
      rw [fubiniStudyDistance_eq_arccos]; exact Real.arccos_nonneg _)
  exact (fubiniStudyDistance_eq_zero_iff P Q).mp hzero

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual CP2 parametrization is a global homeomorphism. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

def actualComplexHomeomorph (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    : ComplexProjective2 ≃ₜ M := by
  let : CompactSpace ComplexProjective2 := complexProjective_compactSpace
  let E := Equiv.ofBijective (actualComplexProjectiveMap g o e)
    ⟨actualComplexProjectiveMap_injective hRic hminus hdim W hstar hw hz e he hstd,
      actualComplexProjectiveMap_surjective hRic hminus hdim W hstar hw hz e he hstd⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := E)
    (actualComplexProjectiveMap_continuous hRic hminus hdim W hstar hw hz e he hstd)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


