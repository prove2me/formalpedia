-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.path_likelihood_radon_nikodym_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T18:39:28.724943+00:00
-- url     : https://prove2.me/submissions/ee892905-54ad-487b-8957-1c77869a9b9d

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZmeas : Measurable Z)
    (hZnonneg : ∀ ω : Ω, 0 ≤ Z ω)
    (hZintegrable : Integrable Z P)
    (hZmean : ∫ ω, Z ω ∂P = 1)
    (F : Ω → ℝ) (hFmeas : Measurable F)
    (hFZintegrable : Integrable (fun ω => F ω * Z ω) P) :
    let Q : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
    IsProbabilityMeasure Q ∧
      (∫ ω, F ω ∂Q) = (∫ ω, F ω * Z ω ∂P) := by
  let Q : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
  change IsProbabilityMeasure Q ∧
    (∫ ω, F ω ∂Q) = (∫ ω, F ω * Z ω ∂P)
  have hQone : Q Set.univ = 1 := by
    dsimp [Q]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hZintegrable
      (Filter.Eventually.of_forall hZnonneg)]
    rw [hZmean]
    simp
  refine ⟨isProbabilityMeasure_iff.mpr hQone, ?_⟩
  have hmeas : Measurable (fun ω : Ω => ENNReal.ofReal (Z ω)) :=
    hZmeas.ennreal_ofReal
  have hfinite : ∀ᵐ ω ∂P, ENNReal.ofReal (Z ω) < ∞ := by
    filter_upwards [] with ω
    simp
  change (∫ ω, F ω ∂P.withDensity (fun ω => ENNReal.ofReal (Z ω))) =
    ∫ ω, F ω * Z ω ∂P
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hfinite F]
  congr 1
  funext ω
  rw [ENNReal.toReal_ofReal (hZnonneg ω)]
  simp [smul_eq_mul, mul_comm]
