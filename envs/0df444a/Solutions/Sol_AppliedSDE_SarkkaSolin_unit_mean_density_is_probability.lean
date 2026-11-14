-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.unit_mean_density_is_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:52:17.799518+00:00
-- url     : https://prove2.me/submissions/8c711b3e-071b-4d79-8517-3132ab6d3090

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ)
    (hZi : Integrable Z P)
    (hZnonneg : ∀ ω, 0 ≤ Z ω)
    (hZmean : ∫ ω, Z ω ∂P = 1) :
    IsProbabilityMeasure
      (P.withDensity (fun ω => ENNReal.ofReal (Z ω))) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hZi
    (Filter.Eventually.of_forall hZnonneg)]
  simp only [hZmean, ENNReal.ofReal_one]