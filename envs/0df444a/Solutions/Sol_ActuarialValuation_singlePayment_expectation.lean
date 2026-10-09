-- Prove2me | solution 1 for ActuarialValuation.singlePayment_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:12:37.347152+00:00
-- url     : https://prove2.me/submissions/f14ff5e3-b7ff-4dc0-81ad-291555a1582c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- Proof template from a successful private Prove2Me compiler preflight.
Publication-time imports and the 'theorem solution' wrapper are not yet verified. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (discount amount : ℝ) :
    (∫ ω, discount * amount * (A.indicator (fun _ : Ω => (1 : ℝ)) ω) ∂P =
      discount * amount * (P A).toReal) := by
  classical
  have hf :
      (fun ω : Ω => discount * amount *
        A.indicator (fun _ : Ω => (1 : ℝ)) ω) =
      A.indicator (fun _ : Ω => discount * amount) := by
    funext ω
    by_cases hw : ω ∈ A
    · simp [Set.indicator, hw]
    · simp [Set.indicator, hw]
  rw [hf]
  simpa [MeasureTheory.Measure.real, smul_eq_mul, mul_comm] using
    (MeasureTheory.integral_indicator_const (μ := P) (discount * amount) hA)
