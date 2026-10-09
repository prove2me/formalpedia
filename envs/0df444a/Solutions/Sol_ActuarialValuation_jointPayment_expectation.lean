-- Prove2me | solution 1 for ActuarialValuation.jointPayment_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:12:42.182765+00:00
-- url     : https://prove2.me/submissions/b9f94bc1-b595-4794-94c6-ee6552c28c51

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- Proof template from a successful private Prove2Me compiler preflight.
Publication-time imports and the 'theorem solution' wrapper are not yet verified. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫ ω, (A.indicator (fun _ : Ω => (1 : ℝ)) ω) *
      (B.indicator (fun _ : Ω => (1 : ℝ)) ω) ∂P =
      (P (A ∩ B)).toReal) := by
  classical
  have hf :
      (fun ω : Ω =>
        A.indicator (fun _ : Ω => (1 : ℝ)) ω *
          B.indicator (fun _ : Ω => (1 : ℝ)) ω) =
      (A ∩ B).indicator (fun _ : Ω => (1 : ℝ)) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;>
      simp [Set.indicator, ha, hb]
  rw [hf]
  simpa [MeasureTheory.Measure.real, smul_eq_mul] using
    (MeasureTheory.integral_indicator_const (μ := P) (1 : ℝ) (hA.inter hB))
