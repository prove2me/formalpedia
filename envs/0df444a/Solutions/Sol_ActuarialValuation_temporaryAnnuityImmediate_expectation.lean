-- Prove2me | solution 1 for ActuarialValuation.temporaryAnnuityImmediate_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:28:30.430253+00:00
-- url     : https://prove2.me/submissions/324182eb-6386-4d5a-86fa-25b11afb8cbc

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityImmediatePV
import Definitions.Def_actuarial_curtateSurvivalEvent
import Theorems.Thm_ActuarialValuation_presentValue_expectation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    :
    (∫ ω, temporaryAnnuityImmediatePV K v n ω ∂P) = ∑ k ∈ Finset.range n, v ^ (k + 1) * (P (curtateSurvivalEvent K (k + 1))).toReal := by
  classical
  have htrigger :
      ∀ k ∈ Finset.range n, MeasurableSet (curtateSurvivalEvent K (k + 1)) := by
    intro k hk
    change MeasurableSet (K ⁻¹' Set.Ici (k + 1))
    exact hK measurableSet_Ici
  unfold temporaryAnnuityImmediatePV
  simpa only [mul_one] using
    (presentValue_expectation P (Finset.range n)
      (fun k : ℕ => k + 1) (fun t : ℕ => v ^ t)
      (fun _ : ℕ => (1 : ℝ))
      (fun k : ℕ => curtateSurvivalEvent K (k + 1)) htrigger)
