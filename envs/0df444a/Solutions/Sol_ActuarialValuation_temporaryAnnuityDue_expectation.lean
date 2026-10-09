-- Prove2me | solution 1 for ActuarialValuation.temporaryAnnuityDue_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:28:06.694198+00:00
-- url     : https://prove2.me/submissions/4842c687-f251-49e2-907e-2c757c7e9ecd

import Mathlib
import Definitions.Def_actuarial_temporaryAnnuityDuePV
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
    (∫ ω, temporaryAnnuityDuePV K v n ω ∂P) = ∑ k ∈ Finset.range n, v ^ k * (P (curtateSurvivalEvent K k)).toReal := by
  classical
  have htrigger :
      ∀ k ∈ Finset.range n, MeasurableSet (curtateSurvivalEvent K k) := by
    intro k hk
    change MeasurableSet (K ⁻¹' Set.Ici k)
    exact hK measurableSet_Ici
  unfold temporaryAnnuityDuePV
  simpa only [mul_one] using
    (presentValue_expectation P (Finset.range n)
      (fun k : ℕ => k) (fun t : ℕ => v ^ t)
      (fun _ : ℕ => (1 : ℝ)) (curtateSurvivalEvent K) htrigger)
