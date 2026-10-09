-- Prove2me | solution 1 for ActuarialValuation.termAssurance_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T19:22:42.280322+00:00
-- url     : https://prove2.me/submissions/a48097ba-aca9-4b8e-ac75-1fa7eb34eb49

import Mathlib
import Definitions.Def_actuarial_deathYearEvent
import Definitions.Def_actuarial_termAssurancePV
import Theorems.Thm_ActuarialValuation_presentValue_expectation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    :
    (∫ ω, termAssurancePV K v n ω ∂P) =
      ∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal := by
  classical
  have htrigger :
      ∀ k ∈ Finset.range n, MeasurableSet (deathYearEvent K k) := by
    intro k hk
    change MeasurableSet (K ⁻¹' ({k} : Set ℕ))
    exact hK (measurableSet_singleton k)
  unfold termAssurancePV
  simpa only [mul_one] using
    (presentValue_expectation P (Finset.range n)
      (fun k : ℕ => k + 1) (fun t : ℕ => v ^ t)
      (fun _ : ℕ => (1 : ℝ)) (deathYearEvent K) htrigger)
