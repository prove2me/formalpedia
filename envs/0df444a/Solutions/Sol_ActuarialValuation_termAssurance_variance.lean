-- Prove2me | solution 1 for ActuarialValuation.termAssurance_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T19:25:27.219979+00:00
-- url     : https://prove2.me/submissions/8c23db00-5004-4a5b-9769-627248affe76

import Mathlib
import Definitions.Def_actuarial_deathYearEvent
import Definitions.Def_actuarial_termAssurancePV
import Theorems.Thm_ActuarialValuation_presentValue_memLp_two
import Theorems.Thm_ActuarialValuation_termAssurance_expectation
import Theorems.Thm_ActuarialValuation_termAssurance_secondMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    :
    ProbabilityTheory.variance (termAssurancePV K v n) P =
      (∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal) -
      (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) ^ 2 := by
  classical
  have htrigger :
      ∀ k ∈ Finset.range n, MeasurableSet (deathYearEvent K k) := by
    intro k hk
    change MeasurableSet (K ⁻¹' ({k} : Set ℕ))
    exact hK (measurableSet_singleton k)
  have hLp : MemLp (termAssurancePV K v n) 2 P := by
    unfold termAssurancePV
    exact presentValue_memLp_two P (Finset.range n)
      (fun k : ℕ => k + 1) (fun t : ℕ => v ^ t)
      (fun _ : ℕ => (1 : ℝ)) (deathYearEvent K) htrigger
  rw [ProbabilityTheory.variance_eq_sub hLp]
  change (∫ ω, (termAssurancePV K v n ω) ^ 2 ∂P) -
      (∫ ω, termAssurancePV K v n ω ∂P) ^ 2 = _
  rw [termAssurance_secondMoment P K hK v n,
      termAssurance_expectation P K hK v n]
