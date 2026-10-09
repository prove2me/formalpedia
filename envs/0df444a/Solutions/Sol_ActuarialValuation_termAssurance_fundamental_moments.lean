-- Prove2me | solution 1 for ActuarialValuation.termAssurance_fundamental_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T19:25:39.869013+00:00
-- url     : https://prove2.me/submissions/fade1b81-1043-4e3f-8534-42f9c5fea099

import Mathlib
import Definitions.Def_actuarial_deathYearEvent
import Definitions.Def_actuarial_termAssurancePV
import Theorems.Thm_ActuarialValuation_termAssurance_expectation
import Theorems.Thm_ActuarialValuation_termAssurance_secondMoment
import Theorems.Thm_ActuarialValuation_termAssurance_variance
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
    ((∫ ω, termAssurancePV K v n ω ∂P) =
      ∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) ∧
    ((∫ ω, (termAssurancePV K v n ω) ^ 2 ∂P) =
      ∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal) ∧
    (ProbabilityTheory.variance (termAssurancePV K v n) P =
      (∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal) -
      (∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) ^ 2) := by
  exact ⟨termAssurance_expectation P K hK v n,
    termAssurance_secondMoment P K hK v n,
    termAssurance_variance P K hK v n⟩
