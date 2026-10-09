-- Prove2me | solution 1 for ActuarialValuation.endowment_secondMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:33:54.348476+00:00
-- url     : https://prove2.me/submissions/fab2ac47-4486-4495-8062-3376b31ac1c7

import Mathlib
import Definitions.Def_actuarial_endowmentAssurancePV
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deathYearEvent
import Theorems.Thm_ActuarialValuation_endowment_expectation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    : (∫ ω, (endowmentAssurancePV K v n ω) ^ 2 ∂P) = (∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal) + (v ^ n) ^ 2 * (P (curtateSurvivalEvent K n)).toReal := by
  have hp (m : ℕ) : (v ^ 2) ^ m = (v ^ m) ^ 2 := by
    calc
      (v ^ 2) ^ m = v ^ (2 * m) := (pow_mul v 2 m).symm
      _ = v ^ (m * 2) := by rw [Nat.mul_comm]
      _ = (v ^ m) ^ 2 := pow_mul v m 2
  have hpoint (ω : Ω) :
      (endowmentAssurancePV K v n ω) ^ 2 =
        endowmentAssurancePV K (v ^ 2) n ω := by
    unfold endowmentAssurancePV
    exact (hp (min (K ω + 1) n)).symm
  calc
    (∫ ω, (endowmentAssurancePV K v n ω) ^ 2 ∂P) =
        (∫ ω, endowmentAssurancePV K (v ^ 2) n ω ∂P) := by
      congr 1
      funext ω
      exact hpoint ω
    _ = (∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 *
        (P (deathYearEvent K k)).toReal) +
        (v ^ n) ^ 2 * (P (curtateSurvivalEvent K n)).toReal := by
      have h := endowment_expectation P K hK (v ^ 2) n
      simp_rw [hp] at h
      exact h
