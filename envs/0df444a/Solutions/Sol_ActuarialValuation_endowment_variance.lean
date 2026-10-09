-- Prove2me | solution 1 for ActuarialValuation.endowment_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:39:23.566578+00:00
-- url     : https://prove2.me/submissions/ad71de42-d3b2-4d5c-851a-8e5988815c54

import Mathlib
import Definitions.Def_actuarial_endowmentAssurancePV
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_curtatePureEndowmentPV
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_deathYearEvent
import Theorems.Thm_ActuarialValuation_presentValue_memLp_two
import Theorems.Thm_ActuarialValuation_endowmentPV_decomposition
import Theorems.Thm_ActuarialValuation_endowment_expectation
import Theorems.Thm_ActuarialValuation_endowment_secondMoment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (v : ℝ) (n : ℕ)
    : ProbabilityTheory.variance (endowmentAssurancePV K v n) P = ((∑ k ∈ Finset.range n, (v ^ (k + 1)) ^ 2 * (P (deathYearEvent K k)).toReal) + (v ^ n) ^ 2 * (P (curtateSurvivalEvent K n)).toReal) - ((∑ k ∈ Finset.range n, v ^ (k + 1) * (P (deathYearEvent K k)).toReal) + v ^ n * (P (curtateSurvivalEvent K n)).toReal) ^ 2 := by
  classical
  have hA : MeasurableSet (curtateSurvivalEvent K n) := by
    change MeasurableSet (K ⁻¹' Set.Ici n)
    exact hK measurableSet_Ici
  have hdeath (k : ℕ) : MeasurableSet (deathYearEvent K k) := by
    change MeasurableSet (K ⁻¹' {k})
    exact hK (measurableSet_singleton k)
  have ht : MemLp (termAssurancePV K v n) 2 P := by
    unfold termAssurancePV
    exact presentValue_memLp_two P (Finset.range n) (fun k : ℕ => k + 1)
      (fun t : ℕ => v ^ t) (fun _ : ℕ => (1 : ℝ))
      (deathYearEvent K) (by intro k hk; exact hdeath k)
  have hm : MemLp (curtatePureEndowmentPV K v n) 2 P := by
    have heq : curtatePureEndowmentPV K v n =
        (curtateSurvivalEvent K n).indicator (fun _ : Ω => v ^ n) := by
      funext ω
      by_cases hw : ω ∈ curtateSurvivalEvent K n <;>
        simp [curtatePureEndowmentPV, Set.indicator, hw]
    rw [heq]
    exact (memLp_const (μ := P) (p := 2) (v ^ n)).indicator hA
  have heq : endowmentAssurancePV K v n =
      fun ω => termAssurancePV K v n ω + curtatePureEndowmentPV K v n ω := by
    funext ω
    exact endowmentPV_decomposition K v n ω
  have hLp : MemLp (endowmentAssurancePV K v n) 2 P := by
    rw [heq]
    exact ht.add hm
  rw [ProbabilityTheory.variance_eq_sub hLp]
  change (∫ ω, (endowmentAssurancePV K v n ω) ^ 2 ∂P) -
    (∫ ω, endowmentAssurancePV K v n ω ∂P) ^ 2 = _
  rw [endowment_secondMoment P K hK v n,
    endowment_expectation P K hK v n]
