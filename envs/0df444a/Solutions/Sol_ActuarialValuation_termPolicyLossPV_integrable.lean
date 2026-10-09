-- Prove2me | solution 1 for ActuarialValuation.termPolicyLossPV_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:03:58.199822+00:00
-- url     : https://prove2.me/submissions/5cb8e4a3-3d3c-49e1-9f8c-35cb3d40d298

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
import Definitions.Def_actuarial_termPolicyLossPV
import Theorems.Thm_ActuarialValuation_deathYearEvent_measurable
import Theorems.Thm_ActuarialValuation_presentValue_memLp_two
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ) (b π : ℝ)
    : Integrable (termPolicyLossPV K v n b π) P := by
  classical
  have hprem : Integrable (premiumDuePV K v n) P := by
    have hterm (k : ℕ) :
        Integrable (fun ω : Ω => if k ≤ K ω then v ^ k else 0) P := by
      have hs : MeasurableSet {ω : Ω | k ≤ K ω} := by
        change MeasurableSet (K ⁻¹' Set.Ici k)
        exact hK measurableSet_Ici
      have hc : Integrable (fun _ : Ω => (v ^ k : ℝ)) P := integrable_const _
      have hfun :
          (fun ω : Ω => if k ≤ K ω then v ^ k else (0 : ℝ)) =
          {ω : Ω | k ≤ K ω}.indicator (fun _ : Ω => v ^ k) := by
        funext ω
        by_cases hk : k ≤ K ω <;> simp [Set.indicator, hk]
      rw [hfun]
      exact hc.indicator hs
    change Integrable (fun ω : Ω =>
      ∑ k ∈ Finset.range n, (if k ≤ K ω then v ^ k else 0)) P
    exact integrable_finset_sum (Finset.range n) (fun k hk => hterm k)
  have htrig : ∀ k ∈ Finset.range n,
      MeasurableSet (deathYearEvent K k) := by
    intro k hk
    exact deathYearEvent_measurable K hK k
  have hL2 : MemLp (termAssurancePV K v n) 2 P := by
    unfold termAssurancePV
    exact presentValue_memLp_two P (Finset.range n)
      (fun k : ℕ => k + 1) (fun t : ℕ => v ^ t)
      (fun _ : ℕ => (1 : ℝ)) (deathYearEvent K) htrig
  have hbenefit : Integrable (termAssurancePV K v n) P :=
    hL2.integrable (by norm_num)
  change Integrable (fun ω =>
    b * termAssurancePV K v n ω - π * premiumDuePV K v n ω) P
  exact (hbenefit.const_mul b).sub (hprem.const_mul π)
