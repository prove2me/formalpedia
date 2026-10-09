-- Prove2me | solution 1 for ActuarialValuation.netLevelPremium_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:09:15.043782+00:00
-- url     : https://prove2.me/submissions/c1a1cf6b-77aa-481d-bdc0-cb767b977261

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
import Definitions.Def_actuarial_termPolicyLossPV
import Definitions.Def_actuarial_netLevelPremium
import Theorems.Thm_ActuarialValuation_deathYearEvent_measurable
import Theorems.Thm_ActuarialValuation_presentValue_memLp_two
import Theorems.Thm_ActuarialValuation_premiumDuePV_integrable
import Theorems.Thm_ActuarialValuation_premiumDuePV_expectation_positive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ) (b π : ℝ) (hn : 0 < n) (hv : 0 ≤ v)
    (hzero : (∫ ω, termPolicyLossPV K v n b π ω ∂P) = 0)
    : π = netLevelPremium P K v n b := by
  have htrig : ∀ k ∈ Finset.range n,
      MeasurableSet (deathYearEvent K k) := by
    intro k hk
    exact deathYearEvent_measurable K hK k
  have hL2 : MemLp (termAssurancePV K v n) 2 P := by
    unfold termAssurancePV
    exact presentValue_memLp_two P (Finset.range n)
      (fun k : ℕ => k + 1) (fun t : ℕ => v ^ t)
      (fun _ : ℕ => (1 : ℝ)) (deathYearEvent K) htrig
  have hA : Integrable (termAssurancePV K v n) P :=
    hL2.integrable (by norm_num)
  have hY : Integrable (premiumDuePV K v n) P :=
    premiumDuePV_integrable P K hK v n
  have hlin (q : ℝ) :
      (∫ ω, termPolicyLossPV K v n b q ω ∂P) =
      b * (∫ ω, termAssurancePV K v n ω ∂P) -
      q * (∫ ω, premiumDuePV K v n ω ∂P) := by
    change (∫ ω, b * termAssurancePV K v n ω -
        q * premiumDuePV K v n ω ∂P) = _
    rw [integral_sub (hA.const_mul b) (hY.const_mul q)]
    simp only [integral_const_mul]
  have hpos : 0 < ∫ ω, premiumDuePV K v n ω ∂P :=
    premiumDuePV_expectation_positive P K hK v n hn hv
  have hne : (∫ ω, premiumDuePV K v n ω ∂P) ≠ 0 := ne_of_gt hpos
  rw [hlin π] at hzero
  unfold netLevelPremium
  apply (eq_div_iff hne).2
  linarith
