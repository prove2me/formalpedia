-- Prove2me | solution 1 for ActuarialValuation.netLevelPremium_fundamental_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:11:32.035724+00:00
-- url     : https://prove2.me/submissions/a977fc4f-d150-40b3-92c6-196fc4d400b2

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_premiumDuePV
import Definitions.Def_actuarial_termPolicyLossPV
import Definitions.Def_actuarial_netLevelPremium
import Theorems.Thm_ActuarialValuation_deathYearEvent_measurable
import Theorems.Thm_ActuarialValuation_presentValue_memLp_two
import Theorems.Thm_ActuarialValuation_premiumDuePV_integrable
import Theorems.Thm_ActuarialValuation_premiumDuePV_expectation_positive
import Theorems.Thm_ActuarialValuation_netLevelPremium_benefit_scale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ) (b c : ℝ) (hn : 0 < n) (hv : 0 ≤ v)
    :
    (0 < ∫ ω, premiumDuePV K v n ω ∂P)
    ∧ ((∫ ω, termPolicyLossPV K v n b
          (netLevelPremium P K v n b) ω ∂P) = 0)
    ∧ (∀ π : ℝ, (∫ ω, termPolicyLossPV K v n b π ω ∂P) = 0 →
          π = netLevelPremium P K v n b)
    ∧ (netLevelPremium P K v n (c * b) =
          c * netLevelPremium P K v n b) := by
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
  have hequiv :
      (∫ ω, termPolicyLossPV K v n b
        (netLevelPremium P K v n b) ω ∂P) = 0 := by
    rw [hlin (netLevelPremium P K v n b)]
    unfold netLevelPremium
    field_simp [hne]
    ring
  have hunique :
      ∀ q : ℝ, (∫ ω, termPolicyLossPV K v n b q ω ∂P) = 0 →
          q = netLevelPremium P K v n b := by
    intro q hzero
    rw [hlin q] at hzero
    unfold netLevelPremium
    apply (eq_div_iff hne).2
    linarith
  exact ⟨hpos, hequiv, hunique,
    netLevelPremium_benefit_scale P K hK v n b c⟩
