-- Prove2me | solution 2 for ActuarialValuation.netLevelPremium_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:13:24.786004+00:00
-- url     : https://prove2.me/submissions/468c812b-975f-459d-957c-12d4bd21a849

import Mathlib
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_termPolicyLossPV
import Definitions.Def_actuarial_netLevelPremium
import Theorems.Thm_ActuarialValuation_premiumDuePV_expectation_positive
import Theorems.Thm_ActuarialValuation_termPolicyLoss_expected_linear
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
  have hpos : 0 < ∫ ω, premiumDuePV K v n ω ∂P :=
    premiumDuePV_expectation_positive P K hK v n hn hv
  have hne : (∫ ω, premiumDuePV K v n ω ∂P) ≠ 0 := ne_of_gt hpos
  rw [termPolicyLoss_expected_linear P K hK v n b π] at hzero
  unfold netLevelPremium
  apply (eq_div_iff hne).2
  linarith
