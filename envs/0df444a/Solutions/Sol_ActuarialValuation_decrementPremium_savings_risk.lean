-- Prove2me | solution 1 for ActuarialValuation.decrementPremium_savings_risk
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:51:29.230989+00:00
-- url     : https://prove2.me/submissions/3cecbcae-bcb3-430c-bc3b-4f9b085c5ef0

import Mathlib
import Definitions.Def_actuarial_decrementAnnualPremium
import Definitions.Def_actuarial_decrementRiskPremium
import Definitions.Def_actuarial_decrementSavingsPremium
import Definitions.Def_actuarial_isAnnualDecrementLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {J : Type*} [Fintype J] (p : ℝ) (q b : J → ℝ) (v R Rnext : ℝ)
  (h : isAnnualDecrementLaw p q)
  :
  decrementAnnualPremium p q b v R Rnext =
    decrementSavingsPremium v R Rnext +
      decrementRiskPremium q b v Rnext := by
  classical
  rcases h with ⟨hp_nonneg, hq_nonneg, htotal⟩
  have hp : p = 1 - (∑ j : J, q j) := by linarith
  have hsum : (∑ j : J, q j * (b j - Rnext)) =
      (∑ j : J, q j * b j) - (∑ j : J, q j) * Rnext := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_mul]
  change v * (p * Rnext + (∑ j : J, q j * b j)) - R =
    (v * Rnext - R) + v * (∑ j : J, q j * (b j - Rnext))
  rw [hsum, hp]
  ring
