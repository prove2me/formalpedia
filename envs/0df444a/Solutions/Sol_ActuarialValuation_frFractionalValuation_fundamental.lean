-- Prove2me | solution 1 for ActuarialValuation.frFractionalValuation_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T11:47:18.138627+00:00
-- url     : https://prove2.me/submissions/95c1c161-3308-4b99-a756-03d825d8bca8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueValue
import Definitions.Def_actuarial_frAnnualDueValue
import Definitions.Def_actuarial_frPremiumPV
import Definitions.Def_actuarial_frNetPremium
import Definitions.Def_actuarial_frFractionalReserve
import Definitions.Def_actuarial_frUddSurvival
import Definitions.Def_actuarial_frForceSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (discount : ℝ → ℝ) (p qSeries : ℕ → ℝ) (n : ℕ) (benefitPV annuityPV assets premium benefit q s growth endDiscount mu : ℝ) (ha : annuityPV ≠ 0) (hs : frUddSurvival q s ≠ 0) : (frDueValue c discount p qSeries n 1 = frAnnualDueValue c discount p n) ∧ (frPremiumPV (frNetPremium benefitPV annuityPV) annuityPV = benefitPV) ∧ (frFractionalReserve assets premium benefit q s growth endDiscount * frUddSurvival q s + s*q*benefit*endDiscount = (assets+premium)*growth) ∧ (0 < frForceSurvival mu s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold frDueValue frAnnualDueValue
    apply Finset.sum_congr rfl
    intro k hk
    simp [frDueTerm, frTime, frUddSurvival]
  · simp [frPremiumPV, frNetPremium, ha]
  · simp [frFractionalReserve, hs]
  · simpa [frForceSurvival] using Real.exp_pos (-mu * s)
