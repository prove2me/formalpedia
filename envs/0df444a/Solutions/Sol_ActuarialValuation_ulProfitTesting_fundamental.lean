-- Prove2me | solution 1 for ActuarialValuation.ulProfitTesting_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:19:19.160494+00:00
-- url     : https://prove2.me/submissions/e981f05d-7247-40cf-90c6-cb2849e59723

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulPremiumAlloc
import Definitions.Def_actuarial_ulUnallocated
import Definitions.Def_actuarial_ulBidOfferCost
import Definitions.Def_actuarial_ulDeathBenefit
import Definitions.Def_actuarial_ulNetAmountAtRisk
import Definitions.Def_actuarial_ulDeathCost
import Definitions.Def_actuarial_ulNonUnitProfit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (premium allocation offer bid fund guarantee mortality income expense commission guaranteedExpense : ℝ) (hprice : 0<offer) (hbid : 0≤bid) (hspread : bid≤offer) (hp : 0≤premium) (ha : 0≤allocation) (hq : 0≤mortality) : (ulUnallocated premium allocation+ulPremiumAlloc premium allocation=premium) ∧ (0≤ulBidOfferCost (ulPremiumAlloc premium allocation) offer bid) ∧ (ulDeathBenefit fund guarantee=fund+ulNetAmountAtRisk fund guarantee) ∧ (ulNonUnitProfit income expense commission (ulDeathCost mortality fund guarantee) guaranteedExpense+expense+commission+ulDeathCost mortality fund guarantee+guaranteedExpense=income) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold ulUnallocated
    ring
  · have halloc : 0 ≤ ulPremiumAlloc premium allocation := by
      unfold ulPremiumAlloc
      exact mul_nonneg hp ha
    have hmul : ulPremiumAlloc premium allocation * bid ≤
        ulPremiumAlloc premium allocation * offer :=
      mul_le_mul_of_nonneg_left hspread halloc
    unfold ulBidOfferCost ulUnitsBidValue ulBuyUnits
    have heq : (ulPremiumAlloc premium allocation / offer) * bid =
        ulPremiumAlloc premium allocation * bid / offer := by ring
    rw [heq]
    exact sub_nonneg.mpr ((div_le_iff₀ hprice).2 hmul)
  · unfold ulDeathBenefit ulNetAmountAtRisk
    rcases le_total guarantee fund with h | h
    · rw [max_eq_left h, max_eq_left (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_right h, max_eq_right (sub_nonneg.mpr h)]
      ring
  · unfold ulNonUnitProfit
    ring
