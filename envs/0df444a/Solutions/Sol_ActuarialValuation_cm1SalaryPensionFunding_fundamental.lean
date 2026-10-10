-- Prove2me | solution 1 for ActuarialValuation.cm1SalaryPensionFunding_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:50:06.157273+00:00
-- url     : https://prove2.me/submissions/a6fb9198-38d1-4153-aeb1-293abe5111fc

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CARELiability
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase
import Definitions.Def_actuarial_cm1DCFund
import Definitions.Def_actuarial_cm1CAREFundingRate
import Definitions.Def_actuarial_cm1FundingSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary revalue growth : ℕ → ℝ) (n : ℕ)
    (accrual annuity : ℝ)
    (hF : 0 < cm1AccumulatedSalaryBase salary growth n)
    (hL : 0 ≤ cm1CARELiability salary revalue n accrual annuity) :
    (0 ≤ cm1CAREFundingRate salary revalue growth n accrual annuity) ∧
      (cm1DCFund salary growth n
        (cm1CAREFundingRate salary revalue growth n accrual annuity) =
          cm1CARELiability salary revalue n accrual annuity) ∧
      (∀ c : ℝ, cm1CAREFundingRate salary revalue growth n accrual annuity ≤ c →
        0 ≤ cm1FundingSurplus salary revalue growth n accrual annuity c) := by
  constructor
  · simp only [cm1CAREFundingRate]
    exact div_nonneg hL (le_of_lt hF)
  constructor
  · simp only [cm1DCFund, cm1CAREFundingRate]
    exact div_mul_cancel₀ _ (ne_of_gt hF)
  · intro c hc
    have hrate :
        cm1CARELiability salary revalue n accrual annuity /
            cm1AccumulatedSalaryBase salary growth n ≤ c := by
      simpa only [cm1CAREFundingRate] using hc
    have hfund :
        cm1CARELiability salary revalue n accrual annuity ≤
          c * cm1AccumulatedSalaryBase salary growth n :=
      (div_le_iff₀ hF).mp hrate
    simpa only [cm1FundingSurplus, cm1DCFund] using
      (sub_nonneg.mpr hfund)
