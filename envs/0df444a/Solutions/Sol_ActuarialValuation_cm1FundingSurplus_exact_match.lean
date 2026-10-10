-- Prove2me | solution 1 for ActuarialValuation.cm1FundingSurplus_exact_match
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:57:58.622895+00:00
-- url     : https://prove2.me/submissions/11d04681-1d32-40e2-8c17-f5ccbf5a0f64

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase
import Definitions.Def_actuarial_cm1CAREFundingRate
import Definitions.Def_actuarial_cm1FundingSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary revalue growth : ℕ → ℝ) (n : ℕ) (a annuity : ℝ)
    (hF : cm1AccumulatedSalaryBase salary growth n ≠ 0) :
    cm1FundingSurplus salary revalue growth n a annuity
      (cm1CAREFundingRate salary revalue growth n a annuity) = 0 := by
  simp only [cm1FundingSurplus, cm1DCFund, cm1CAREFundingRate]
  exact sub_eq_zero.mpr (div_mul_cancel₀ _ hF)
