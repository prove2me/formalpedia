-- Prove2me | solution 1 for ActuarialValuation.cm1CAREFundingRate_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:07:09.06599+00:00
-- url     : https://prove2.me/submissions/320daaac-679e-419a-8842-1dc35e244121

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CARELiability
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase
import Definitions.Def_actuarial_cm1DCFund
import Definitions.Def_actuarial_cm1CAREFundingRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary revalue growth : ℕ → ℝ) (n : ℕ) (a annuity : ℝ)
    (hF : cm1AccumulatedSalaryBase salary growth n ≠ 0) :
    cm1DCFund salary growth n (cm1CAREFundingRate salary revalue growth n a annuity) =
      cm1CARELiability salary revalue n a annuity := by
  simp only [cm1DCFund, cm1CAREFundingRate]
  exact div_mul_cancel₀ _ hF
