-- Prove2me | solution 1 for ActuarialValuation.cm1CAREFundingRate_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:13:33.1923+00:00
-- url     : https://prove2.me/submissions/787f0116-9e42-45fb-a18b-019076b7e3c1

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

theorem solution (salary revalue growth : ℕ → ℝ) (n : ℕ) (a annuity c : ℝ)
    (hF : cm1AccumulatedSalaryBase salary growth n ≠ 0)
    (hmatch : cm1DCFund salary growth n c =
      cm1CARELiability salary revalue n a annuity) :
    c = cm1CAREFundingRate salary revalue growth n a annuity := by
  rw [cm1CAREFundingRate]
  apply (eq_div_iff hF).2
  simpa only [cm1DCFund] using hmatch
