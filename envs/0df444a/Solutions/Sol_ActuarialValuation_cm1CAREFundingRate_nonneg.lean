-- Prove2me | solution 1 for ActuarialValuation.cm1CAREFundingRate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:51:23.360637+00:00
-- url     : https://prove2.me/submissions/7857e2da-ad11-41b7-8ec2-c0700e9a2490

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CARELiability
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase
import Definitions.Def_actuarial_cm1CAREFundingRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary revalue growth : ℕ → ℝ) (n : ℕ)
    (a annuity : ℝ)
    (hL : 0 ≤ cm1CARELiability salary revalue n a annuity)
    (hF : 0 < cm1AccumulatedSalaryBase salary growth n) :
    0 ≤ cm1CAREFundingRate salary revalue growth n a annuity := by
  simp only [cm1CAREFundingRate]
  exact div_nonneg hL (le_of_lt hF)
