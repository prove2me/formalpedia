-- Prove2me | solution 1 for ActuarialValuation.cm1FundingSurplus_mono_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:05:40.206029+00:00
-- url     : https://prove2.me/submissions/73dfaa64-db47-41d7-ad12-1b2809e7401b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase
import Definitions.Def_actuarial_cm1FundingSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary revalue growth : ℕ → ℝ) (n : ℕ)
    (a annuity c₁ c₂ : ℝ)
    (hF : 0 ≤ cm1AccumulatedSalaryBase salary growth n)
    (hc : c₁ ≤ c₂) :
    cm1FundingSurplus salary revalue growth n a annuity c₁ ≤
      cm1FundingSurplus salary revalue growth n a annuity c₂ := by
  simp only [cm1FundingSurplus, cm1DCFund]
  exact sub_le_sub_right (mul_le_mul_of_nonneg_right hc hF) _
