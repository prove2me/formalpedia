-- Prove2me | solution 1 for ActuarialValuation.cm1FundingSurplus_nonnegative_above_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:56:48.850988+00:00
-- url     : https://prove2.me/submissions/e8798195-ddac-4fd5-b9dc-8d58bd5e9334

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AccumulatedSalaryBase
import Definitions.Def_actuarial_cm1CAREFundingRate
import Definitions.Def_actuarial_cm1FundingSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary revalue growth : ℕ → ℝ) (n : ℕ) (a annuity c : ℝ)
    (hF : 0 < cm1AccumulatedSalaryBase salary growth n)
    (hc : cm1CAREFundingRate salary revalue growth n a annuity ≤ c) :
    0 ≤ cm1FundingSurplus salary revalue growth n a annuity c := by
  have hrate :
      cm1CARELiability salary revalue n a annuity /
          cm1AccumulatedSalaryBase salary growth n ≤ c := by
    simpa only [cm1CAREFundingRate] using hc
  have hfund :
      cm1CARELiability salary revalue n a annuity ≤
        c * cm1AccumulatedSalaryBase salary growth n :=
    (div_le_iff₀ hF).mp hrate
  simpa only [cm1FundingSurplus, cm1DCFund] using
    (sub_nonneg.mpr hfund)
