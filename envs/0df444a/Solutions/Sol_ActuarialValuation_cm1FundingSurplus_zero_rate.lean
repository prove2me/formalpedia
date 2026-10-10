-- Prove2me | solution 1 for ActuarialValuation.cm1FundingSurplus_zero_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:52:56.338562+00:00
-- url     : https://prove2.me/submissions/c01b0d13-b19b-4898-924c-96b34c4ffe1a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1CARELiability
import Definitions.Def_actuarial_cm1FundingSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary revalue growth : ℕ → ℝ) (n : ℕ)
    (a annuity : ℝ) :
    cm1FundingSurplus salary revalue growth n a annuity 0 =
      - cm1CARELiability salary revalue n a annuity := by
  simp [cm1FundingSurplus, cm1DCFund]
