-- Prove2me | solution 1 for ActuarialValuation.cm1DCFund_zero_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:37:38.172201+00:00
-- url     : https://prove2.me/submissions/eeda862b-dea0-41a2-b35f-1b27e7d438aa

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1DCFund

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary growth : ℕ → ℝ) (n : ℕ) : cm1DCFund salary growth n 0 = 0 := by
  simp [cm1DCFund]
