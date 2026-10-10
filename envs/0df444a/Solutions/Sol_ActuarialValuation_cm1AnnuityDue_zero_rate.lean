-- Prove2me | solution 1 for ActuarialValuation.cm1AnnuityDue_zero_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:14:45.421899+00:00
-- url     : https://prove2.me/submissions/52dd596d-3cd4-487d-8cfa-2050c9c7a59e

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1AnnuityDue
import Definitions.Def_actuarial_cm1Discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (n : ℕ) : cm1AnnuityDue 0 n = n := by
  simp [cm1AnnuityDue, cm1Discount, cm1Accum]
