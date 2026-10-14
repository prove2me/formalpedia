-- Prove2me | solution 1 for ActuarialValuation.pfAggregate_no_payroll
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:27:01.726978+00:00
-- url     : https://prove2.me/submissions/5831ade7-f3cc-446a-8b86-b2b05efe1765

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAggregateRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (benefit assets : ℝ) : pfAggregateRate benefit assets 0=0 := by
  unfold pfAggregateRate
  simp
