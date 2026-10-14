-- Prove2me | solution 1 for ActuarialValuation.pfAggregateRate_clears
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:21:06.741855+00:00
-- url     : https://prove2.me/submissions/7efbc19e-bab8-4ac7-9194-d5adc74ea256

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAggregateRate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (benefit assets payroll : ℝ) (hp : payroll≠0) : assets+pfAggregateRate benefit assets payroll*payroll=benefit := by
  unfold pfAggregateRate
  field_simp [hp]
  ring
