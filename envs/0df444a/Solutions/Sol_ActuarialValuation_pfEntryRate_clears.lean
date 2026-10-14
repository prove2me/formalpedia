-- Prove2me | solution 1 for ActuarialValuation.pfEntryRate_clears
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:29:27.127415+00:00
-- url     : https://prove2.me/submissions/5de20869-ecb6-4611-abe6-1049b4e58cd1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfEntryRate
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (benefit payroll : ℝ) (hp : payroll≠0) : pfEntryRate benefit payroll*payroll=benefit := by
  unfold pfEntryRate
  field_simp [hp]
