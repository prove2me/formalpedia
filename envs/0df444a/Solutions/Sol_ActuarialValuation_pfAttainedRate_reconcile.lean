-- Prove2me | solution 1 for ActuarialValuation.pfAttainedRate_reconcile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:52:36.617353+00:00
-- url     : https://prove2.me/submissions/49e8a211-24fb-4ff2-94be-f3ae641d4ace

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAttainedRate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (total past payroll : ℝ) (hp : payroll≠0) : past+pfAttainedRate total past payroll*payroll=total := by
  unfold pfAttainedRate
  field_simp [hp]
  ring
