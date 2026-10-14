-- Prove2me | solution 1 for ActuarialValuation.pfAttainedRate_clears
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:49:31.967994+00:00
-- url     : https://prove2.me/submissions/e51acfe8-d98c-498b-9353-3857f264786f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAttainedRate
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (total past payroll : ℝ) (hp : payroll≠0) : pfAttainedRate total past payroll*payroll=total-past := by
  unfold pfAttainedRate
  field_simp [hp]
