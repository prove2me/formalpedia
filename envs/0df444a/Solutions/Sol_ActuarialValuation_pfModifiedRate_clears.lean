-- Prove2me | solution 1 for ActuarialValuation.pfModifiedRate_clears
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:34:30.453952+00:00
-- url     : https://prove2.me/submissions/63ab081f-9ae6-45ff-a1b6-ee6043c09000

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfModifiedRate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (normal deficit annuity : ℝ) (ha : annuity≠0) : (pfModifiedRate normal deficit annuity-normal)*annuity=deficit := by
  unfold pfModifiedRate pfAmortisation
  field_simp [ha] <;> ring
