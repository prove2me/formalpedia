-- Prove2me | solution 1 for ActuarialValuation.ulAdjusted_rate_same
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:01:35.862931+00:00
-- url     : https://prove2.me/submissions/77b79fa5-d077-4a93-b935-9bbfb97e589b

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulAdjustedMortality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (interest mortality : ℝ) (hi : 1+interest ≠ 0) : ulAdjustedMortality interest interest mortality = mortality := by
  change mortality * (1 + interest) / (1 + interest) = mortality
  field_simp [hi] <;> ring
