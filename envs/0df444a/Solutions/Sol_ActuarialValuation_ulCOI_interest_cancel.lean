-- Prove2me | solution 1 for ActuarialValuation.ulCOI_interest_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:22:26.234399+00:00
-- url     : https://prove2.me/submissions/f532fab4-3bb6-4fb4-b296-713bf8ece93c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulCOIAtStart

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (interest mortality risk : ℝ) (hi : 1+interest ≠ 0) : ulCOIAtStart interest mortality risk * (1+interest) = mortality*risk := by
  change (mortality * risk / (1 + interest)) * (1 + interest) = mortality * risk
  exact (eq_div_iff hi).mp rfl
