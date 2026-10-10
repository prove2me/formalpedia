-- Prove2me | solution 1 for ActuarialValuation.dbCappedPCLS_le_allowance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:10:38.096193+00:00
-- url     : https://prove2.me/submissions/ac6b649a-788d-42c4-9bb1-bdadf47f7c90

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbCappedPCLS

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g f A : ℝ) :
  dbCappedPCLS g f A ≤ A := by
  unfold dbCappedPCLS
  exact min_le_right _ _
