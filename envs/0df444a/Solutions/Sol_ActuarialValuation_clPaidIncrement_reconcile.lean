-- Prove2me | solution 1 for ActuarialValuation.clPaidIncrement_reconcile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:16:30.97407+00:00
-- url     : https://prove2.me/submissions/42511020-3056-41ce-9a3c-4956dd3c98d4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clPaidIncrement
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℕ → ℝ) (i j : ℕ) : p i j + clPaidIncrement p i j = p i (j+1) := by
  unfold clPaidIncrement
  ring
