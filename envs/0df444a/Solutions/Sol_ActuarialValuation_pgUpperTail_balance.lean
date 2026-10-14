-- Prove2me | solution 1 for ActuarialValuation.pgUpperTail_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:57:06.760859+00:00
-- url     : https://prove2.me/submissions/5ba43ac8-b633-4c3b-a650-999517fde160

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgAggregateCDF
import Definitions.Def_actuarial_pgUpperTail
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p f : ℕ → ℝ) (m k : ℕ) :
    pgUpperTail p f m k + pgAggregateCDF p f m k = 1 := by
  unfold pgUpperTail
  ring
