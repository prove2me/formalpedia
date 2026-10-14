-- Prove2me | solution 1 for ActuarialValuation.pen9TUC_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:15:39.154187+00:00
-- url     : https://prove2.me/submissions/fc7c61de-aa8a-44b5-9f0f-9835ba728bc4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_pen9TUC
import Definitions.Def_actuarial_pen9TUCNormalCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a current f : ℝ) (n : ℕ) : pen9TUC a current f (n+1) = pen9TUC a current f n + pen9TUCNormalCost a current f := by
  simp only [pen9TUC, pen9TUCNormalCost, Nat.cast_add, Nat.cast_one]
  ring
