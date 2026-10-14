-- Prove2me | solution 1 for ActuarialValuation.pen9PUC_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:17:19.451684+00:00
-- url     : https://prove2.me/submissions/3702d4dc-8ded-432e-9dd1-2cbaaca58a22

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_pen9PUC
import Definitions.Def_actuarial_pen9PUCNormalCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a projected f : ℝ) (n : ℕ) : pen9PUC a projected f (n+1) = pen9PUC a projected f n + pen9PUCNormalCost a projected f := by
  simp only [pen9PUC, pen9PUCNormalCost, Nat.cast_add, Nat.cast_one]
  ring
