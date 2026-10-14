-- Prove2me | solution 1 for ActuarialValuation.pen9Service_salary_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:24:16.936404+00:00
-- url     : https://prove2.me/submissions/1b702f69-2f03-45ee-a76c-6888923ccb81

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9PUC
import Definitions.Def_actuarial_pen9PUCNormalCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a old projected f : ℝ) (n : ℕ) : pen9PUC a projected f (n+1) - pen9PUC a old f n = pen9PUCNormalCost a projected f + a*(n:ℝ)*(projected-old)*f := by
  simp only [pen9PUC, pen9PUCNormalCost, Nat.cast_add, Nat.cast_one]
  ring
