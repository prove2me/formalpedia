-- Prove2me | solution 1 for ActuarialValuation.frDueValue_scale
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:33:36.845359+00:00
-- url     : https://prove2.me/submissions/78831426-488f-4e2c-8213-80d2d4539e9b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueValue
open ActuarialValuation

theorem solution(c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (n m : ℕ) (a : ℝ) : frDueValue (fun k => a*c k) discount p q n m = a * frDueValue c discount p q n m := by
  unfold frDueValue frDueTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
