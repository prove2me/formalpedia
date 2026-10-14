-- Prove2me | solution 1 for ActuarialValuation.frDueValue_add
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:54:06.161987+00:00
-- url     : https://prove2.me/submissions/4f52029f-8cd5-4ecb-abd5-e189982bc70c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueValue
open ActuarialValuation

theorem solution (a b : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (n m : ℕ) : frDueValue (fun k => a k+b k) discount p q n m = frDueValue a discount p q n m + frDueValue b discount p q n m := by
  simp only [frDueValue, frDueTerm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp [add_mul, mul_add, add_div]

