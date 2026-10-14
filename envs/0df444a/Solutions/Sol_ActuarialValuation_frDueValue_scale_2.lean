-- Prove2me | solution 2 for ActuarialValuation.frDueValue_scale
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:10:29.406039+00:00
-- url     : https://prove2.me/submissions/93d71bca-ceb5-408f-bbe4-f61404ff159c

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueValue
open ActuarialValuation

theorem solution (c : ℕ → ℝ) (discount : ℝ → ℝ) (p q : ℕ → ℝ) (n m : ℕ) (a : ℝ) : frDueValue (fun k => a*c k) discount p q n m = a * frDueValue c discount p q n m := by
  simp only [frDueValue, frDueTerm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

