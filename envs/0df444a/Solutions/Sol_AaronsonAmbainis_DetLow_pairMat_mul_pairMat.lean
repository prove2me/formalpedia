-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.pairMat_mul_pairMat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:43.375431+00:00
-- url     : https://prove2.me/submissions/ad479ea1-58b0-425a-8b03-3a13ea6d7d03

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
import Theorems.Thm_AaronsonAmbainis_DetLow_pairMat_apply
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_self
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_singleton_self



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (g : Cube ι → Bool) (j : ι) : pairMat g j * pairMat g j = 0 := by
  apply Matrix.ext
  intro x z
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro y _
  rw [pairMat_apply, pairMat_apply]
  by_cases h : x.1 j = true ∧ y.1 = flipSet x.1 {j}
  · have hy : ¬ (y.1 j = true ∧ z.1 = flipSet y.1 {j}) := by
      rintro ⟨hy1, -⟩
      have hf : y.1 j = false := by
        rw [h.2, flipSet_singleton_self, h.1]
        rfl
      rw [hf] at hy1
      exact Bool.false_ne_true hy1
    rw [if_neg hy, mul_zero]
  · rw [if_neg h, zero_mul]
end AaronsonAmbainis.DetLow
