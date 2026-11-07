-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.pairMat_mul_agMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:49.647028+00:00
-- url     : https://prove2.me/submissions/69c4463e-911f-45c1-a3ab-42c2182e36a0

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
import Theorems.Thm_AaronsonAmbainis_DetLow_pairMat_apply
import Theorems.Thm_AaronsonAmbainis_DetLow_agMatrix_apply
import Theorems.Thm_AaronsonAmbainis_DetLow_mem_Up


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (g : Cube ι → Bool) (j : ι) (x z : Ones g) :
    (pairMat g j * agMatrix g) x z =
      if x ∈ Up g j then agMon (flipSet x.1 {j}) z.1 else 0 := by
  rw [Matrix.mul_apply]
  by_cases hx : x ∈ Up g j
  · rw [if_pos hx]
    have hx' := mem_Up.mp hx
    rw [Finset.sum_eq_single (⟨flipSet x.1 {j}, hx'.2⟩ : Ones g)]
    · rw [pairMat_apply, agMatrix_apply, if_pos ⟨hx'.1, rfl⟩, one_mul]
    · intro y _ hy
      rw [pairMat_apply, if_neg, zero_mul]
      rintro ⟨-, h2⟩
      exact hy (Subtype.ext h2)
    · intro h
      exact absurd (mem_univ _) h
  · rw [if_neg hx]
    apply Finset.sum_eq_zero
    intro y _
    rw [pairMat_apply, if_neg, zero_mul]
    rintro ⟨h1, h2⟩
    apply hx
    rw [mem_Up]
    refine ⟨h1, ?_⟩
    rw [← h2]
    exact y.2
end AaronsonAmbainis.DetLow
