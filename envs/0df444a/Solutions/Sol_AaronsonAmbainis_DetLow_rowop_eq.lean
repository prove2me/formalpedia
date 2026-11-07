-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.rowop_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:31:54.276741+00:00
-- url     : https://prove2.me/submissions/8f05af9b-d6e4-4bf2-a963-3ced77557020

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
import Theorems.Thm_AaronsonAmbainis_DetLow_agMon_of_eq
import Theorems.Thm_AaronsonAmbainis_DetLow_agMon_of_ne
import Theorems.Thm_AaronsonAmbainis_DetLow_agMatrix_apply
import Theorems.Thm_AaronsonAmbainis_DetLow_pairMat_mul_agMatrix
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_flipSet_singleton
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_self
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_flipSet_singleton
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_singleton_self



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (g : Cube ι → Bool) (j : ι) :
    (1 - (X j : MvPolynomial ι ℤ) • pairMat g j) * agMatrix g
      = Matrix.diagonal (diagVec g j) * redMat g j := by
  apply Matrix.ext
  intro x z
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply,
    pairMat_mul_agMatrix, Matrix.diagonal_mul, smul_eq_mul, agMatrix_apply]
  simp only [diagVec, redMat]
  by_cases hx : x ∈ Up g j
  · by_cases hz : z.1 j = x.1 j
    · rw [if_pos hx, if_pos hx, if_pos ⟨hx, hz⟩, mul_zero, agMon_of_eq x.1 z.1 j hz.symm,
        sub_self]
    · rw [if_pos hx, if_pos hx, if_neg (fun h => hz h.2),
        agMon_of_ne x.1 z.1 j (fun h => hz h.symm)]
      ring
  · rw [if_neg hx, if_neg hx, if_neg (fun h => hx h.1), mul_zero, sub_zero, one_mul]
end AaronsonAmbainis.DetLow
