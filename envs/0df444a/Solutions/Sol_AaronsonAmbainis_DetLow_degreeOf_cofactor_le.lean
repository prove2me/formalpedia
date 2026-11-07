-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.degreeOf_cofactor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:17:45.564471+00:00
-- url     : https://prove2.me/submissions/906ba517-12b9-41a3-8ebd-1914a8b584aa

import Definitions.Def_AaronsonAmbainis_DetLow_Unit
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
import Definitions.Def_AaronsonAmbainis_DetLow_Degree
import Definitions.Def_AaronsonAmbainis_DetLow_Count
import Definitions.Def_AaronsonAmbainis_DetLow_Main
import Theorems.Thm_AaronsonAmbainis_DetLow_agMatrix_det_ne_zero
import Theorems.Thm_AaronsonAmbainis_DetLow_card_ones_eq
import Theorems.Thm_AaronsonAmbainis_DetLow_degreeOf_det_le
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_flipSet_singleton
import Theorems.Thm_AaronsonAmbainis_DetLow_flipSet_singleton_self
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_flipSet_singleton
attribute [local simp] AaronsonAmbainis.DetLow.flipSet_singleton_self



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
namespace AaronsonAmbainis.DetLow
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (g : Cube ι → Bool) (j : ι)
    (R : MvPolynomial ι ℤ) (hR : (agMatrix g).det = (1 - X j ^ 2) ^ (Up g j).card * R) :
    degreeOf j R ≤ bdry g j := by
  have hp : (agMatrix g).det ≠ 0 := agMatrix_det_ne_zero g
  have hu0 : ((1 : MvPolynomial ι ℤ) - X j ^ 2) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp at h'
  have hR0 : R ≠ 0 := by
    rintro rfl
    exact hp (by rw [hR, mul_zero])
  have hdeg1 : degreeOf j ((1 : MvPolynomial ι ℤ) - X j ^ 2) = 2 := by
    have h : (1 : MvPolynomial ι ℤ) - X j ^ 2 = -(X j ^ 2) + 1 := by ring
    have hlt : degreeOf j (1 : MvPolynomial ι ℤ) < degreeOf j (-(X j ^ 2 : MvPolynomial ι ℤ)) := by
      rw [degreeOf_neg, degreeOf_X_self_pow, degreeOf_one]
      norm_num
    rw [h, degreeOf_add_eq_of_degreeOf_lt hlt, degreeOf_neg, degreeOf_X_self_pow]
  have h1 := degreeOf_det_le g j
  rw [hR, degreeOf_mul_eq (pow_ne_zero _ hu0) hR0, degreeOf_pow_eq j _ _ hu0, hdeg1,
    card_ones_eq g j] at h1
  omega
end AaronsonAmbainis.DetLow
