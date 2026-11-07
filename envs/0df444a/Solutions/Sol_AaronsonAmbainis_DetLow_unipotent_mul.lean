-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.unipotent_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:12.710806+00:00
-- url     : https://prove2.me/submissions/66e28e16-d8a2-4403-9f12-6ae1ed87ce61

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
import Theorems.Thm_AaronsonAmbainis_DetLow_pairMat_mul_pairMat

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (g : Cube ι → Bool) (j : ι) :
    (1 + (X j : MvPolynomial ι ℤ) • pairMat g j) * (1 - (X j : MvPolynomial ι ℤ) • pairMat g j)
      = 1 := by
  have h : ((X j : MvPolynomial ι ℤ) • pairMat g j) * ((X j : MvPolynomial ι ℤ) • pairMat g j)
      = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, pairMat_mul_pairMat, smul_zero, smul_zero]
  rw [mul_sub, mul_one, add_mul, one_mul, h, add_zero, add_sub_cancel_right]
end AaronsonAmbainis.DetLow
