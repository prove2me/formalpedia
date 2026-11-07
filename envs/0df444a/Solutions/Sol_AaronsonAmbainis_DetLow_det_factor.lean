-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.det_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:14.448876+00:00
-- url     : https://prove2.me/submissions/e9d44424-0336-49f7-817e-e3cbed7d2639

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_RowOps
import Theorems.Thm_AaronsonAmbainis_DetLow_unipotent_mul
import Theorems.Thm_AaronsonAmbainis_DetLow_rowop_eq
import Theorems.Thm_AaronsonAmbainis_DetLow_prod_diagVec

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (g : Cube ι → Bool) (j : ι) :
    ∃ R : MvPolynomial ι ℤ, (agMatrix g).det = (1 - X j ^ 2) ^ (Up g j).card * R := by
  refine ⟨(1 + (X j : MvPolynomial ι ℤ) • pairMat g j).det * (redMat g j).det, ?_⟩
  have h1 := congrArg Matrix.det (unipotent_mul g j)
  have h2 := congrArg Matrix.det (rowop_eq g j)
  rw [Matrix.det_mul, Matrix.det_one] at h1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_diagVec] at h2
  calc (agMatrix g).det
      = (1 + (X j : MvPolynomial ι ℤ) • pairMat g j).det *
          ((1 - (X j : MvPolynomial ι ℤ) • pairMat g j).det * (agMatrix g).det) := by
        rw [← mul_assoc, h1, one_mul]
    _ = (1 - X j ^ 2) ^ (Up g j).card *
          ((1 + (X j : MvPolynomial ι ℤ) • pairMat g j).det * (redMat g j).det) := by
        rw [h2]
        ring
end AaronsonAmbainis.DetLow
