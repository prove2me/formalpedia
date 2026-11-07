-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.agMatrix_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:07.332197+00:00
-- url     : https://prove2.me/submissions/67451941-4ac8-40ab-884e-92970ac0d1b5

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
import Theorems.Thm_AaronsonAmbainis_DetLow_evalMat_dominant

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (g : Cube ι → Bool) : (agMatrix g).det ≠ 0 := by
  intro h0
  have hne : ((evalAt ((2 : ℝ) ^ Fintype.card ι)).mapMatrix (agMatrix g)).det ≠ 0 :=
    det_ne_zero_of_sum_row_lt_diag (fun x => evalMat_dominant g _ rfl x)
  apply hne
  rw [← RingHom.map_det, h0, map_zero]
end AaronsonAmbainis.DetLow
