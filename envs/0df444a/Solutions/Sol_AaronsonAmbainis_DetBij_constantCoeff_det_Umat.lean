-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.constantCoeff_det_Umat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:30:19.959725+00:00
-- url     : https://prove2.me/submissions/e7493049-4a1d-463c-bd87-8454cc613cff

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    constantCoeff (Umat g A).det = 1 := by
  unfold Umat
  rw [Matrix.det_diagonal, map_prod]
  refine Finset.prod_eq_one fun x _ => ?_
  rw [map_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  simp
end AaronsonAmbainis.DetBij
