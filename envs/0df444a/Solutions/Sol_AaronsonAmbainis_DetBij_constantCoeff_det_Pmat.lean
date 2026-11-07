-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.constantCoeff_det_Pmat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:44.162043+00:00
-- url     : https://prove2.me/submissions/f2a8eddf-bc19-4645-90c3-3fc7faeb31b6

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Theorems.Thm_AaronsonAmbainis_DetBij_constantCoeff_Pmat

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    constantCoeff (Pmat g A).det = 1 := by
  have h1 : (constantCoeff : MvPolynomial ι ℤ →+* ℤ).mapMatrix (Pmat g A) = 1 := by
    refine Matrix.ext fun x w => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
    exact constantCoeff_Pmat g A x w
  rw [RingHom.map_det, h1, Matrix.det_one]
end AaronsonAmbainis.DetBij
