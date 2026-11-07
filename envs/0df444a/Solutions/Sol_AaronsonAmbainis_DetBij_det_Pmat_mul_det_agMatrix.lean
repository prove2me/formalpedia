-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.det_Pmat_mul_det_agMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:38:34.343432+00:00
-- url     : https://prove2.me/submissions/aaf5f0ce-46de-4d53-b7b0-f561e6a596f9

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Theorems.Thm_AaronsonAmbainis_DetBij_Pmat_mul_agMatrix


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (A : Cube ι → Finset ι)
    (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    (Pmat g A).det * (agMatrix g).det = (Umat g A).det * (Qmat g A).det := by
  rw [← Matrix.det_mul, ← Matrix.det_mul, Pmat_mul_agMatrix g A hA]
end AaronsonAmbainis.DetBij
