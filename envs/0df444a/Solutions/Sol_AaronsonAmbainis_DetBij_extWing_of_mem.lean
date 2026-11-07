-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.extWing_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:31:58.43908+00:00
-- url     : https://prove2.me/submissions/75260949-50cb-4159-961d-972a076462d3

import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Definitions.Def_AaronsonAmbainis_DetBij_Main

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (A : Cube ι → Finset ι) {x : Cube ι}
    (hx : x ∈ zone g) : extWing g A x = A x := by
  unfold extWing
  rw [if_pos hx]
end AaronsonAmbainis.DetBij
