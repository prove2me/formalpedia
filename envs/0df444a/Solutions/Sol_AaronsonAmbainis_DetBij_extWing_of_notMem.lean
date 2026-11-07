-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.extWing_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:14.574334+00:00
-- url     : https://prove2.me/submissions/22228552-7bd2-41cf-9299-cf36ce30ca93

import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Definitions.Def_AaronsonAmbainis_DetBij_Main

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (A : Cube ι → Finset ι) {x : Cube ι}
    (hx : x ∉ zone g) : extWing g A x = ∅ := by
  unfold extWing
  rw [if_neg hx]
end AaronsonAmbainis.DetBij
