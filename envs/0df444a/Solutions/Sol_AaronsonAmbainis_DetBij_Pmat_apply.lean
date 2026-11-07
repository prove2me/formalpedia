-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.Pmat_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:27:16.789029+00:00
-- url     : https://prove2.me/submissions/0bfa5d7f-df41-4860-8583-6f6d59d7cd7a

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
import Definitions.Def_AaronsonAmbainis_DetBij_Identity

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (A : Cube ι → Finset ι) (x w : Ones g) :
    Pmat g A x w
      = if diffSet x.1 w.1 ⊆ A x.1 then ∏ i ∈ diffSet x.1 w.1, -(X i) else 0 := rfl
end AaronsonAmbainis.DetBij
