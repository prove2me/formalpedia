-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.sum_agExp_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:30:29.316245+00:00
-- url     : https://prove2.me/submissions/6fbe62de-799c-4959-ba25-feba7c1bb9a1

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Theorems.Thm_AaronsonAmbainis_DetBij_agExp_apply


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (g : Cube ι → Bool) (σ : Equiv.Perm (Ones g)) (j : ι) :
    (∑ x : Ones g, agExp (σ x).1 x.1) j
      = (univ.filter fun x : Ones g => (σ x).1 j = x.1 j).card := by
  rw [Finsupp.finsetSum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [agExp_apply]
end AaronsonAmbainis.DetBij
