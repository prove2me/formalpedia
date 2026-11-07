-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.agExp_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:23:12.88544+00:00
-- url     : https://prove2.me/submissions/b9579868-aaed-4f98-8486-dad80184d419

import Definitions.Def_AaronsonAmbainis_DetDefs
import Definitions.Def_AaronsonAmbainis_DetBij_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (x z : Cube ι) (j : ι) : agExp x z j = if x j = z j then 1 else 0 := by
  rw [agExp, Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · split_ifs <;> simp
  · intro i _ hij
    split_ifs
    · simp [hij]
    · simp
  · intro h
    exact absurd (Finset.mem_univ j) h
end AaronsonAmbainis.DetBij
