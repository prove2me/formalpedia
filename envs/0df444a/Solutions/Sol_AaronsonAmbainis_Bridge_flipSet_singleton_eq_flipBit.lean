-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.flipSet_singleton_eq_flipBit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:16:25.016759+00:00
-- url     : https://prove2.me/submissions/4afc88e5-7f72-4fe6-8598-0c23e9033d26

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_singleton_ne
import Theorems.Thm_AaronsonAmbainis_Bridge_flipSet_singleton_self


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (X : Cube (Fin N)) (i : Fin N) :
    flipSet X {i} = flipBit X i := by
  funext k
  by_cases hk : k = i
  · subst hk
    rw [flipSet_singleton_self]
    simp [flipBit]
  · rw [flipSet_singleton_ne X hk]
    simp [flipBit, Function.update_of_ne hk]
end AaronsonAmbainis.Bridge
