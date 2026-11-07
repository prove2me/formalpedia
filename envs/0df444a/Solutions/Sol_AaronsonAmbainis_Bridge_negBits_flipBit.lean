-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.negBits_flipBit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:33.756627+00:00
-- url     : https://prove2.me/submissions/b1dae83d-1606-47fe-90c8-b3ff2cc59b9a

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (X : Fin N → Bool) (i : Fin N) :
    negBits (flipBit X i) = flipBit (negBits X) i := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [negBits, flipBit]
  · simp [negBits, flipBit, Function.update_of_ne hk]
end AaronsonAmbainis.Bridge
