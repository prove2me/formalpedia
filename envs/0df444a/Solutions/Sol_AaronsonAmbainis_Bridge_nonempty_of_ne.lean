-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.nonempty_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:09:14.951977+00:00
-- url     : https://prove2.me/submissions/0c206863-8f88-4565-8fd3-83f2d2a3745c

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {g : Cube ι → Bool} {x y : Cube ι} (h : g x ≠ g y) : Nonempty ι := by
  by_contra hcon
  have : IsEmpty ι := not_nonempty_iff.mp hcon
  exact h (congrArg g (Subsingleton.elim x y))
end AaronsonAmbainis.Bridge
