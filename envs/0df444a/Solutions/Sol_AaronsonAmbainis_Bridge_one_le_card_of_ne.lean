-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.one_le_card_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:28:53.770011+00:00
-- url     : https://prove2.me/submissions/e43f727f-08de-468c-8592-221283b20668

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Theorems.Thm_AaronsonAmbainis_Bridge_nonempty_of_ne

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {g : Cube ι → Bool} {x y : Cube ι} (h : g x ≠ g y) :
    1 ≤ Fintype.card ι := by
  have : Nonempty ι := nonempty_of_ne h
  exact Fintype.card_pos
end AaronsonAmbainis.Bridge
