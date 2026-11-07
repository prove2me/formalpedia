-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.dict_abs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:48:17.747128+00:00
-- url     : https://prove2.me/submissions/2eac069d-96e2-43a0-8de8-55d35df36d59

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*}
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (j : ι) (x : Cube ι) : |dict j x| ≤ 1 := by
  unfold dict
  split_ifs <;> simp
end AaronsonAmbainis.Bridge
