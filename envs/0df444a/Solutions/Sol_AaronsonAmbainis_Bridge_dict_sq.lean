-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.dict_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:47:54.645251+00:00
-- url     : https://prove2.me/submissions/d3d61055-cb7a-41d3-a1eb-fae2308ee156

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*}
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (j : ι) (x : Cube ι) : dict j x ^ 2 = 1 := by
  unfold dict
  split_ifs <;> norm_num
end AaronsonAmbainis.Bridge
