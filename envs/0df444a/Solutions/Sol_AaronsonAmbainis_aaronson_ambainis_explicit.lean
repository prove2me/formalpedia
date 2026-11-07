-- Prove2me | solution 1 for AaronsonAmbainis.aaronson_ambainis_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:04:23.995624+00:00
-- url     : https://prove2.me/submissions/290c7aff-0f7a-4375-813d-283109d83f38

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Main
import Theorems.Thm_AaronsonAmbainis_Bridge_explicitBound


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : ExplicitBound :=
  Bridge.explicitBound
end AaronsonAmbainis
