-- Prove2me | solution 1 for AaronsonAmbainis.aaronson_ambainis_pm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:05:47.981926+00:00
-- url     : https://prove2.me/submissions/d4345278-c5bd-4eb3-8be5-d3be161677d2

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Main
import Theorems.Thm_AaronsonAmbainis_Bridge_explicitBoundPM


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : ExplicitBoundPM :=
  Bridge.explicitBoundPM
end AaronsonAmbainis
