-- Prove2me | solution 1 for AaronsonAmbainis.aaronson_ambainis_of_fbsDegreeBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:07:39.911379+00:00
-- url     : https://prove2.me/submissions/973698d4-d1b9-46fb-a550-2ab75b08350e

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Main
import Theorems.Thm_AaronsonAmbainis_Bridge_explicitBoundImproved_of_fbsDegreeBound


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : FbsDegreeBound → ExplicitBoundImproved :=
  Bridge.explicitBoundImproved_of_fbsDegreeBound
end AaronsonAmbainis
