-- Prove2me | solution 1 for AaronsonAmbainis.detInequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:22:25.47406+00:00
-- url     : https://prove2.me/submissions/961d92ae-ff54-4c5f-afa2-82f711fa9f27

import Definitions.Def_AaronsonAmbainis_DetLow_Main
import Definitions.Def_AaronsonAmbainis_DetBij_Main
import Definitions.Def_AaronsonAmbainis_DetTheorem
import Theorems.Thm_AaronsonAmbainis_DetBij_detInequality_of_lowest
import Theorems.Thm_AaronsonAmbainis_DetLow_lowestBound
import Theorems.Thm_AaronsonAmbainis_DetLow_lowestUnit


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : DetInequality :=
  DetBij.detInequality_of_lowest DetLow.lowestUnit DetLow.lowestBound
end AaronsonAmbainis
