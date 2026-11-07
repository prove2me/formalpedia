-- Prove2me | solution 1 for AaronsonAmbainis.thirdMomentInequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:34:08.737234+00:00
-- url     : https://prove2.me/submissions/a5fd4e42-fbf4-4516-b13c-be415a4104b4

import Definitions.Def_AaronsonAmbainis_DetTheorem
import Definitions.Def_AaronsonAmbainis_TwoSided_Main
import Definitions.Def_AaronsonAmbainis_Level_Main
import Definitions.Def_AaronsonAmbainis_Average_Main
import Definitions.Def_AaronsonAmbainis_Row_Main
import Definitions.Def_AaronsonAmbainis_Row_DisjointBlocks
import Definitions.Def_AaronsonAmbainis_Pack_Main
import Definitions.Def_AaronsonAmbainis_Dual_Main
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Chain
import Theorems.Thm_AaronsonAmbainis_integratedAllPairsInequality
import Theorems.Thm_AaronsonAmbainis_thirdMoment_of_integratedAllPairs


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : ThirdMomentInequality :=
  thirdMoment_of_integratedAllPairs integratedAllPairsInequality
end AaronsonAmbainis
