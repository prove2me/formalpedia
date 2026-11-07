-- Prove2me | solution 1 for AaronsonAmbainis.twoSidedInequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:32:00.759204+00:00
-- url     : https://prove2.me/submissions/7f791151-bfdd-4510-867b-9cda554975e0

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
import Theorems.Thm_AaronsonAmbainis_allPairsInequality
import Theorems.Thm_AaronsonAmbainis_twoSided_of_allPairs


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : TwoSidedInequality := twoSided_of_allPairs allPairsInequality
end AaronsonAmbainis
