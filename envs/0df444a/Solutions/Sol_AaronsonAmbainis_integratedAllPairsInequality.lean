-- Prove2me | solution 1 for AaronsonAmbainis.integratedAllPairsInequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:31:13.474461+00:00
-- url     : https://prove2.me/submissions/2aaadd3d-17e3-41ec-9cfe-a11227c9dbbf

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
import Theorems.Thm_AaronsonAmbainis_integratedAllPairs_of_allPairs


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : IntegratedAllPairsInequality :=
  integratedAllPairs_of_allPairs allPairsInequality
end AaronsonAmbainis
