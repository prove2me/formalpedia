-- Prove2me | solution 1 for AaronsonAmbainis.mainTheoremImproved_of_rowBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:46:20.318687+00:00
-- url     : https://prove2.me/submissions/d38ba6fc-c60f-4b54-ba49-35536430f906

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
import Theorems.Thm_AaronsonAmbainis_influenceBound
import Theorems.Thm_AaronsonAmbainis_sensitivityBound
import Theorems.Thm_AaronsonAmbainis_mainTheoremImproved_of_influence


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : RowBound → MainTheoremImproved :=
  mainTheoremImproved_of_influence influenceBound sensitivityBound
end AaronsonAmbainis
