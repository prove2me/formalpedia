-- Prove2me | solution 1 for AaronsonAmbainis.influenceBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:43:23.808378+00:00
-- url     : https://prove2.me/submissions/c2615e7c-0d2f-4eb9-b5ef-75da4e537cda

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
import Theorems.Thm_AaronsonAmbainis_meanIncrementBound
import Theorems.Thm_AaronsonAmbainis_influence_of_meanIncrement


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : InfluenceBound := influence_of_meanIncrement meanIncrementBound
end AaronsonAmbainis
