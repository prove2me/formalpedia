-- Prove2me | solution 1 for AaronsonAmbainis.rowBoundPM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:39:08.544061+00:00
-- url     : https://prove2.me/submissions/2bfca2d0-da86-45ef-8986-dbf8c1573801

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
import Theorems.Thm_AaronsonAmbainis_packingBound
import Theorems.Thm_AaronsonAmbainis_rowBoundPM_of_packing


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : RowBoundPM := rowBoundPM_of_packing packingBound
end AaronsonAmbainis
