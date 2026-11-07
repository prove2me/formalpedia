-- Prove2me | solution 1 for AaronsonAmbainis.antipodalInequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:54.259104+00:00
-- url     : https://prove2.me/submissions/d4143aad-ea83-4640-aae8-64aad454254b

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
import Theorems.Thm_AaronsonAmbainis_antipodal_of_det
import Theorems.Thm_AaronsonAmbainis_detInequality


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : AntipodalInequality := antipodal_of_det detInequality
end AaronsonAmbainis
