-- Prove2me | solution 1 for AaronsonAmbainis.mainTheorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:46:19.49729+00:00
-- url     : https://prove2.me/submissions/6a131a08-b9db-4fe0-942f-465edb3dfd08

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
import Theorems.Thm_AaronsonAmbainis_rowBoundPM
import Theorems.Thm_AaronsonAmbainis_mainTheorem_of_influence


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : MainTheorem :=
  mainTheorem_of_influence influenceBound sensitivityBound rowBoundPM
end AaronsonAmbainis
