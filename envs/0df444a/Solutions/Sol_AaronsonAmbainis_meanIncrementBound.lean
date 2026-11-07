-- Prove2me | solution 1 for AaronsonAmbainis.meanIncrementBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:38:20.269256+00:00
-- url     : https://prove2.me/submissions/a4db1527-8f4f-4212-8f86-b13c056936d7

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
import Theorems.Thm_AaronsonAmbainis_thirdMomentInequality
import Theorems.Thm_AaronsonAmbainis_meanIncrement_of_thirdMoment


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : MeanIncrementBound :=
  meanIncrement_of_thirdMoment thirdMomentInequality
end AaronsonAmbainis
