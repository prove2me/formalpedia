-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.mainTheorem_iff_printed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:39:25.3776+00:00
-- url     : https://prove2.me/submissions/ac2139a7-acbd-4f2d-b763-24f38adec13c

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Bridge_PaperTheorems
import Theorems.Thm_AaronsonAmbainis_Bridge_mainTheoremPrinted_of_mainTheorem
import Theorems.Thm_AaronsonAmbainis_Bridge_mainTheorem_of_mainTheoremPrinted

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : MainTheorem ↔ MainTheoremPrinted :=
  ⟨mainTheoremPrinted_of_mainTheorem, mainTheorem_of_mainTheoremPrinted⟩
end AaronsonAmbainis.Bridge
