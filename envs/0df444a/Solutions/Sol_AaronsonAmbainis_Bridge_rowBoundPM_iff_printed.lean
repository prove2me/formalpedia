-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.rowBoundPM_iff_printed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:38:25.797961+00:00
-- url     : https://prove2.me/submissions/a5ca5bbf-a826-4461-8e7c-f5836446d4ac

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Level_Increments
import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Bridge_PaperTheorems
import Theorems.Thm_AaronsonAmbainis_Bridge_rows_iff_printed

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : RowBoundPM ↔ RowBoundPMPrinted :=
  ⟨fun h ι _ _ d f hbd hdeg => (rows_iff_printed f _).mp (h ι d f hbd hdeg),
    fun h ι _ _ d f hbd hdeg => (rows_iff_printed f _).mpr (h ι d f hbd hdeg)⟩
end AaronsonAmbainis.Bridge
