-- Prove2me | solution 1 for AaronsonAmbainis.Dual.packingBound_of_rowBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:36:34.533526+00:00
-- url     : https://prove2.me/submissions/e059c0fe-2f19-49b6-ba1c-547f5c8bc57a

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
import Theorems.Thm_AaronsonAmbainis_Dual_packingBound_of_rowBoundPM
import Theorems.Thm_AaronsonAmbainis_Dual_rowBoundPM_of_rowBound

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
namespace AaronsonAmbainis.Dual
theorem _root_.solution : RowBound → PackingBound :=
  fun h => packingBound_of_rowBoundPM (rowBoundPM_of_rowBound h)
end AaronsonAmbainis.Dual
