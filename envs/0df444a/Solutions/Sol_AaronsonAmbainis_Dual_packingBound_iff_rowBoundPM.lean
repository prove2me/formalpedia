-- Prove2me | solution 1 for AaronsonAmbainis.Dual.packingBound_iff_rowBoundPM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:35:46.228141+00:00
-- url     : https://prove2.me/submissions/4d8b9ac1-ae9e-4292-9ede-a3cbbb26c241

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
import Theorems.Thm_AaronsonAmbainis_Dual_packingBound_of_rowBoundPM
import Theorems.Thm_AaronsonAmbainis_Dual_exists_cover
import Theorems.Thm_AaronsonAmbainis_Dual_rowBoundPM_of_packing_of_cover


set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
namespace AaronsonAmbainis.Dual
theorem _root_.solution : PackingBound ↔ RowBoundPM :=
  ⟨fun h => rowBoundPM_of_packing_of_cover h (fun _ _ _ t K _ _ hp => exists_cover t K hp),
    packingBound_of_rowBoundPM⟩
end AaronsonAmbainis.Dual
