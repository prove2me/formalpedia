-- Prove2me | solution 1 for AaronsonAmbainis.rowBoundPM_of_packing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:14:45.566098+00:00
-- url     : https://prove2.me/submissions/3137d9a6-2020-4005-9339-a1d0cd3317f5

import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_Row
import Theorems.Thm_AaronsonAmbainis_Dual_rowBoundPM_of_packing_of_cover
import Theorems.Thm_AaronsonAmbainis_coverDuality


set_option autoImplicit true
open AaronsonAmbainis
namespace AaronsonAmbainis
theorem _root_.solution : PackingBound → RowBoundPM :=
  fun hPB => Dual.rowBoundPM_of_packing_of_cover hPB coverDuality
end AaronsonAmbainis
