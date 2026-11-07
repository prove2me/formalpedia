-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.infl_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:29:16.033358+00:00
-- url     : https://prove2.me/submissions/12956149-7f20-494c-93b5-cb38fb967922

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Definitions.Def_AaronsonAmbainis_Bridge_PaperInequalities

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (g : Cube ι → Bool) (j : ι) : 0 ≤ infl g j := by
  unfold infl
  positivity
end AaronsonAmbainis.Bridge
