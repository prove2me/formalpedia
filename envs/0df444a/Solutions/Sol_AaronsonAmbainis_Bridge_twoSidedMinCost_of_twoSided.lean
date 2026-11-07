-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.twoSidedMinCost_of_twoSided
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:37:37.317464+00:00
-- url     : https://prove2.me/submissions/a6e63da3-7063-4198-8e48-eeee16159f37

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Bridge_Positivity
import Definitions.Def_AaronsonAmbainis_Bridge_PaperInequalities
import Theorems.Thm_AaronsonAmbainis_Bridge_twoSided_iff_printed

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : TwoSidedInequality) : TwoSidedMinCost := by
  intro ι _ _ _ g hnc F hF
  choose lam hrow hval using fun x => (hF x).1
  have h1 := twoSided_iff_printed.mp h ι g hnc lam hrow
  simp only [hval] at h1
  exact h1
end AaronsonAmbainis.Bridge
