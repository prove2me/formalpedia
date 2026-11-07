-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.rowBound_of_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:53:48.989515+00:00
-- url     : https://prove2.me/submissions/b6e70862-0edf-495b-bf5f-bed2594b3720

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_comp_equiv
import Theorems.Thm_AaronsonAmbainis_Bridge_rowBound_concl_transport

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (h : RowBoundFin) : RowBound := by
  intro ι _ _ d f hf hdeg
  refine rowBound_concl_transport (Fintype.equivFin ι) f _ ?_
  exact h (Fintype.card ι) d (fun y => f (fun i => y (Fintype.equivFin ι i)))
    (fun y => hf _) (hasDegreeLE_comp_equiv (Fintype.equivFin ι) hdeg)
end AaronsonAmbainis.Bridge
