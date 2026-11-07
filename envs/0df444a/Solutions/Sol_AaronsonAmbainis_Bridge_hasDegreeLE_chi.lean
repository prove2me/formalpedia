-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_chi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:37:55.880412+00:00
-- url     : https://prove2.me/submissions/5ae8041d-ba02-49bc-b975-ebc59277d9d0

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_chi_iff


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (S : Finset ι) : HasDegreeLE (chi S) S.card :=
  (hasDegreeLE_chi_iff S S.card).mpr le_rfl
end AaronsonAmbainis.Bridge
