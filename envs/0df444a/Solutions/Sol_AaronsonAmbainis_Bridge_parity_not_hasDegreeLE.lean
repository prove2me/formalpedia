-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.parity_not_hasDegreeLE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:38:14.934008+00:00
-- url     : https://prove2.me/submissions/271d8f42-305f-4927-b6a2-dc1f06369646

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_chi_iff

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {d : ℕ} (hd : d < Fintype.card ι) :
    ¬ HasDegreeLE (chi (univ : Finset ι)) d := by
  rw [hasDegreeLE_chi_iff, Finset.card_univ]
  exact not_le.mpr hd
end AaronsonAmbainis.Bridge
