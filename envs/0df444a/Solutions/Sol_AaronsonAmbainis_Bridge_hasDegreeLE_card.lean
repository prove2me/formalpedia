-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:33:26.163237+00:00
-- url     : https://prove2.me/submissions/96aa96f9-7db4-4268-800c-dac657fdc65e

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Theorems.Thm_AaronsonAmbainis_Bridge_fourier_inversion

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (f : Cube ι → ℝ) : HasDegreeLE f (Fintype.card ι) :=
  ⟨fourier f, fun S hS => absurd (Finset.card_le_univ S) (not_le.mpr hS),
    fun x => (fourier_inversion f x).symm⟩
end AaronsonAmbainis.Bridge
