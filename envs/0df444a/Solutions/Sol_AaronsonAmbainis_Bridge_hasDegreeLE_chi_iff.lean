-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_chi_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:31:35.870214+00:00
-- url     : https://prove2.me/submissions/0ae3bb9e-bf6f-4e50-a894-b6b80d5ca2ce

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_iff_fourier
import Theorems.Thm_AaronsonAmbainis_Bridge_fourier_chi

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (S : Finset ι) (d : ℕ) : HasDegreeLE (chi S) d ↔ S.card ≤ d := by
  rw [hasDegreeLE_iff_fourier]
  constructor
  · intro h
    by_contra hlt
    have h1 := h S (not_le.mp hlt)
    rw [fourier_chi, if_pos rfl] at h1
    exact one_ne_zero h1
  · intro h T hT
    rw [fourier_chi, if_neg]
    rintro rfl
    exact absurd h (not_le.mpr hT)
end AaronsonAmbainis.Bridge
