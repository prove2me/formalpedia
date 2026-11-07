-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_iff_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:28:39.051748+00:00
-- url     : https://prove2.me/submissions/98a8101a-aac2-4057-9b9f-7f228f63c8f7

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Theorems.Thm_AaronsonAmbainis_Bridge_fourier_inversion
import Theorems.Thm_AaronsonAmbainis_Bridge_fourier_unique

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔ ∀ S : Finset ι, d < S.card → fourier f S = 0 := by
  constructor
  · rintro ⟨c, hc, hf⟩ S hS
    rw [← fourier_unique hf S]
    exact hc S hS
  · intro h
    exact ⟨fourier f, h, fun x => (fourier_inversion f x).symm⟩
end AaronsonAmbainis.Bridge
