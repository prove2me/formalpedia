-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.hasDegreeLE_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:00:23.792215+00:00
-- url     : https://prove2.me/submissions/9ed65426-3b21-469b-b8e0-f4c30cfa2306

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_mono
import Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_zero_iff


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (a : ℝ) (d : ℕ) : HasDegreeLE (fun _ : Cube ι => a) d :=
  hasDegreeLE_mono (hasDegreeLE_zero_iff.mpr ⟨a, fun _ => rfl⟩) (Nat.zero_le d)
end AaronsonAmbainis.Bridge
