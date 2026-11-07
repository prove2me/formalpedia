-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.card_points
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:26:03.693169+00:00
-- url     : https://prove2.me/submissions/486c0f46-b717-4878-a2db-d030e8ce6230

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
import Theorems.Thm_AaronsonAmbainis_Bridge_card_cube
import Theorems.Thm_AaronsonAmbainis_Level_card_cube
import Theorems.Thm_AaronsonAmbainis_card_cube


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (N : ℕ) : (Fintype.card (Fin N → Bool) : ℝ) = 2 ^ N := by
  have h := card_cube (ι := Fin N)
  rw [Fintype.card_fin] at h
  exact h
end AaronsonAmbainis.Bridge
