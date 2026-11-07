-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.card_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:47:45.138293+00:00
-- url     : https://prove2.me/submissions/346c9fe1-af17-489b-af93-8448587d9145

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution : (Fintype.card (Cube ι) : ℝ) = 2 ^ Fintype.card ι := by
  show (Fintype.card (ι → Bool) : ℝ) = 2 ^ Fintype.card ι
  rw [Fintype.card_fun, Fintype.card_bool]
  norm_num
end AaronsonAmbainis.Bridge
