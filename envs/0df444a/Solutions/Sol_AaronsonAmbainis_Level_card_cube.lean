-- Prove2me | solution 1 for AaronsonAmbainis.Level.card_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:34:30.188059+00:00
-- url     : https://prove2.me/submissions/bf3e783d-f660-46a1-b7c0-f0633307bc21

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution : ((Fintype.card (Cube ι) : ℕ) : ℝ) = 2 ^ Fintype.card ι := by
  have h : Fintype.card (Cube ι) = 2 ^ Fintype.card ι := by
    rw [Fintype.card_fun, Fintype.card_bool]
  rw [h]
  push_cast
  rfl
end AaronsonAmbainis.Level
