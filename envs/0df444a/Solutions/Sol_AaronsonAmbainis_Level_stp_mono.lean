-- Prove2me | solution 1 for AaronsonAmbainis.Level.stp_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:18:44.024223+00:00
-- url     : https://prove2.me/submissions/b17f72cb-0bff-41d5-8730-4a601298203f

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Integral

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
namespace AaronsonAmbainis.Level
theorem _root_.solution (c : ℝ) : Monotone (stp c) := by
  intro s t hst
  unfold stp
  by_cases h : c ≤ s
  · rw [if_pos h, if_pos (h.trans hst)]
  · rw [if_neg h]
    split_ifs <;> norm_num
end AaronsonAmbainis.Level
