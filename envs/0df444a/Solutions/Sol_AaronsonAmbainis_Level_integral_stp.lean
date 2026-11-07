-- Prove2me | solution 1 for AaronsonAmbainis.Level.integral_stp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:23:06.747187+00:00
-- url     : https://prove2.me/submissions/bf840e19-cb30-4946-baa7-a354cb7ffe01

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Integral
import Theorems.Thm_AaronsonAmbainis_Level_stp_intervalIntegrable

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
namespace AaronsonAmbainis.Level
theorem _root_.solution {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) : ∫ t in a..b, stp c t = b - c := by
  have e1 : ∫ t in a..c, stp c t = 0 := by
    rw [intervalIntegral.integral_congr_Ioo_of_le hac (g := fun _ => (0 : ℝ)),
      intervalIntegral.integral_zero]
    intro t ht
    show stp c t = 0
    unfold stp
    rw [if_neg (not_le.mpr ht.2)]
  have e2 : ∫ t in c..b, stp c t = b - c := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)), integral_one]
    intro t ht
    rw [Set.uIcc_of_le hcb] at ht
    show stp c t = 1
    unfold stp
    rw [if_pos ht.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals (stp_intervalIntegrable c a c)
    (stp_intervalIntegrable c c b), e1, e2, zero_add]
end AaronsonAmbainis.Level
