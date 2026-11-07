-- Prove2me | solution 1 for AaronsonAmbainis.Level.ind_eq_stp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:18:33.802193+00:00
-- url     : https://prove2.me/submissions/ce4db729-692c-4e59-a3f8-212d4fbf9f23

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Integral

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
namespace AaronsonAmbainis.Level
theorem _root_.solution (p q t : ℝ) :
    (if p ≤ t ∧ t < q then (1 : ℝ) else 0) = stp p t - stp (max p q) t := by
  unfold stp
  by_cases h1 : p ≤ t
  · by_cases h2 : t < q
    · have h3 : ¬ max p q ≤ t := fun h => absurd ((le_max_right p q).trans h) (not_le.mpr h2)
      rw [if_pos ⟨h1, h2⟩, if_pos h1, if_neg h3, sub_zero]
    · rw [if_neg (fun h => h2 h.2), if_pos h1, if_pos (max_le h1 (not_lt.mp h2)), sub_self]
  · rw [if_neg (fun h => h1 h.1), if_neg h1,
      if_neg (fun h => h1 ((le_max_left p q).trans h)), sub_self]
end AaronsonAmbainis.Level
