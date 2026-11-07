-- Prove2me | solution 1 for AaronsonAmbainis.Level.abs_sub_le_of_lev_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:38:43.079955+00:00
-- url     : https://prove2.me/submissions/cd3941b0-e227-434f-bfcd-72f40d97f09a

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Level_Rows

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
namespace AaronsonAmbainis.Level
theorem _root_.solution {ι : Type*} {f : Cube ι → ℝ} {t : ℝ} {x y : Cube ι}
    (h : lev f t y ≠ lev f t x) : |f x - t| ≤ |f x - f y| := by
  unfold lev at h
  by_cases h1 : t < f x <;> by_cases h2 : t < f y
  · simp [h1, h2] at h
  · rw [abs_of_pos (sub_pos.mpr h1)]
    exact le_trans (by linarith) (le_abs_self _)
  · rw [abs_sub_comm (f x) t, abs_sub_comm (f x) (f y), abs_of_nonneg (by linarith)]
    exact le_trans (by linarith) (le_abs_self _)
  · simp [h1, h2] at h
end AaronsonAmbainis.Level
