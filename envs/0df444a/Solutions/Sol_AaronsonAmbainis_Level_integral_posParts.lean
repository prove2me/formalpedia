-- Prove2me | solution 1 for AaronsonAmbainis.Level.integral_posParts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:20:56.300097+00:00
-- url     : https://prove2.me/submissions/54176349-4673-4eac-be13-fe8990707ef0

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Integral
import Theorems.Thm_AaronsonAmbainis_Level_integral_quad

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
namespace AaronsonAmbainis.Level
theorem _root_.solution {a b u v : ℝ} (hub : u ≤ b) (hav : a ≤ v) :
    ∫ t in a..b, max (u - t) 0 * max (t - v) 0 = max (u - v) 0 ^ 3 / 6 := by
  have hc : Continuous fun t : ℝ => max (u - t) 0 * max (t - v) 0 := by fun_prop
  rcases le_or_gt u v with h | h
  · have h0 : ∀ t : ℝ, max (u - t) 0 * max (t - v) 0 = 0 := by
      intro t
      rcases le_or_gt u t with ht | ht
      · rw [max_eq_right (by linarith : u - t ≤ 0), zero_mul]
      · rw [max_eq_right (by linarith : t - v ≤ 0), mul_zero]
    simp only [h0]
    rw [intervalIntegral.integral_zero, max_eq_right (by linarith : u - v ≤ 0)]
    norm_num
  · have e1 : ∫ t in a..v, max (u - t) 0 * max (t - v) 0 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)),
        intervalIntegral.integral_zero]
      intro t ht
      rw [Set.uIcc_of_le hav] at ht
      show max (u - t) 0 * max (t - v) 0 = 0
      rw [max_eq_right (by linarith [ht.2] : t - v ≤ 0), mul_zero]
    have e2 : ∫ t in v..u, max (u - t) 0 * max (t - v) 0 = (u - v) ^ 3 / 6 := by
      rw [intervalIntegral.integral_congr (g := fun t => (u - t) * (t - v)), integral_quad]
      intro t ht
      rw [Set.uIcc_of_le h.le] at ht
      show max (u - t) 0 * max (t - v) 0 = (u - t) * (t - v)
      rw [max_eq_left (by linarith [ht.2] : 0 ≤ u - t),
        max_eq_left (by linarith [ht.1] : 0 ≤ t - v)]
    have e3 : ∫ t in u..b, max (u - t) 0 * max (t - v) 0 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)),
        intervalIntegral.integral_zero]
      intro t ht
      rw [Set.uIcc_of_le hub] at ht
      show max (u - t) 0 * max (t - v) 0 = 0
      rw [max_eq_right (by linarith [ht.1] : u - t ≤ 0), zero_mul]
    have s1 := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable a v) (hc.intervalIntegrable (μ := MeasureTheory.volume) v b)
    have s2 := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable v u) (hc.intervalIntegrable (μ := MeasureTheory.volume) u b)
    rw [← s1, ← s2, e1, e2, e3, max_eq_left (by linarith : 0 ≤ u - v)]
    ring
end AaronsonAmbainis.Level
