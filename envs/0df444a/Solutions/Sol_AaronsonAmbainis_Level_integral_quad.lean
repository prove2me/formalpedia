-- Prove2me | solution 1 for AaronsonAmbainis.Level.integral_quad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:18:43.47265+00:00
-- url     : https://prove2.me/submissions/720dba56-7a90-47bf-9587-914502495984

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Integral

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
namespace AaronsonAmbainis.Level
theorem _root_.solution (v u : ℝ) : ∫ t in v..u, (u - t) * (t - v) = (u - v) ^ 3 / 6 := by
  have hd : ∀ t ∈ Set.uIcc v u, HasDerivAt
      (fun t : ℝ => -1 / 3 * t ^ 3 + (u + v) / 2 * t ^ 2 - u * v * t) ((u - t) * (t - v)) t := by
    intro t _
    have h3 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * t ^ 2) t := by
      simpa using hasDerivAt_pow 3 t
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h1 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id' t
    have h : HasDerivAt (fun t : ℝ => -1 / 3 * t ^ 3 + (u + v) / 2 * t ^ 2 - u * v * t)
        (-1 / 3 * (3 * t ^ 2) + (u + v) / 2 * (2 * t) - u * v * 1) t :=
      ((h3.const_mul (-1 / 3)).add (h2.const_mul ((u + v) / 2))).sub (h1.const_mul (u * v))
    convert h using 1
    ring
  have hc : Continuous fun t : ℝ => (u - t) * (t - v) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  ring
end AaronsonAmbainis.Level
