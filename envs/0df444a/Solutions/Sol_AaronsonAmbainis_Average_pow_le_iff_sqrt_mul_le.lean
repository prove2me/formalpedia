-- Prove2me | solution 1 for AaronsonAmbainis.Average.pow_le_iff_sqrt_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:42:10.494437+00:00
-- url     : https://prove2.me/submissions/3469f942-d95a-4baf-845f-add3c5d3f5d5

import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Definitions.Def_AaronsonAmbainis_Average_Influence

set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Average
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Average
theorem _root_.solution {V L K I : ℝ} (hV : 0 ≤ V) (hL : 0 ≤ L) (hI : 0 ≤ I) :
    3 * V ^ 5 ≤ 3125 * L ^ 2 * K ^ 4 * I ^ 2
      ↔ Real.sqrt 15 * (V ^ 2 * Real.sqrt V) ≤ 125 * L * K ^ 2 * I := by
  have ha : 0 ≤ Real.sqrt 15 * (V ^ 2 * Real.sqrt V) := by positivity
  have hb : 0 ≤ 125 * L * K ^ 2 * I :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) (sq_nonneg K)) hI
  have e1 : (Real.sqrt 15 * (V ^ 2 * Real.sqrt V)) ^ 2 = 15 * V ^ 5 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15), Real.sq_sqrt hV]
    ring
  have e2 : (125 * L * K ^ 2 * I) ^ 2 = 5 * (3125 * L ^ 2 * K ^ 4 * I ^ 2) := by ring
  constructor
  · intro h
    apply le_of_pow_le_pow_left₀ two_ne_zero hb
    rw [e1, e2]
    linarith
  · intro h
    have h2 := pow_le_pow_left₀ ha h 2
    rw [e1, e2] at h2
    linarith
end AaronsonAmbainis.Average
