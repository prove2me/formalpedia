-- Prove2me | solution 1 for AaronsonAmbainis.Level.cube_le_iff_mul_sqrt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:08:24.029687+00:00
-- url     : https://prove2.me/submissions/e31d2e81-6df7-4325-baf8-8ee1ca44f8c1

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Median
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
import Definitions.Def_AaronsonAmbainis_Level_Increments

set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Level
theorem _root_.solution {V K L : ℝ} (hV : 0 ≤ V) (hL : 0 ≤ L) :
    V ^ 3 ≤ 36 * K ^ 4 * L ^ 2 ↔ V * Real.sqrt V ≤ 6 * K ^ 2 * L := by
  have ha : 0 ≤ V * Real.sqrt V := mul_nonneg hV (Real.sqrt_nonneg V)
  have hb : 0 ≤ 6 * K ^ 2 * L := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K)) hL
  have e1 : (V * Real.sqrt V) ^ 2 = V ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hV]
    ring
  have e2 : (6 * K ^ 2 * L) ^ 2 = 36 * K ^ 4 * L ^ 2 := by ring
  constructor
  · intro h
    apply le_of_pow_le_pow_left₀ two_ne_zero hb
    rw [e1, e2]
    exact h
  · intro h
    have h2 := pow_le_pow_left₀ ha h 2
    rw [e1, e2] at h2
    exact h2
end AaronsonAmbainis.Level
