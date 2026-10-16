-- Prove2me | solution 1 for AccelVI.MVC.rate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-15T20:05:19.036669+00:00
-- url     : https://prove2.me/submissions/f705cf48-789b-41eb-bba7-774b5eb83c97

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_MVC_Setting
open AccelVI.MVC

theorem solution(lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    0 < rateMVC lam ∧ rateMVC lam < lam := by
  unfold rateMVC AccelVI.AVC.kappa
  have hk : 1 / ((1 + lam) / (1 - lam)) = (1 - lam) / (1 + lam) := by
    rw [one_div_div]
  rw [hk]
  have hpos : 0 < (1 - lam) / (1 + lam) := by apply div_pos <;> linarith
  have hlt : (1 - lam) / (1 + lam) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hs2 : Real.sqrt ((1 - lam) / (1 + lam)) ^ 2 = (1 - lam) / (1 + lam) := Real.sq_sqrt hpos.le
  have hs0 : 0 < Real.sqrt ((1 - lam) / (1 + lam)) := Real.sqrt_pos.2 hpos
  have hs1 : Real.sqrt ((1 - lam) / (1 + lam)) < 1 := by
    rw [Real.sqrt_lt' one_pos]; linarith
  generalize Real.sqrt ((1 - lam) / (1 + lam)) = s at *
  have hs2' : s ^ 2 * (1 + lam) = 1 - lam := by rw [hs2]; field_simp
  constructor
  · apply div_pos <;> linarith
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith [mul_pos (mul_pos hs0 (sub_pos.2 hs1)) (by linarith : (0:ℝ) < 1 + lam)]
