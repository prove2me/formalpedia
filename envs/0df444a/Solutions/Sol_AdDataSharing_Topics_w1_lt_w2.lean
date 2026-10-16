-- Prove2me | solution 1 for AdDataSharing.Topics.w1_lt_w2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-15T20:03:41.990955+00:00
-- url     : https://prove2.me/submissions/29da6d40-32db-499b-8ab2-c28b5f9bb4a0

import Mathlib
import Definitions.Def_AdDataSharing_Topics_Model
open AdDataSharing.Topics

theorem solution(P : Params) (hP : P.Standing) : w₁ P < w₂ P := by
  obtain ⟨hα0, hα, hw0, hwC, hCM, hM2, hφ0, hφ1, hη, hτ, hσ0, hσ1⟩ := hP
  unfold w₁ w₂
  have hden : 0 < P.τ * (1 + P.η₂) - P.σ * (1 - P.α) := by nlinarith
  apply div_lt_div_of_pos_right _ hden
  have h1 : 0 < 1 + P.η₂ - P.σ := by linarith
  nlinarith [mul_lt_mul_of_pos_left hCM h1]
