-- Prove2me | solution 1 for AdDataSharing.Topics.one_lt_tauTilde
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T08:36:47.948955+00:00
-- url     : https://prove2.me/submissions/e0914c18-bc1a-42f3-8478-480cfee55dad

import Mathlib
import Definitions.Def_AdDataSharing_Topics_Model
open AdDataSharing.Topics

theorem solution(P : Params) (hP : P.Standing) : 1 < tauTilde P := by
  obtain ⟨hα0, hα, hw0, hwC, hCM, hM2, hφ0, hφ1, hη, hτ, hσ0, hσ1⟩ := hP
  unfold tauTilde
  have h1 : 0 < 1 + P.η₂ := by linarith
  have hA : 0 < (1 + P.η₂) - P.σ * (1 - P.α) := by nlinarith
  have hfrac : (1 + P.η₂ - P.σ * (1 - P.α)) / (1 + P.η₂) <
      (1 + P.η₂ - P.σ * (1 - P.α)) * P.C / (P.w * (1 + P.η₂)) := by
    rw [div_lt_div_iff₀ h1 (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hwC (mul_pos hA h1)]
  have hsum : (1 + P.η₂ - P.σ * (1 - P.α)) / (1 + P.η₂) + P.σ * (1 - P.α) / (1 + P.η₂) = 1 := by
    field_simp
    ring
  linarith
