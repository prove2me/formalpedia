-- Prove2me | solution 1 for AdBlockers.Allow.moreover_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:36:24.82015+00:00
-- url     : https://prove2.me/submissions/00415f59-c08a-49a2-8bd7-b668f3008834

import Mathlib
set_option autoImplicit false

theorem solution (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β)
    (hγ : 0 < γ) :
    ((lam + μ) ^ 2 / (2 * (β * lam + γ * μ)) ≤ lam / (2 * β) ↔ 2 + μ / lam ≤ γ / β) ∧
      ((lam + μ) / 2 ≤ lam / (2 * β) ↔ β ≤ lam / (lam + μ)) := by
  constructor
  · have h : 2 + μ / lam = (2 * lam + μ) / lam := by field_simp
    rw [h, div_le_div_iff₀ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    constructor <;> intro h <;> nlinarith [mul_pos hlam hβ]
  · rw [div_le_div_iff₀ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith [mul_pos hlam hβ]
