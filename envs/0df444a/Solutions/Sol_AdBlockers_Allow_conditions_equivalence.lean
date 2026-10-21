-- Prove2me | solution 1 for AdBlockers.Allow.conditions_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:36:23.637996+00:00
-- url     : https://prove2.me/submissions/a7f1320a-f976-4c30-a21d-9090f97dd14c

import Mathlib
set_option autoImplicit false

theorem solution (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) (hβ : 0 < β)
    (hγ : 0 < γ) :
    ((lam + μ) * (3 * lam + 2 * μ) ^ 2 / (2 * (3 * lam + 4 * μ) ^ 2) ≤ lam / (2 * β) ↔
        β ≤ lam * (3 * lam + 4 * μ) ^ 2 / ((lam + μ) * (3 * lam + 2 * μ) ^ 2)) ∧
      ((3 * lam + 2 * μ) ^ 2 * (β * lam + γ * μ) / (2 * (3 * β * lam + 4 * γ * μ) ^ 2) ≤
          lam / (2 * β) ↔
        (lam + μ * (γ / β)) / (3 * lam + 4 * μ * (γ / β)) ^ 2 ≤ lam / (3 * lam + 2 * μ) ^ 2) := by
  have hA : 0 < 3 * lam + 4 * μ := by positivity
  have hB : 0 < 3 * lam + 2 * μ := by positivity
  have hC : 0 < lam + μ := by positivity
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity), le_div_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith [mul_pos hlam hβ]
  · obtain ⟨t, ht, rfl⟩ : ∃ t, 0 < t ∧ γ = t * β := ⟨γ / β, by positivity, by field_simp⟩
    have hD : 0 < 3 * lam + 4 * μ * t := by positivity
    have e1 : (3 * β * lam + 4 * (t * β) * μ) = β * (3 * lam + 4 * μ * t) := by ring
    have e2 : (β * lam + t * β * μ) = β * (lam + μ * t) := by ring
    have e3 : t * β / β = t := by field_simp
    rw [e1, e2, e3, div_le_div_iff₀ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hb2 : 0 < β := hβ
    constructor
    · intro h
      have : β * (β * ((3 * lam + 2 * μ) ^ 2 * (lam + μ * t))) ≤ β * (β * (lam * (3 * lam + 4 * μ * t) ^ 2)) := by
        nlinarith
      have := le_of_mul_le_mul_left this hb2
      have := le_of_mul_le_mul_left this hb2
      nlinarith
    · intro h
      have := mul_le_mul_of_nonneg_left h (le_of_lt (mul_pos hb2 hb2))
      nlinarith
