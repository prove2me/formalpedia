-- Prove2me | solution 1 for AdaDiscRL.lemma_E_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:45:38.352568+00:00
-- url     : https://prove2.me/submissions/6626d8aa-cd9c-442e-84bf-32491a470edc

import Mathlib
import Definitions.Def_AdaDiscRL_clip

open MeasureTheory ProbabilityTheory Classical

open AdaDiscRL in
theorem solution (H : ℕ) (hH : 1 ≤ H) (g φ μ₁ μ₂ : ℝ) (hμ₂ : 0 ≤ μ₂) (hg : g ≤ φ) (hφ : φ ≤ μ₁ + μ₂) :
    φ ≤ AdaDiscRL.clip μ₁ (g / ((H : ℝ) + 1)) + (1 + 1 / (H : ℝ)) * μ₂ := by
  have hH' : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0:ℝ) < H := by linarith
  have key : (1 + 1 / (H : ℝ)) * μ₂ = μ₂ + μ₂ / H := by ring
  rw [key]
  have hq : 0 ≤ μ₂ / H := div_nonneg hμ₂ hHpos.le
  unfold AdaDiscRL.clip
  by_cases h : g / ((H : ℝ) + 1) ≤ μ₁
  · rw [if_pos h]; linarith
  · rw [if_neg h]
    push_neg at h
    have hH1 : (0:ℝ) < (H:ℝ) + 1 := by linarith
    have ht : g / ((H : ℝ) + 1) * ((H:ℝ) + 1) = g := div_mul_cancel₀ g hH1.ne'
    have h2 : (φ - μ₂) * H < μ₂ := by nlinarith
    have h3 : φ - μ₂ < μ₂ / H := (lt_div_iff₀ hHpos).mpr h2
    linarith
