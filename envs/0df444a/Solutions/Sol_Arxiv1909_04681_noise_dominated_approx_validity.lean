-- Prove2me | solution 1 for Arxiv1909_04681.noise_dominated_approx_validity
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:34:42.982991+00:00
-- url     : https://prove2.me/submissions/6c6dce7a-fa00-4eea-ab26-7ef75081003e

import Mathlib
import Definitions.Def_Arxiv1909_04681_Basic

open MeasureTheory Filter Topology

open Arxiv1909_04681 in
theorem solution :
    (∀ S : ℝ, 0 < S → S < Real.sqrt (2 / Real.pi) → ∀ x : ℝ, 0 ≤ noiseApprox S x) ∧
    (∀ S : ℝ, Real.sqrt (2 / Real.pi) < S → ∃ x : ℝ, noiseApprox S x < 0) := by
  have hπ := Real.pi_pos
  have hq : 0 < Real.sqrt (2 / Real.pi) := Real.sqrt_pos.2 (by positivity)
  have h8 : Real.sqrt (8 * Real.pi) = 2 * Real.pi * Real.sqrt (2 / Real.pi) := by
    rw [show 8 * Real.pi = (2 * Real.pi) ^ 2 * (2 / Real.pi) by field_simp; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  refine ⟨fun S hS hSl x => ?_, fun S hS => ⟨Real.pi, ?_⟩⟩
  · unfold noiseApprox
    rw [h8]
    have hc := Real.neg_one_le_cos x
    have hk : S / (2 * Real.pi * Real.sqrt (2 / Real.pi)) ≤ 1 / (2 * Real.pi) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have hk0 : 0 ≤ S / (2 * Real.pi * Real.sqrt (2 / Real.pi)) := by positivity
    nlinarith
  · unfold noiseApprox
    rw [h8, Real.cos_pi]
    have hk : 1 / (2 * Real.pi) < S / (2 * Real.pi * Real.sqrt (2 / Real.pi)) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
