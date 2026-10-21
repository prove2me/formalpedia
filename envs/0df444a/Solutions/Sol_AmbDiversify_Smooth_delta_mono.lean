-- Prove2me | solution 1 for AmbDiversify.Smooth.delta_mono
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:00:56.781658+00:00
-- url     : https://prove2.me/submissions/95b29c43-9d4e-4b1f-b736-5ac1e7e76461

import Mathlib
import Definitions.Def_AmbDiversify_Smooth_Model

set_option autoImplicit false
open AmbDiversify.Smooth

theorem vd_eq (u : ℝ → ℝ) (W0 L p : ℝ) :
    VD_risk u W0 L p = p * (1 - p) * (2 * u (W0 - L / 2) - u (W0 - L) - u W0) := by
  unfold VD_risk EU_D EU_ND
  ring

theorem solution (u : ℝ → ℝ) (W0 L p1 p2 : ℝ) (hp2 : 1 / 2 ≤ p2) (h21 : p2 ≤ p1) (hp1 : p1 ≤ 1) :
    (ConcaveOn ℝ Set.univ u → VD_risk u W0 L p1 ≤ VD_risk u W0 L p2) ∧
    (p2 < p1 → 0 < L → StrictConcaveOn ℝ Set.univ u →
      VD_risk u W0 L p1 < VD_risk u W0 L p2) := by
  have hmid : (W0 - L / 2) = (1 / 2 : ℝ) • (W0 - L) + (1 / 2 : ℝ) • W0 := by
    simp only [smul_eq_mul]; ring
  have key : ∀ q : ℝ, VD_risk u W0 L q = q * (1 - q) * (2 * u (W0 - L / 2) - u (W0 - L) - u W0) :=
    fun q => vd_eq u W0 L q
  have hdiff : p2 * (1 - p2) - p1 * (1 - p1) = (p1 - p2) * (p1 + p2 - 1) := by ring
  constructor
  · intro hc
    have hG : 0 ≤ 2 * u (W0 - L / 2) - u (W0 - L) - u W0 := by
      have := @hc.2 (W0 - L) (Set.mem_univ _) W0 (Set.mem_univ _) (1 / 2) (1 / 2)
        (by norm_num) (by norm_num) (by norm_num)
      rw [← hmid] at this
      simp only [smul_eq_mul] at this
      linarith
    rw [key, key]
    have : 0 ≤ (p1 - p2) * (p1 + p2 - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith [mul_nonneg this hG]
  · intro hlt hL hs
    have hG : 0 < 2 * u (W0 - L / 2) - u (W0 - L) - u W0 := by
      have := @hs.2 (W0 - L) (Set.mem_univ _) W0 (Set.mem_univ _) (by intro h; linarith) (1 / 2) (1 / 2)
        (by norm_num) (by norm_num) (by norm_num)
      rw [← hmid] at this
      simp only [smul_eq_mul] at this
      linarith
    rw [key, key]
    have : 0 < (p1 - p2) * (p1 + p2 - 1) := mul_pos (by linarith) (by linarith)
    nlinarith [mul_pos this hG]
