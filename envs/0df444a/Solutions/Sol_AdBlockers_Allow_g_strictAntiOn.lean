-- Prove2me | solution 1 for AdBlockers.Allow.g_strictAntiOn
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:31:26.828634+00:00
-- url     : https://prove2.me/submissions/85a0458b-a51e-4881-a992-97f965f86822

import Mathlib
set_option autoImplicit false

theorem solution (lam μ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) :
    StrictAntiOn (fun x : ℝ => (lam + μ * x) / (3 * lam + 4 * μ * x) ^ 2) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  simp only
  have h1 : 0 < (3 * lam + 4 * μ * y) ^ 2 := by
    have : 0 ≤ y := hy
    positivity
  have h2 : 0 < (3 * lam + 4 * μ * x) ^ 2 := by positivity
  rw [div_lt_div_iff₀ h1 h2]
  have hd0 : 0 < μ * (y - x) := mul_pos hμ (by linarith)
  have hp0 : 0 ≤ μ * x := by positivity
  have key : (lam + μ * x) * (3 * lam + 4 * μ * y) ^ 2 - (lam + μ * y) * (3 * lam + 4 * μ * x) ^ 2
      = (μ * (y - x)) * ((3 * lam + 4 * (μ * x)) * (5 * lam + 4 * (μ * x))
          + 16 * (lam + μ * x) * (μ * (y - x))) := by ring
  have pos : 0 < (μ * (y - x)) * ((3 * lam + 4 * (μ * x)) * (5 * lam + 4 * (μ * x))
          + 16 * (lam + μ * x) * (μ * (y - x))) := by positivity
  linarith
