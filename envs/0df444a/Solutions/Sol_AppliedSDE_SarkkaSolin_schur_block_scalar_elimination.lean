-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.schur_block_scalar_elimination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:55:57.745713+00:00
-- url     : https://prove2.me/submissions/f5a3eb11-c52a-4451-b51c-eaeed89d0565

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (n : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (l : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (u b x : Fin n → ℝ) (w d v : ℝ)
    (hx : x = A (u - w • b))
    (hrow : l x + d * w = v)
    (hS : d - l (A b) ≠ 0) :
    w = (v - l (A u)) / (d - l (A b)) := by
  have hlinear : l x = l (A u) - w * l (A b) := by
    calc
      l x = l (A (u - w • b)) := by rw [hx]
      _ = l (A u) - w * l (A b) := by
        simp [map_sub, map_smul, smul_eq_mul]
  apply (eq_div_iff hS).2
  rw [hlinear] at hrow
  nlinarith
