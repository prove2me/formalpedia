-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.euler_constant_coefficients_fin_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:23:31.371387+00:00
-- url     : https://prove2.me/submissions/59ef9f43-5aad-44d3-8dd5-26bac10ba66b

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} (W : ℝ → Ω → ℝ)
    (n : ℕ) (T x₀ b σ : ℝ)
    (E : Fin (n + 1) → Ω → ℝ)
    (hE0 : ∀ ω, E 0 ω = x₀)
    (hErec : ∀ (k : Fin n) (ω : Ω),
      E k.succ ω = E k.castSucc ω + b * (T / (n : ℝ)) +
        σ * (W (((k.val + 1 : ℕ) : ℝ) * (T / (n : ℝ))) ω -
          W ((k.val : ℝ) * (T / (n : ℝ))) ω)) :
    ∀ (k : Fin (n + 1)) (ω : Ω),
      E k ω = x₀ + b * ((k.val : ℝ) * (T / (n : ℝ))) +
        σ * (W ((k.val : ℝ) * (T / (n : ℝ))) ω - W 0 ω) := by
  intro k
  induction k using Fin.inductionOn with
  | zero =>
      intro ω
      simpa using hE0 ω
  | succ k ih =>
      intro ω
      rw [hErec k ω, ih ω]
      simp only [Fin.val_succ, Fin.val_castSucc]
      push_cast
      ring
