-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.euler_constant_coefficients_exact_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:20:05.839218+00:00
-- url     : https://prove2.me/submissions/5a1fa92e-8182-4e2e-baad-3fc5f3083e80

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} (W : ℝ → Ω → ℝ)
    (x₀ b σ h : ℝ) (E : ℕ → Ω → ℝ)
    (hE0 : ∀ ω, E 0 ω = x₀)
    (hErec : ∀ (k : ℕ) (ω : Ω),
      E (k + 1) ω = E k ω + b * h +
        σ * (W (((k + 1 : ℕ) : ℝ) * h) ω -
          W ((k : ℝ) * h) ω)) :
    ∀ (k : ℕ) (ω : Ω),
      E k ω = x₀ + b * ((k : ℝ) * h) +
        σ * (W ((k : ℝ) * h) ω - W 0 ω) := by
  intro k
  induction k with
  | zero =>
      intro ω
      simpa using hE0 ω
  | succ k ih =>
      intro ω
      rw [hErec k ω, ih ω]
      push_cast
      ring
