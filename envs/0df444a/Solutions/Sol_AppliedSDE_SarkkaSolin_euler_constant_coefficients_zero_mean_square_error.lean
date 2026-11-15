-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.euler_constant_coefficients_zero_mean_square_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:44:26.309414+00:00
-- url     : https://prove2.me/submissions/cf883a38-0599-455f-8b53-8e5c079f93a8

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_constant_coefficients_fin_grid
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ → Ω → ℝ) (n : ℕ) (T x₀ b σ : ℝ)
    (X : ℝ → Ω → ℝ) (E : Fin (n + 1) → Ω → ℝ)
    (hX : ∀ (t : ℝ) (ω : Ω),
      X t ω = x₀ + b * t + σ * (W t ω - W 0 ω))
    (hE0 : ∀ ω, E 0 ω = x₀)
    (hErec : ∀ (k : Fin n) (ω : Ω),
      E k.succ ω = E k.castSucc ω + b * (T / (n : ℝ)) +
        σ * (W (((k.val + 1 : ℕ) : ℝ) * (T / (n : ℝ))) ω -
          W ((k.val : ℝ) * (T / (n : ℝ))) ω)) :
    ∀ (k : Fin (n + 1)),
      (∫ ω, (X ((k.val : ℝ) * (T / (n : ℝ))) ω - E k ω) ^ 2 ∂P) = 0 := by
  have hexact :=
    AppliedSDE.SarkkaSolin.euler_constant_coefficients_fin_grid
      W n T x₀ b σ E hE0 hErec
  intro k
  have hzero :
      (fun ω : Ω =>
        (X ((k.val : ℝ) * (T / (n : ℝ))) ω - E k ω) ^ 2) =
        fun _ : Ω => (0 : ℝ) := by
    funext ω
    rw [hX, hexact k ω]
    ring
  rw [hzero]
  simp
