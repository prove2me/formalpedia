-- Prove2me | Definitions.Def_AppliedSDE_SarkkaSolin_Ch02NumericalAlgorithms
-- name    : AppliedSDE_SarkkaSolin_Ch02NumericalAlgorithms
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-13T17:58:31.026201+00:00
-- url     : https://prove2.me/theorems/cae9335d-4217-47e8-8837-b7d8ff0f3c11
-- title:
--   Euler, Heun, classical RK4 and Picard iteration update formulas
-- statement:
--   Algorithm 2.6, Eq. (2.74): explicit Euler update. Algorithm 2.7, Eq. (2.78): Heun predictor-corrector update. Algorithm 2.8, Eq. (2.79): four-stage classical RK4 update. Algorithm 2.10, Eq. (2.83): deterministic integral Picard iteration map. These scalar definitions capture the exact source recurrence formulas. Global orders 1, 2, 4 and Picard fixed-point convergence require separate theorem proofs.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   x_{n+1}=x_n+h\,f(t_n,x_n)\quad\text{(Euler update)}
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Algorithms 2.6, 2.7, 2.8 and 2.10, equations (2.74), (2.78), (2.79), (2.83), printed pp. 16–19. https://doi.org/10.1017/9781108186735

import Mathlib
set_option autoImplicit false

namespace AppliedSDE.SarkkaSolin

/-- Algorithm 2.6, equation (2.74): one explicit Euler step. -/
def eulerStep (f : ℝ → ℝ → ℝ) (t x Δ : ℝ) : ℝ :=
  x + f x t * Δ

/-- Algorithm 2.7, equation (2.78): one predictor-corrector Heun step. -/
noncomputable def heunStep (f : ℝ → ℝ → ℝ) (t x Δ : ℝ) : ℝ :=
  let predicted := x + f x t * Δ
  x + Δ / 2 * (f x t + f predicted (t + Δ))

/-- Algorithm 2.8, equation (2.79): one classical fourth-order RK step. -/
noncomputable def rk4Step (f : ℝ → ℝ → ℝ) (t x Δ : ℝ) : ℝ :=
  let k₁ := Δ * f x t
  let k₂ := Δ * f (x + k₁ / 2) (t + Δ / 2)
  let k₃ := Δ * f (x + k₂ / 2) (t + Δ / 2)
  let k₄ := Δ * f (x + k₃) (t + Δ)
  x + (k₁ + 2 * k₂ + 2 * k₃ + k₄) / 6

/-- Algorithm 2.10, equation (2.83): the Picard iteration map. -/
noncomputable def picardUpdate
    (f : ℝ → ℝ → ℝ) (t₀ x₀ : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  x₀ + ∫ s in t₀..t, f (g s) s

end AppliedSDE.SarkkaSolin


