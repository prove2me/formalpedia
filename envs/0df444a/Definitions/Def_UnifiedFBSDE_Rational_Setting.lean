-- Prove2me | Definitions.Def_UnifiedFBSDE_Rational_Setting
-- name    : UnifiedFBSDE_Rational_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:13:18.525137+00:00
-- url     : https://prove2.me/theorems/89985454-aebc-4385-9745-c6a5889e80fd
-- title:
--   (3.9), (5.3), (5.8), (5.9), pp. 10, 20, 22 — the rational F of the constant-coefficient linear FBSDE and solutions of y_t = h + ∫ₜᵀ F(y_s) ds keeping y and (1 − σ₃y)⁻¹ bounded
-- statement:
--   This file fixes the deterministic objects of §5.1, Case 2, of Ma, Wu, Zhang and Zhang.
--
--   For the linear forward–backward SDE (4.1) with constant coefficients, the data are nine real numbers $b_1,b_2,b_3,\sigma_1,\sigma_2,\sigma_3,f_1,f_2,f_3$ (a record `Coeffs`). The function of (3.9) is
--   $$
--   F(y)=f_1+f_2y+y(b_1+b_2y)+\frac{(f_3+b_3y)\,y\,(\sigma_1+\sigma_2y)}{1-\sigma_3y},
--   $$
--   defined away from the pole $y=1/\sigma_3$. The number $\alpha_3=b_2-b_3\sigma_2/\sigma_3$ is the coefficient of $y^2$ in (5.8), and the predicate `IsDecomp58 α₀ α₁ α₂` says that
--   $$
--   F(y)=\frac{\alpha_0}{1/\sigma_3-y}+\alpha_1+\alpha_2y+\Big[b_2-\frac{b_3\sigma_2}{\sigma_3}\Big]y^2\qquad\text{whenever }1-\sigma_3y\neq0 .
--   $$
--
--   A function $y:\mathbb R\to\mathbb R$ **solves the backward integral equation** $y_t=h+\int_t^T G(s,y_s)\,ds$ on $[0,T]$ if for every $t\in[0,T]$ the integrand $s\mapsto G(s,y_s)$ is integrable on $[t,T]$ and the identity holds. A solution of (5.3), $y_t=h+\int_t^TF(y_s)\,ds$, **satisfies (5.9)** if both $y$ and $(1-\sigma_3y)^{-1}$ are bounded on $[0,T]$; the second condition is stated as: there is $\kappa>0$ with $|1-\sigma_3y_t|\ge\kappa$ for all $t\in[0,T]$.
--
--   These are the objects of Theorem 5.6, which characterises when (5.3) has a solution satisfying (5.9) on every horizon.
--
--   **Formalization Note** Lean evaluates $x/0$ as $0$, so `Coeffs.F` has a junk value at $y=1/\sigma_3$ and `α₃` is junk when $\sigma_3=0$; every statement of the mission keeps its arguments off the pole and assumes $\sigma_3\neq0$ where $\alpha_3$ or $1/\sigma_3$ appears. Integrability is part of the solution predicate because the Lean integral of a non-integrable function is $0$. "$(1-\sigma_3y)^{-1}$ bounded" is encoded as $|1-\sigma_3y_t|\ge\kappa>0$, never as a bound on the Lean inverse, which is $0$ at the pole.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 10, (3.9), (3.10); p. 20, (5.3); p. 22, (5.8), (5.9)

import Mathlib
import Definitions.Def_UnifiedFBSDE_Cubic_Setting

namespace UnifiedFBSDE.Rational

/-- The nine constant coefficients `b₁ b₂ b₃ σ₁ σ₂ σ₃ f₁ f₂ f₃` of the linear FBSDE (4.1)
of Ma–Wu–Zhang–Zhang (arXiv:1110.4658v2); for constant coefficients the difference quotients
(3.1) are these constants themselves. -/
structure Coeffs where
  b₁ : ℝ
  b₂ : ℝ
  b₃ : ℝ
  σ₁ : ℝ
  σ₂ : ℝ
  σ₃ : ℝ
  f₁ : ℝ
  f₂ : ℝ
  f₃ : ℝ

/-- The function `F` of (3.9), p. 10, with constant coefficients:
`F(y) = f₁ + f₂ y + y (b₁ + b₂ y) + (f₃ + b₃ y) y (σ₁ + σ₂ y) / (1 − σ₃ y)`.
At the pole `y = 1/σ₃` Lean's convention `x / 0 = 0` gives a junk value; no statement of
the mission evaluates `F` there. -/
noncomputable def Coeffs.F (c : Coeffs) (y : ℝ) : ℝ :=
  c.f₁ + c.f₂ * y + y * (c.b₁ + c.b₂ * y) +
    (c.f₃ + c.b₃ * y) * y * (c.σ₁ + c.σ₂ * y) / (1 - c.σ₃ * y)

/-- `α₃ = b₂ − b₃ σ₂ / σ₃`, the coefficient of `y²` in (5.8); meaningful only for `σ₃ ≠ 0`. -/
noncomputable def Coeffs.α₃ (c : Coeffs) : ℝ :=
  c.b₂ - c.b₃ * c.σ₂ / c.σ₃

/-- The constants `α₀, α₁, α₂` give the decomposition (5.8), p. 22:
`F(y) = α₀ / (1/σ₃ − y) + α₁ + α₂ y + [b₂ − b₃σ₂/σ₃] y²` for every `y` off the pole. -/
def Coeffs.IsDecomp58 (c : Coeffs) (α₀ α₁ α₂ : ℝ) : Prop :=
  ∀ y : ℝ, 1 - c.σ₃ * y ≠ 0 →
    c.F y = α₀ / (1 / c.σ₃ - y) + α₁ + α₂ * y + (c.b₂ - c.b₃ * c.σ₂ / c.σ₃) * y ^ 2

/-- `y` is a solution of the ODE (5.3), `y_t = h + ∫ₜᵀ F(y_s) ds`, on `[0, T]` satisfying (5.9):
both `y` and `(1 − σ₃ y)⁻¹` are bounded on `[0, T]`; the latter is stated as
`|1 − σ₃ y_t| ≥ κ` for some `κ > 0`. -/
def IsSolution59 (c : Coeffs) (h T : ℝ) (y : ℝ → ℝ) : Prop :=
  UnifiedFBSDE.Cubic.IsSolution (fun _ z => c.F z) h T y ∧
    (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, |y t| ≤ C) ∧
    (∃ κ : ℝ, 0 < κ ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, κ ≤ |1 - c.σ₃ * y t|)

end UnifiedFBSDE.Rational


