-- Prove2me | Definitions.Def_MakeToStockRM_ExpDensity_expDensity
-- name    : MakeToStockRM_ExpDensity_expDensity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:35:24.796085+00:00
-- url     : https://prove2.me/theorems/0785a335-e45e-4298-aaf5-80e78f6e6111
-- title:
--   Exponents $m_x, m_y$ of (47) and the exponential density $e^{m_x x+m_y y}$
-- statement:
--   Let $\theta\in\mathbb R$, $\sigma>0$, $\delta>0$ and $\varrho\in(-1,1)$ be the drift, diffusion coefficients and correlation of the inventory/log-price diffusion. Equation (47) of the paper defines the exponents
--
--   $$
--   m_x=\frac{2\theta}{\sigma^2(1-\varrho^2)},\qquad m_y=\frac{-2\varrho\theta}{\sigma\delta(1-\varrho^2)},
--   $$
--
--   and the (unnormalized) exponential density
--
--   $$
--   p(x,y)=\exp(m_x x+m_y y),\qquad (x,y)\in\mathbb R^2 .
--   $$
--
--   Proposition 2 asserts that, under normal reflection, the steady-state distribution of $(\mathcal X,\mathcal Y)$ on the region $\Omega$ is $\pi_\Omega=K_\Omega\,p$ for a positive normalizing constant $K_\Omega$.
--
--   **Formalization Note** The normalizing constant $K_\Omega$ is not part of this definition; its existence and positivity are a separate theorem. Lean's division returns $0$ when the denominator vanishes, so $m_x,m_y$ carry their intended values only when $\sigma\neq0$, $\delta\neq0$ and $\varrho^2\neq1$; every theorem using them assumes $\sigma>0$, $\delta>0$, $|\varrho|<1$.
-- source:
--   Caldentey, Wein, Revenue Management of a Make-to-Stock Queue, Oper. Res. 54(5), 2006, p. 867, Proposition 2, eq. (47)

import Mathlib

namespace MakeToStockRM.ExpDensity

/-- The exponent `m_x = 2θ / (σ²(1 − ϱ²))` of (47) (Caldentey–Wein 2006, p. 867). -/
noncomputable def mx (θ σ ϱ : ℝ) : ℝ := 2 * θ / (σ ^ 2 * (1 - ϱ ^ 2))

/-- The exponent `m_y = −2ϱθ / (σδ(1 − ϱ²))` of (47) (Caldentey–Wein 2006, p. 867). -/
noncomputable def my (θ σ δ ϱ : ℝ) : ℝ := -2 * ϱ * θ / (σ * δ * (1 - ϱ ^ 2))

/-- The unnormalized exponential density `(x, y) ↦ exp(m_x x + m_y y)` of Proposition 2. -/
noncomputable def expDensity (θ σ δ ϱ : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.exp (mx θ σ ϱ * z.1 + my θ σ δ ϱ * z.2)

end MakeToStockRM.ExpDensity


