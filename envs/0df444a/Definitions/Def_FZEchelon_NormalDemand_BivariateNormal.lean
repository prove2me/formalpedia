-- Prove2me | Definitions.Def_FZEchelon_NormalDemand_BivariateNormal
-- name    : FZEchelon_NormalDemand_BivariateNormal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:02:58.163469+00:00
-- url     : https://prove2.me/theorems/9b7fb780-efcb-4736-b402-3dc91d2d0e99
-- title:
--   The standard normal cdf $\Phi$ and density $\phi$, $\Theta(x)=x\Phi(x)+\phi(x)$, and the bivariate standard normal cdf $\Phi(\xi_1,\xi_2;\rho)$
-- statement:
--   This file fixes the standard normal objects used in §4 of Federgruen and Zipkin (1984).
--
--   1. $\Phi(x)=P(Z\le x)$ for $Z\sim N(0,1)$, the standard normal cdf, and $\phi(x)=(2\pi)^{-1/2}e^{-x^2/2}$, its density.
--   2. $\Theta(x)=x\Phi(x)+\phi(x)$.
--   3. For a correlation $\rho$ with $|\rho|<1$, the bivariate normal density with standard normal marginals and correlation $\rho$,
--   $$\phi_2(s,t;\rho)=\frac{1}{2\pi\sqrt{1-\rho^2}}\exp\Big(-\frac{s^2-2\rho st+t^2}{2(1-\rho^2)}\Big),$$
--   and its cdf
--   $$\Phi(\xi_1,\xi_2;\rho)=\int_{-\infty}^{\xi_1}\int_{-\infty}^{\xi_2}\phi_2(s,t;\rho)\,dt\,ds .$$
--
--   These are the special functions in which the paper expresses the closed form (13) of the induced penalty cost under normal demand.
--
--   **Formalization Note** $\Phi$ is `ProbabilityTheory.cdf (gaussianReal 0 1)` and $\phi$ is `gaussianPDFReal 0 1`. The bivariate cdf is written as an explicit iterated integral of the density over $(-\infty,\xi_1]\times(-\infty,\xi_2]$ rather than through Mathlib's `multivariateGaussian`; the two agree for $|\rho|<1$, and only $\rho\in(-1,0)$ occurs in this mission. For $|\rho|\ge1$ the formula is not a density and the value has no meaning.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, pp. 829-830, §4 (definitions of Φ, φ, Φ(ξ1, ξ2; ρ) and Θ)

import Mathlib

open MeasureTheory ProbabilityTheory Real

namespace FZEchelon.NormalDemand

/-- The standard normal cdf `Φ(x) = P(Z ≤ x)` for `Z ∼ N(0,1)`. -/
noncomputable def stdNormalCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The standard normal density `φ(x) = (2π)^{-1/2} e^{-x²/2}`. -/
noncomputable def stdNormalPDF (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- `Θ(x) = x Φ(x) + φ(x)` (Federgruen–Zipkin 1984, p. 830). -/
noncomputable def Theta (x : ℝ) : ℝ := x * stdNormalCDF x + stdNormalPDF x

/-- The density of a bivariate normal vector with standard normal marginals and correlation `ρ`
(meaningful for `|ρ| < 1`):
`φ₂(s, t; ρ) = (2π √(1-ρ²))⁻¹ exp(-(s² - 2ρst + t²) / (2(1-ρ²)))`. -/
noncomputable def bivNormalPDF (ρ s t : ℝ) : ℝ :=
  (2 * π * Real.sqrt (1 - ρ ^ 2))⁻¹ * Real.exp (-(s ^ 2 - 2 * ρ * s * t + t ^ 2) / (2 * (1 - ρ ^ 2)))

/-- The bivariate standard normal cdf `Φ(ξ₁, ξ₂; ρ) = P(Z₁ ≤ ξ₁, Z₂ ≤ ξ₂)`, as the integral of
`bivNormalPDF ρ` over `(-∞, ξ₁] × (-∞, ξ₂]` (meaningful for `|ρ| < 1`). -/
noncomputable def bivNormalCDF (ξ₁ ξ₂ ρ : ℝ) : ℝ :=
  ∫ s in Set.Iic ξ₁, ∫ t in Set.Iic ξ₂, bivNormalPDF ρ s t

end FZEchelon.NormalDemand


