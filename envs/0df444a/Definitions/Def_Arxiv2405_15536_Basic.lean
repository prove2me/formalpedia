-- Prove2me | Definitions.Def_Arxiv2405_15536_Basic
-- name    : Arxiv2405_15536_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T18:06:34.94469+00:00
-- url     : https://prove2.me/theorems/003c54f9-e83b-483b-a6f4-de3cdab18ee5
-- title:
--   $\kappa$-exponential, $\kappa$-Gaussian, $\kappa$-objective function and influence function
-- statement:
--   Objects of Sections 2.1 and 2.2 of da Silva and Kaniadakis (2024).
--
--   1. **κ-exponential (eq. 9).** For $\kappa\neq0$ and $y\in\mathbb{R}$, $\exp_\kappa(y)=\big(\sqrt{1+\kappa^2y^2}+\kappa y\big)^{1/\kappa}$; the base is always positive. In the classical case $\exp_0=\exp$.
--   2. **κ-Gaussian (eqs. 6-8).** $p_\kappa(\varepsilon)=\exp_\kappa(-\beta_\kappa\varepsilon^2)/Z_\kappa$, where, writing $a=1/|2\kappa|$,
--   $$\beta_\kappa=\frac{|2\kappa|^{-1}}{2}\,\frac{1+\frac12|\kappa|}{1+\frac32|\kappa|}\,\frac{\Gamma(a-\frac34)\,\Gamma(a+\frac14)}{\Gamma(a+\frac34)\,\Gamma(a-\frac14)},\qquad Z_\kappa=\sqrt{\frac{\pi}{\beta_\kappa}}\,\frac{|2\kappa|^{-1/2}}{1+\frac12|\kappa|}\,\frac{\Gamma(a-\frac14)}{\Gamma(a+\frac14)}$$
--   for $0<|\kappa|<2/3$, and $\beta_0=1/2$, $Z_0=\sqrt{2\pi}$, so that $p_0$ is the standard Gaussian density of eq. (10).
--   3. **κ-likelihood (eq. 11).** For finitely many errors $(\varepsilon_i)_{i\in I}$, $\mathcal L_\kappa=\prod_{i\in I}p_\kappa(\varepsilon_i)$.
--   4. **Objective functions (eqs. 1 and 12).** For a single residual value, the κ-loss is $-\ln\exp_\kappa(-\beta_\kappa\varepsilon^2)$. For residual traces $\varepsilon_{s,r}(t)=\Gamma_{s,r}u_s(m,t)-d_{s,r}(t)$ over finitely many sources $s$ and receivers $r$ and times $t\in[0,T]$,
--   $$\phi_\kappa=-\sum_{s,r}\int_0^T\ln\big[\exp_\kappa(-\beta_\kappa\varepsilon_{s,r}(t)^2)\big]\,dt,\qquad \phi_0=\frac12\sum_{s,r}\int_0^T\varepsilon_{s,r}(t)^2\,dt.$$
--   5. **Influence function (eq. 13).** $\Upsilon_\kappa(\varepsilon)$ is the derivative with respect to $\varepsilon$ of the κ-loss of a single residual.
--   6. **Robustness (Hampel).** An objective is robust if its influence function satisfies $\Upsilon(\varepsilon)\to0$ as $\varepsilon\to\pm\infty$, and non-robust if $\Upsilon(\varepsilon)\to\pm\infty$ as $\varepsilon\to\pm\infty$.
--
--   **Formalization Note** At $\kappa=0$ the quantities $\exp_0$, $\beta_0$, $Z_0$ are set to the values the paper gives for the classical limit; all limit statements are taken over $\kappa\to0$ with $\kappa\neq0$, so they concern the printed formulas. The residual traces are taken as given real functions of time; the acoustic wave equation (2) that produces them is not modelled, since no stated result depends on it. The integrals are Lebesgue integrals over $[0,T]$. "Non-robust" is read with matched signs: $\Upsilon\to+\infty$ as $\varepsilon\to+\infty$ and $\Upsilon\to-\infty$ as $\varepsilon\to-\infty$.
-- source:
--   da Silva and Kaniadakis, A graph-space optimal transport FWI approach based on kappa-generalized Gaussian distribution, arXiv:2405.15536v1 (2024), Sec. 2.1 eq. (1), Sec. 2.2 eqs. (6)-(13) and the robustness criterion after eq. (13), PDF pp. 2-4

import Mathlib

/-!
da Silva and Kaniadakis, *A graph-space optimal transport FWI approach based on
κ-generalized Gaussian distribution*, arXiv:2405.15536v1 (2024): the κ-exponential, the
κ-Gaussian distribution, the least-squares and κ-objective functions, the influence function
and Hampel's robustness criterion of Sections 2.1 and 2.2.

Conventions. At `κ = 0` the κ-quantities are given the values the paper assigns to them in its
classical limit (Sec. 2.2, text after eq. (10)): `exp_0 = exp`, `β_0 = 1/2`, `Z_0 = √(2π)`.
For `κ ≠ 0` they are the printed formulas (7)-(9), which the paper states for `|κ| < 2/3`.
Residual traces `ε_{s,r}(t) = Γ_{s,r} u_s(m,t) - d_{s,r}(t)` are taken as given real functions
of time, indexed by finite sets of sources and receivers.
-/

open MeasureTheory Filter

noncomputable section

namespace Arxiv2405_15536

/-- Eq. (9), Sec. 2.2, p. 3: the Kaniadakis κ-exponential
`exp_κ(y) = (√(1 + κ² y²) + κ y)^(1/κ)` for `κ ≠ 0` (the base is always positive), and
`exp_0 = exp` (Sec. 2.2, text after eq. (10)). -/
def expKappa (κ y : ℝ) : ℝ :=
  if κ = 0 then Real.exp y else (Real.sqrt (1 + κ ^ 2 * y ^ 2) + κ * y) ^ (1 / κ)

/-- Eq. (8), Sec. 2.2, p. 3: the factor
`β_κ = (|2κ|⁻¹/2) · (1 + |κ|/2)/(1 + 3|κ|/2) · Γ(1/|2κ| - 3/4) Γ(1/|2κ| + 1/4) /
(Γ(1/|2κ| + 3/4) Γ(1/|2κ| - 1/4))` for `κ ≠ 0` (stated for `|κ| < 2/3`), and `β_0 = 1/2`
(text after eq. (10)). -/
def betaKappa (κ : ℝ) : ℝ :=
  if κ = 0 then 1 / 2 else
    (|2 * κ|⁻¹ / 2) * ((1 + |κ| / 2) / (1 + 3 / 2 * |κ|)) *
      (Real.Gamma (1 / |2 * κ| - 3 / 4) * Real.Gamma (1 / |2 * κ| + 1 / 4)) /
      (Real.Gamma (1 / |2 * κ| + 3 / 4) * Real.Gamma (1 / |2 * κ| - 1 / 4))

/-- Eq. (7), Sec. 2.2, p. 3: the normalization constant
`Z_κ = √(π/β_κ) · |2κ|^(-1/2)/(1 + |κ|/2) · Γ(1/|2κ| - 1/4)/Γ(1/|2κ| + 1/4)` for `κ ≠ 0`
(stated for `|κ| < 2/3`), and `Z_0 = √(2π)` (text after eq. (10)). -/
def zKappa (κ : ℝ) : ℝ :=
  if κ = 0 then Real.sqrt (2 * Real.pi) else
    Real.sqrt (Real.pi / betaKappa κ) * (|2 * κ| ^ (-(1 / 2 : ℝ)) / (1 + |κ| / 2)) *
      (Real.Gamma (1 / |2 * κ| - 1 / 4) / Real.Gamma (1 / |2 * κ| + 1 / 4))

/-- Eq. (6), Sec. 2.2, p. 3: the κ-Gaussian density `p_κ(ε) = exp_κ(-β_κ ε²) / Z_κ`. -/
def kappaGaussian (κ ε : ℝ) : ℝ :=
  expKappa κ (-betaKappa κ * ε ^ 2) / zKappa κ

/-- Eq. (11), Sec. 2.2, p. 4: the κ-likelihood `L_κ = ∏_{i=1}^N p_κ(ε_i)` of a finite family of
independent errors `ε_i`, indexed by a finite type of samples. -/
def kappaLikelihood {I : Type*} [Fintype I] (κ : ℝ) (ε : I → ℝ) : ℝ :=
  ∏ i, kappaGaussian κ (ε i)

/-- Eq. (12), Sec. 2.2, p. 4: the κ-objective of a single residual value,
`-ln exp_κ(-β_κ ε²)` (the integrand of eq. (12), plotted in Fig. 1(c)). -/
def lossKappa (κ ε : ℝ) : ℝ :=
  -Real.log (expKappa κ (-betaKappa κ * ε ^ 2))

/-- Eq. (12), Sec. 2.2, p. 4: the κ-objective function
`φ_κ = -∑_{s,r} ∫_0^T ln[exp_κ(-β_κ ε_{s,r}(t)²)] dt` of residual traces `e s r t`
(`s` a source, `r` a receiver, `t ∈ [0, T]` time). -/
def phiKappa {S R : Type*} [Fintype S] [Fintype R] (κ T : ℝ) (e : S → R → ℝ → ℝ) : ℝ :=
  ∑ s, ∑ r, ∫ t in Set.Icc 0 T, lossKappa κ (e s r t)

/-- Eq. (1), Sec. 2.1, p. 2: the least-squares objective
`φ_0 = (1/2) ∑_{s,r} ∫_0^T ε_{s,r}(t)² dt` of residual traces
`ε_{s,r}(t) = Γ_{s,r} u_s(m,t) - d_{s,r}(t)`. -/
def phi0 {S R : Type*} [Fintype S] [Fintype R] (T : ℝ) (e : S → R → ℝ → ℝ) : ℝ :=
  (1 / 2) * ∑ s, ∑ r, ∫ t in Set.Icc 0 T, e s r t ^ 2

/-- Eq. (13), Sec. 2.2, p. 4: the influence function `Υ_κ(ε) = ∂φ_κ/∂ε` of the κ-objective
with respect to a single residual `ε` (for a fixed model), i.e. the derivative of
`ε ↦ -ln exp_κ(-β_κ ε²)`. -/
def influence (κ ε : ℝ) : ℝ :=
  deriv (lossKappa κ) ε

/-- Sec. 2.2, p. 4 (after eq. (13)), following Hampel et al.: an objective whose influence
function `Υ` satisfies `Υ(ε) → 0` as `ε → ±∞` is called robust. -/
def IsRobust (f : ℝ → ℝ) : Prop :=
  Tendsto f atTop (nhds 0) ∧ Tendsto f atBot (nhds 0)

/-- Sec. 2.2, p. 4 (after eq. (13)), following Hampel et al.: an objective whose influence
function `Υ` satisfies `Υ(ε) → ±∞` as `ε → ±∞` is called non-robust. -/
def IsNonRobust (f : ℝ → ℝ) : Prop :=
  Tendsto f atTop atTop ∧ Tendsto f atBot atBot

end Arxiv2405_15536


