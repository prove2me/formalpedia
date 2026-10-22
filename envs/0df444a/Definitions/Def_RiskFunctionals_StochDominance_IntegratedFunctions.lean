-- Prove2me | Definitions.Def_RiskFunctionals_StochDominance_IntegratedFunctions
-- name    : RiskFunctionals_StochDominance_IntegratedFunctions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:29.121113+00:00
-- url     : https://prove2.me/theorems/1bb67e9e-2770-4e87-a203-2eafc556a402
-- title:
--   The integrated distribution function $\mathcal G$, the integrated quantile function $\mathcal G^{[-1]}$ and the Lorenz curve $L_G$
-- statement:
--   Let $G$ be the distribution function and $G^{-1}$ the quantile function of a probability law $\mu$ on $\mathbb R$, and suppose that the first moment of $G$ exists. The file defines three functions built from them.
--
--   1. The **integrated distribution function** (IDF)
--   $$\mathcal G(u) = \int_{-\infty}^{u} G(v)\,dv, \qquad u \in \mathbb R. \tag{1.16}$$
--   2. The **integrated quantile function** (IQF)
--   $$\mathcal G^{[-1]}(p) = \int_0^{p} G^{-1}(q)\,dq, \qquad 0 < p \le 1. \tag{1.17}$$
--   The bracket in $[-1]$ signals that $\mathcal G^{[-1]}$ is not the inverse of $\mathcal G$. The book notes $\mathcal G^{[-1]}(1) = \int u\,dG(u) = \mathbb E\{G\}$.
--   3. For a distribution with finite (and nonzero) expectation, the **Lorenz curve**
--   $$L_G(p) = \frac{\mathcal G^{[-1]}(p)}{\mathcal G^{[-1]}(1)} = \frac{\mathcal G^{[-1]}(p)}{\mathbb E\{G\}} .$$
--
--   The IDF and the IQF give the second-order dominance its two classical analytic characterizations; the Lorenz curve normalizes the IQF by the mean.
--
--   **Formalization Note** The IDF is the Lebesgue integral of $G$ over $(-\infty,u]$ and the IQF the Lebesgue integral of $G^{-1}$ over $(0,p]$; both are real numbers, and Lean's Bochner integral returns $0$ for a non-integrable integrand, so they are meaningful only under the first-moment hypothesis, which every theorem using them states. The value of $G^{-1}$ at the single point $q=1$ (where the book's value may be $+\infty$) does not affect the IQF. The Lorenz curve is the real quotient $\mathcal G^{[-1]}(p)/\mathcal G^{[-1]}(1)$, which Lean evaluates to $0$ when the denominator is $0$; every theorem using it assumes a nonzero mean.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 14–15, Definition 1.12, Eqs. (1.16)–(1.17); p. 19, Definition 1.15

import Mathlib
import Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction

namespace RiskFunctionals.StochDominance

open MeasureTheory

/-- The integrated distribution function (IDF) (1.16), `𝒢(u) = ∫_{-∞}^u G(v) dv`
(Pflug & Römisch, p. 14, Definition 1.12). Meaningful when `G` has a first moment, which every
theorem using it assumes. -/
noncomputable def integratedDistributionFunction (μ : Measure ℝ) (u : ℝ) : ℝ :=
  ∫ v in Set.Iic u, distributionFunction μ v

/-- The integrated quantile function (IQF) (1.17), `𝒢^{[-1]}(p) = ∫_0^p G⁻¹(q) dq`
(Pflug & Römisch, p. 15, Definition 1.12), for `0 < p ≤ 1`. The integral is over `(0, p]`; the
value of `G⁻¹` at the single point `q = 1` does not affect it. -/
noncomputable def integratedQuantileFunction (μ : Measure ℝ) (p : ℝ) : ℝ :=
  ∫ q in Set.Ioc 0 p, quantileFunction μ q

/-- The Lorenz curve (Pflug & Römisch, p. 19, Definition 1.15) of a distribution with finite
expectation, `L_G(p) = 𝒢^{[-1]}(p) / 𝒢^{[-1]}(1)` (`= 𝒢^{[-1]}(p) / 𝔼{G}`). The quotient is
meaningful only when `𝒢^{[-1]}(1) ≠ 0`; every theorem using it assumes a nonzero mean. -/
noncomputable def lorenzCurve (μ : Measure ℝ) (p : ℝ) : ℝ :=
  integratedQuantileFunction μ p / integratedQuantileFunction μ 1

end RiskFunctionals.StochDominance


