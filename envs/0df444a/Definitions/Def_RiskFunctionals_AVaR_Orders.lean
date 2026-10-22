-- Prove2me | Definitions.Def_RiskFunctionals_AVaR_Orders
-- name    : RiskFunctionals_AVaR_Orders
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:27.275341+00:00
-- url     : https://prove2.me/theorems/8c89081b-a940-4c03-add5-982a3bff69ae
-- title:
--   Second-order stochastic dominance through concave utilities, and comonotonicity through the upper Fréchet copula
-- statement:
--   1. Let $G_1$, $G_2$ be distribution functions on $\mathbb R$ (laws $\mu_1$, $\mu_2$). $G_1$ is dominated by $G_2$ in **second-order stochastic dominance**, $G_1\prec_{SSD} G_2$, if
--   $$\int U(v)\,dG_1(v) \le \int U(v)\,dG_2(v)$$
--   for every nondecreasing concave utility $U:\mathbb R\to\mathbb R$ for which both integrals exist. For random variables, $Y^{(1)}\prec_{SSD}Y^{(2)}$ refers to their laws.
--   2. Two random variables $Y^{(1)}$, $Y^{(2)}$ on $(\Omega,\mathcal F,\mathbb P)$ with distribution functions $G_1$, $G_2$ are **comonotone** if they are coupled with the upper Fréchet copula $C(s,t)=\min(s,t)$, i.e.
--   $$\mathbb P\{Y^{(1)}\le u,\ Y^{(2)}\le v\} = \min\big(G_1(u), G_2(v)\big)\qquad\text{for all } u, v\in\mathbb R. \tag{1.11}$$
--
--   Second-order dominance is the order with respect to which the average value-at-risk is isotonic, and comonotone additivity is one of its properties.
--
--   **Formalization Note** "For which the integrals exist" is encoded as integrability of $U$ with respect to both laws. Concavity is on the whole real line. Both notions are defined in mission I of this series (SSD) or not yet on the platform (comonotonicity); drafts cannot import one another, so they are stated here.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 13, Definition 1.10(ii); pp. 8–9, Definition 1.4, case (ii), Eq. (1.11)

import Mathlib
import Definitions.Def_RiskFunctionals_AVaR_QuantileFunction

namespace RiskFunctionals.AVaR

open MeasureTheory

/-- Second-order stochastic dominance `G₁ ≺_SSD G₂` (Pflug & Römisch, p. 13, Definition
1.10(ii)), for distributions given as probability measures `μ₁`, `μ₂` on `ℝ`:
`∫ U dG₁ ≤ ∫ U dG₂` for every nondecreasing concave `U` for which both integrals exist. -/
def SSD (μ₁ μ₂ : Measure ℝ) : Prop :=
  ∀ U : ℝ → ℝ, Monotone U → ConcaveOn ℝ Set.univ U → Integrable U μ₁ → Integrable U μ₂ →
    ∫ v, U v ∂μ₁ ≤ ∫ v, U v ∂μ₂

/-- Two random variables `Y₁`, `Y₂` on `(Ω, ℱ, P)` are comonotone (Pflug & Römisch, pp. 8–9,
Definition 1.4, case (ii), (1.11)) if they are coupled with the upper Fréchet copula `C(s, t) = min(s, t)`,
i.e. their joint distribution function is
`P{Y₁ ≤ u, Y₂ ≤ v} = min(G₁(u), G₂(v))` for all `u, v`. -/
def Comonotone {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y₁ Y₂ : Ω → ℝ) : Prop :=
  ∀ u v : ℝ, P.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} =
    min (distributionFunction (P.map Y₁) u) (distributionFunction (P.map Y₂) v)

end RiskFunctionals.AVaR


