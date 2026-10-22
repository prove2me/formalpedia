-- Prove2me | Definitions.Def_RiskFunctionals_Distortion_DistortionFunctional
-- name    : RiskFunctionals_Distortion_DistortionFunctional
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:08.590294+00:00
-- url     : https://prove2.me/theorems/829598d4-be56-4739-8e7e-03828a781d4f
-- title:
--   The distortion acceptability functional $\mathcal A_H\{G\}=\int_0^1 G^{-1}(p)\,dH(p)$, its domain $\mathcal G_H$, and $\bar H(u)=H(1)-H(1-u)$
-- statement:
--   Let $H$ be a bounded, right continuous, increasing function on $[0,1]$: the distribution function of a non-negative (not necessarily probability) measure $dH$ on $[0,1]$. Let $G$ be a distribution function on $\mathbb R$ with quantile function $G^{-1}(p)=\inf\{u: G(u)\ge p\}$.
--
--   1. $\mathcal G_H$ is the set of distributions $G$ for which $G^{-1}$ is $dH$ integrable.
--   2. For $G\in\mathcal G_H$ the **distortion acceptability functional** is
--   $$\mathcal A_H\{G\}=\int_0^1 G^{-1}(p)\,dH(p). \tag{2.64}$$
--   If a random variable $Y$ has distribution $G$, one also writes $\mathcal A_H(Y)$. Distributions with jumps are allowed.
--   3. The dual distortion function is $\bar H(u)=H(1)-H(1-u)$.
--
--   For $H(p)=p$ the functional is the expectation, for $H=\mathbb 1_{[\alpha,1]}$ the value-at-risk $G^{-1}(\alpha)$, and for $H(p)=\min(p/\alpha,1)$ the average value-at-risk.
--
--   **Formalization Note** $H$ is a Mathlib `StieltjesFunction` (a monotone, right continuous function on $\mathbb R$); only its values on $[0,1]$ enter, and $dH$ is its Lebesgue–Stieltjes measure. $\mathcal A_H\{G\}$ is the integral of $G^{-1}$ over $(0,1]$ against $dH$. Membership $G\in\mathcal G_H$ has three clauses: (a) $H(0)=0$, because $dH$ puts mass $H(0)$ on $p=0$, where $G^{-1}(0)=-\infty$ for every $G$; (b) $G^{-1}$ is $dH$-integrable on $(0,1]$; (c) if $dH$ charges $p=1$, then $G(u)\ge1$ for some $u$, i.e. $G^{-1}(1)$ is finite — otherwise the book's $G^{-1}(1)=+\infty$ carries positive mass, while Lean's quantile function would return the junk value $0$ there.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 81, Definition 2.61; p. 81, Lemma 2.62

import Mathlib
import Definitions.Def_RiskFunctionals_Distortion_QuantileFunction

namespace RiskFunctionals.Distortion

open MeasureTheory

/-- The class `𝒢_H` of Definition 2.61 (Pflug & Römisch, p. 81): the distributions `G` (law `μ`)
for which `G⁻¹` is `dH` integrable, where `H` is a bounded, right continuous, increasing function
on `[0, 1]`, the distribution function of a non-negative measure `dH` on `[0, 1]` (p. 81).
`H` is a `StieltjesFunction` (monotone, right continuous on `ℝ`); only its values on `[0, 1]`
matter. The three clauses:
* `H 0 = 0`: `dH` puts mass `H(0)` on the point `p = 0`, where `G⁻¹(0) = inf ℝ = −∞` for every `G`,
  so `G⁻¹` can be `dH` integrable only if that mass is `0`;
* `G⁻¹` is integrable on `(0, 1]` with respect to the Stieltjes measure `dH`;
* if `dH` charges `p = 1`, then `G⁻¹(1)` is finite, i.e. `{u : G(u) ≥ 1}` is nonempty (otherwise
  the book's `G⁻¹(1) = +∞` would carry positive mass; the Lean quantile function would return the
  junk value `0` there). -/
def InDistortionDomain (H : StieltjesFunction ℝ) (μ : Measure ℝ) : Prop :=
  H 0 = 0 ∧ IntegrableOn (quantileFunction μ) (Set.Ioc 0 1) H.measure ∧
    (H.measure {1} ≠ 0 → ∃ u : ℝ, 1 ≤ distributionFunction μ u)

/-- The distortion acceptability functional (p. 81, Definition 2.61, (2.64)):
`𝒜_H{G} = ∫₀¹ G⁻¹(p) dH(p)`, the Lebesgue–Stieltjes integral of the quantile function of the law
`μ` against `dH` over `(0, 1]` (the point `p = 0` carries no mass on `𝒢_H`). For a random variable
`Y` with distribution `G`, `𝒜_H(Y) = 𝒜_H{G}` is `distortionFunctional H (P.map Y)`. Meaningful
for `μ` in `𝒢_H` (`InDistortionDomain H μ`), which every theorem using it assumes. -/
noncomputable def distortionFunctional (H : StieltjesFunction ℝ) (μ : Measure ℝ) : ℝ :=
  ∫ p in Set.Ioc 0 1, quantileFunction μ p ∂H.measure

/-- The dual distortion function `H̄(u) = H(1) − H(1 − u)` (p. 81, Lemma 2.62). -/
noncomputable def distortionBar (H : StieltjesFunction ℝ) (u : ℝ) : ℝ :=
  H 1 - H (1 - u)

end RiskFunctionals.Distortion


