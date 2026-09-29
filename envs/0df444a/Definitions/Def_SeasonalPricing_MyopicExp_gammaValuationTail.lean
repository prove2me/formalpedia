-- Prove2me | Definitions.Def_SeasonalPricing_MyopicExp_gammaValuationTail
-- name    : SeasonalPricing_MyopicExp_gammaValuationTail
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:14:07.540418+00:00
-- url     : https://prove2.me/theorems/466c4844-17ca-4e9f-ae3e-98fb107210ee
-- title:
--   Gamma valuation tail $\bar F$ with mean $\mu$ and coefficient of variation $c$, and the decay ratio $\rho = e^{-\alpha H}$
-- statement:
--   In the model of Aviv and Pazgal, each customer $j$ has a **base valuation** $V_j$ drawn from a distribution $F$, and the valuation at time $t$ is $V_j e^{-\alpha t}$ with a decline factor $\alpha \ge 0$. The numerical study (§7) takes $F$ to be a Gamma law with mean $\mu > 0$ and coefficient of variation $c > 0$ (standard deviation divided by mean), whose density is
--
--   $$
--   f(x \mid \mu, c) = \frac{\frac{1}{\mu c^2}\left(\frac{x}{\mu c^2}\right)^{1/c^2 - 1} e^{-x/(\mu c^2)}}{\Gamma(1/c^2)}, \qquad x \ge 0,
--   $$
--
--   that is, the Gamma law with shape $1/c^2$ and rate $1/(\mu c^2)$. This item defines its **tail**
--
--   $$
--   \bar F(x) = 1 - F(x) = \Pr\{V > x\}, \qquad x \in \mathbb R .
--   $$
--
--   For $\mu = c = 1$ the law is exponential with mean one, and $\bar F(x) = e^{-x}$ for $x \ge 0$, $\bar F(x) = 1$ for $x < 0$.
--
--   The item also defines the paper's reparametrization of the decline factor,
--
--   $$
--   \rho = e^{-\alpha H},
--   $$
--
--   the fraction of a customer's base valuation that remains at the end $H$ of the season. With $H = 1$, $\rho = 1$ means $\alpha = 0$: valuations do not decline.
--
--   **Formalization Note** $F$ is Mathlib's cumulative distribution function `ProbabilityTheory.cdf` of `ProbabilityTheory.gammaMeasure (1/c^2) (1/(μ c^2))`. The printed density on p. 349 has the exponent "$1/(sc^2-1)$"; this is a misprint for $1/c^2 - 1$, the only exponent that makes $f$ a Gamma density with mean $\mu$ and coefficient of variation $c$. Only $\mu = c = 1$ is used in this mission, where the exponent is $0$ under either reading.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 343, §3 (V_j(t) = V_j e^{−αt}, base valuation distribution F); p. 349, §7 (Gamma density f(x | μ, c), ρ ≐ e^{−αH}); p. 350, §7 (H = 1, μ = 1)

import Mathlib

namespace SeasonalPricing.MyopicExp

/-- The tail `F̄(x) = 1 − F(x) = Pr{V > x}` of the base valuation `V` in the numerical study of
Aviv–Pazgal 2008 (§7, p. 349): `V` has the Gamma law with mean `μ` and coefficient of variation
`c`, i.e. density `(1/(μc²)) ((1/(μc²)) x)^{1/c² − 1} e^{−x/(μc²)} / Γ(1/c²)` on `x ≥ 0`
(shape `1/c²`, rate `1/(μc²)`). `F` is Mathlib's cumulative distribution function of
`gammaMeasure (1/c²) (1/(μc²))`. -/
noncomputable def gammaValuationTail (μ c x : ℝ) : ℝ :=
  1 - ProbabilityTheory.cdf (ProbabilityTheory.gammaMeasure (1 / c ^ 2) (1 / (μ * c ^ 2))) x

/-- The paper's reparametrization of the valuation decline factor (p. 349):
`ρ ≐ e^{−αH}`, the fraction of a customer's base valuation left at the end `H` of the season. -/
noncomputable def decayRatio (α H : ℝ) : ℝ :=
  Real.exp (-(α * H))

end SeasonalPricing.MyopicExp


