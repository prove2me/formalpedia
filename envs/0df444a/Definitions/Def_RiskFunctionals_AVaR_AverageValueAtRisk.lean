-- Prove2me | Definitions.Def_RiskFunctionals_AVaR_AverageValueAtRisk
-- name    : RiskFunctionals_AVaR_AverageValueAtRisk
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:23.748164+00:00
-- url     : https://prove2.me/theorems/05746840-5fb6-4201-a80e-249570dd343b
-- title:
--   The average value-at-risk $\mathbb{AV@R}_\alpha(Y)=\frac1\alpha\int_0^\alpha G^{-1}(u)\,du$, its deviation, and the quantities $\alpha^+_G$, $\alpha^-_G$
-- statement:
--   Let $Y$ be a random variable on $(\Omega,\mathcal F,\mathbb P)$ with distribution function $G$ and quantile function $G^{-1}$, and let $0<\alpha\le 1$. The book works with *profit* variables: larger values of $Y$ are better.
--
--   1. The **average value-at-risk** of $Y$ at level $\alpha$ is the average of the lower $\alpha$-fraction of the quantiles,
--   $$\mathbb{AV@R}_\alpha(Y) = \frac{1}{\alpha}\int_0^\alpha G^{-1}(u)\,du. \tag{2.15}$$
--   In particular $\mathbb{AV@R}_1(Y)=\mathbb E Y$.
--   2. The **average value-at-risk deviation** is
--   $$\mathbb{AV@R}\mathbb D_\alpha(Y) = \mathbb E Y - \mathbb{AV@R}_\alpha(Y). \tag{2.16}$$
--   3. The two quantities that measure a jump of $G$ at $G^{-1}(\alpha)$ are
--   $$\alpha^+_G = \inf\{G(u) : G(u)\ge \alpha\}, \qquad \alpha^-_G = \sup\{G(u) : G(u) < \alpha\}.$$
--
--   The average value-at-risk is the lower-tail functional of the book: it averages the *worst* outcomes of a profit, which is the mirror image of the upper-tail conditional value-at-risk of a loss.
--
--   **Formalization Note** $\mathbb{AV@R}_\alpha(Y)$ is defined for a random variable $Y$ through its law, the image of $\mathbb P$ under $Y$, so it depends on $Y$ only through its distribution. The integral is the Lebesgue integral over $(0,\alpha]$; it equals $0$ when $G^{-1}$ is not integrable there, and the factor $1/\alpha$ is $0$ at $\alpha=0$: every theorem using the functional assumes $Y$ integrable and $0<\alpha\le 1$. $\alpha^+_G$ is computed with `sInf` and is a junk $0$ when no $u$ has $G(u)\ge\alpha$ (the case $G^{-1}(\alpha)=+\infty$); every theorem using it assumes such a $u$ exists. For $\alpha>0$ the set defining $\alpha^-_G$ is nonempty and bounded above by $\alpha$. The second expression of (2.15) (the integral of $G$) is not part of the definition.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 48, Definition 2.33, Eqs. (2.15)–(2.16); p. 49 (α⁺_G, α⁻_G)

import Mathlib
import Definitions.Def_RiskFunctionals_AVaR_QuantileFunction

namespace RiskFunctionals.AVaR

open MeasureTheory

/-- The average value-at-risk (Pflug & Römisch, p. 48, Definition 2.33, (2.15)) of a random
variable `Y` on `(Ω, ℱ, P)` at level `α`, `0 < α ≤ 1`:
`𝔸𝕍@ℝ_α(Y) = (1/α) ∫₀^α G⁻¹(u) du`, where `G` is the distribution function of `Y` (its law is
`P.map Y`). This is the *lower-tail* average of a profit variable. The integral is over `(0, α]`;
it is meaningful for integrable `Y` and `0 < α ≤ 1`, which every theorem using it assumes. -/
noncomputable def averageValueAtRisk {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (α : ℝ) : ℝ :=
  (1 / α) * ∫ u in Set.Ioc 0 α, quantileFunction (P.map Y) u

/-- The average value-at-risk deviation (p. 48, (2.16)): `𝔸𝕍@ℝ𝔻_α(Y) = 𝔼Y − 𝔸𝕍@ℝ_α(Y)`. -/
noncomputable def avarDeviation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (α : ℝ) : ℝ :=
  ∫ ω, Y ω ∂P - averageValueAtRisk P Y α

/-- `α⁺_G = inf {G(u) : G(u) ≥ α}` (p. 49), for the law `μ` with distribution function `G`.
The set is nonempty exactly when `G⁻¹(α)` is finite, which every theorem using it assumes;
otherwise `sInf ∅ = 0` is a junk value. -/
noncomputable def alphaPlus (μ : Measure ℝ) (α : ℝ) : ℝ :=
  sInf (distributionFunction μ '' {u : ℝ | α ≤ distributionFunction μ u})

/-- `α⁻_G = sup {G(u) : G(u) < α}` (p. 49), for the law `μ` with distribution function `G`.
For a probability law and `α > 0` the set is nonempty (`G(u) → 0` as `u → -∞`) and bounded
above by `α`. -/
noncomputable def alphaMinus (μ : Measure ℝ) (α : ℝ) : ℝ :=
  sSup (distributionFunction μ '' {u : ℝ | distributionFunction μ u < α})

end RiskFunctionals.AVaR


