-- Prove2me | Definitions.Def_RiskFunctionals_Deviation_AverageValueAtRisk
-- name    : RiskFunctionals_Deviation_AverageValueAtRisk
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:09.499799+00:00
-- url     : https://prove2.me/theorems/ede995d7-947c-4608-8108-faed91c5e9af
-- title:
--   Quantile function, average value-at-risk $\mathbb{AV@R}_\alpha(Y)=\frac1\alpha\int_0^\alpha G^{-1}(u)\,du$ and its deviation $\mathbb E-\mathbb{AV@R}_\alpha$
-- statement:
--   Let $Y$ be a random variable on a probability space $(\Omega,\mathcal F,\mathbb P)$. The book works with *profit* variables: larger values of $Y$ are better.
--
--   1. The **distribution function** of $Y$ is $G(u)=\mathbb P\{Y\le u\}$, $u\in\mathbb R$.
--   2. The **quantile function** is the left-continuous inverse
--   $$G^{-1}(p)=\inf\{u : G(u)\ge p\},\qquad 0<p\le 1. \tag{1.3}$$
--   3. For $0<\alpha\le 1$ the **average value-at-risk** is the average of the lower $\alpha$-fraction of the quantiles,
--   $$\mathbb{AV@R}_\alpha(Y)=\frac1\alpha\int_0^\alpha G^{-1}(u)\,du. \tag{2.15}$$
--   4. The **average value-at-risk deviation** is
--   $$\mathbb{AV@R}\mathbb D_\alpha(Y)=\mathbb E(Y)-\mathbb{AV@R}_\alpha(Y). \tag{2.16}$$
--
--   These are the objects of the special cases (2.112), (2.114) of the minimal loss functional studied in this mission.
--
--   **Formalization Note** $G$ and $G^{-1}$ are written for the law $\mu$ of $Y$ (the image of $\mathbb P$ under $Y$), so $\mathbb{AV@R}_\alpha(Y)$ depends on $Y$ only through its distribution. $G^{-1}$ is a real-valued infimum (`sInf`), which is the junk value $0$ on an empty or unbounded-below set; it is used only inside the integral over $(0,\alpha]$ with $\alpha\le1$, where the single point $p=1$ (the only one in $(0,1]$ at which the set can be empty) is a null set. The integral is the Lebesgue integral over $(0,\alpha]$ and $1/\alpha$ is $0$ at $\alpha=0$; every theorem using these assumes $Y$ measurable and integrable and $0<\alpha\le 1$. The same definitions are drafted in mission III of this series; drafts cannot import one another, so they are restated in this mission's namespace.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 6, Eq. (1.3); p. 48, Definition 2.33, Eqs. (2.15)–(2.16)

import Mathlib

namespace RiskFunctionals.Deviation

open MeasureTheory

/-- The distribution function `G(u) = ℙ{Y ≤ u}` (Pflug & Römisch, *Modeling, Measuring and
Managing Risk*, World Scientific 2007, p. 6, §1.2.1), written for the law `μ` of `Y`, a
measure on `ℝ` (a probability measure in every theorem that uses it). -/
noncomputable def distributionFunction (μ : Measure ℝ) (u : ℝ) : ℝ :=
  μ.real (Set.Iic u)

/-- The quantile function (1.3), `G⁻¹(p) = inf {u : G(u) ≥ p}` for `0 < p ≤ 1` (p. 6): the
left-continuous inverse of the distribution function. The book's domain `0 < p ≤ 1` is not
built in; `sInf` returns the junk value `0` on an empty or unbounded-below set. It is only used
here inside the integral over `(0, α]`, `α ≤ 1`, where the point `p = 1` is a null set. -/
noncomputable def quantileFunction (μ : Measure ℝ) (p : ℝ) : ℝ :=
  sInf {u : ℝ | p ≤ distributionFunction μ u}

/-- The average value-at-risk (p. 48, Definition 2.33, (2.15)) of a random variable `Y` on
`(Ω, ℱ, P)` at level `α`, `0 < α ≤ 1`: `𝔸𝕍@ℝ_α(Y) = (1/α) ∫₀^α G⁻¹(u) du`, where `G` is the
distribution function of `Y` (its law is `P.map Y`). This is the *lower-tail* average of a profit
variable. The integral is over `(0, α]`; it is meaningful for integrable `Y` and `0 < α ≤ 1`,
which every theorem using it assumes. -/
noncomputable def averageValueAtRisk {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (α : ℝ) : ℝ :=
  (1 / α) * ∫ u in Set.Ioc 0 α, quantileFunction (P.map Y) u

/-- The average value-at-risk deviation (p. 48, (2.16)): `𝔸𝕍@ℝ𝔻_α(Y) = 𝔼Y − 𝔸𝕍@ℝ_α(Y)`. -/
noncomputable def avarDeviation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (α : ℝ) : ℝ :=
  ∫ ω, Y ω ∂P - averageValueAtRisk P Y α

end RiskFunctionals.Deviation


