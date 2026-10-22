-- Prove2me | Definitions.Def_RiskFunctionals_Distortion_QuantileFunction
-- name    : RiskFunctionals_Distortion_QuantileFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:41.401551+00:00
-- url     : https://prove2.me/theorems/94b4ca9c-2371-4325-a5a3-4e0592636daa
-- title:
--   The distribution function $G$, its left limit $G(u-)$, the quantile function $G^{-1}$ and $\mathbb{AV@R}_\alpha\{G\}=\frac1\alpha\int_0^\alpha G^{-1}(u)\,du$
-- statement:
--   Let $\mu$ be a probability measure on the Borel sets of $\mathbb R$, the law of a real random variable $Y$ on $(\Omega,\mathcal F,\mathbb P)$. The file defines four functions of the law.
--
--   1. The **distribution function** $G(u)=\mathbb P\{Y\le u\}=\mu\big((-\infty,u]\big)$, $u\in\mathbb R$.
--   2. Its **left limit** $G(u-)=\lim_{v\uparrow u}G(v)=\mathbb P\{Y<u\}=\mu\big((-\infty,u)\big)$.
--   3. The **quantile function**, the left-continuous inverse of $G$,
--   $$G^{-1}(p)=\inf\{u : G(u)\ge p\},\qquad 0<p\le 1. \tag{1.3}$$
--   4. The **average value-at-risk** at level $0<\alpha\le1$, the average of the lower $\alpha$-fraction of the quantiles of a profit variable,
--   $$\mathbb{AV@R}_\alpha\{G\}=\frac1\alpha\int_0^\alpha G^{-1}(u)\,du. \tag{2.15}$$
--
--   The distortion functionals of this mission are integrals of $G^{-1}$ against a distortion measure, and the Choquet representation writes them as mixtures of $\mathbb{AV@R}_\alpha$.
--
--   **Formalization Note** All four functions take the law $\mu$ (a measure on $\mathbb R$); for a random variable $Y$ the law is the image measure of $\mathbb P$ under $Y$. The quantile function is real-valued and computed with `sInf`, which returns the junk value $0$ on an empty or unbounded-below set: at $p=1$ when $G<1$ everywhere (the book's $G^{-1}(1)=+\infty$), and for $p\le 0$ (the book's $G^{-1}(0)=-\infty$). The theorems integrate over $(0,1]$ or $(0,\alpha]$ and exclude a charged point $p=1$ through the domain $\mathcal G_H$. $\mathbb{AV@R}$ integrates over $(0,\alpha]$; at $\alpha=0$ the factor $1/0$ is $0$ in Lean, and no theorem puts mass there. These functions are also defined in other missions of this series; drafts cannot import one another, so they are restated here.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 6, Eq. (1.3); p. 48, Definition 2.33

import Mathlib

namespace RiskFunctionals.Distortion

open MeasureTheory

/-- The distribution function `G(u) = ℙ{Y ≤ u}` (Pflug & Römisch, *Modeling, Measuring and
Managing Risk*, World Scientific 2007, p. 6, §1.2.1), written for the law `μ` of `Y`, a
measure on `ℝ` (a probability measure in every theorem that uses it). -/
noncomputable def distributionFunction (μ : Measure ℝ) (u : ℝ) : ℝ :=
  μ.real (Set.Iic u)

/-- The left limit `G(u−) = lim_{v↑u} G(v) = ℙ{Y < u}` of the distribution function
(p. 81 and p. 86, (2.68)), for the law `μ` of `Y`. -/
noncomputable def distributionFunctionLeft (μ : Measure ℝ) (u : ℝ) : ℝ :=
  μ.real (Set.Iio u)

/-- The quantile function (1.3), `G⁻¹(p) = inf {u : G(u) ≥ p}` for `0 < p ≤ 1` (p. 6): the
left-continuous inverse of the distribution function. The book's domain `0 < p ≤ 1` is not
built in. For a probability law and `0 < p < 1` the set is nonempty and bounded below; at
`p = 1` it is empty exactly when `G < 1` everywhere (the book's `G⁻¹(1) = +∞`), and then `sInf`
returns the junk value `0`; for `p ≤ 0` the set is all of `ℝ` (the book's `G⁻¹(0) = −∞`) and
`sInf` again returns `0`. Every use integrates over `(0, 1]` or evaluates at `0 < p ≤ 1`, and the
distortion domain `InDistortionDomain` excludes the point `p = 1` when it carries mass. -/
noncomputable def quantileFunction (μ : Measure ℝ) (p : ℝ) : ℝ :=
  sInf {u : ℝ | p ≤ distributionFunction μ u}

/-- The average value-at-risk (p. 48, Definition 2.33, (2.15)) of the distribution `G` (law `μ`)
at level `α`, `0 < α ≤ 1`: `𝔸𝕍@ℝ_α{G} = (1/α) ∫₀^α G⁻¹(u) du`, the *lower-tail* average of a
profit variable. The integral is over `(0, α]`. At `α = 0` the factor `1/0 = 0` gives the junk
value `0`; no theorem of this mission puts mass at `α = 0`. -/
noncomputable def averageValueAtRisk (μ : Measure ℝ) (α : ℝ) : ℝ :=
  (1 / α) * ∫ u in Set.Ioc 0 α, quantileFunction μ u

end RiskFunctionals.Distortion


