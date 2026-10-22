-- Prove2me | Definitions.Def_RiskFunctionals_Kusuoka_AverageValueAtRisk
-- name    : RiskFunctionals_Kusuoka_AverageValueAtRisk
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:55.719748+00:00
-- url     : https://prove2.me/theorems/f1e89093-2c74-4137-955d-0cd2a34cab62
-- title:
--   Distribution function, quantile function $G^{-1}$, average value-at-risk $\mathbb{AV@R}_\alpha$ and $\mathbb{M}\mathrm{ad}$
-- statement:
--   Let $Y$ be a real random variable on a probability space $(\Omega,\mathcal F,\mathbb P)$ with law $\mu=\mathbb P\circ Y^{-1}$.
--
--   1. The **distribution function** is $G(u)=\mathbb P\{Y\le u\}=\mu((-\infty,u])$, $u\in\mathbb R$.
--   2. The **quantile function** is the left-continuous inverse
--   $$G^{-1}(p)=\inf\{u\in\mathbb R : G(u)\ge p\},\qquad 0<p\le 1. \tag{1.3}$$
--   3. The **average value-at-risk** at level $\alpha$, $0<\alpha\le1$, is the lower-tail average of the quantiles
--   $$\mathbb{AV@R}_\alpha(Y)=\frac1\alpha\int_0^\alpha G^{-1}(u)\,du. \tag{2.15}$$
--   4. The **mean absolute deviation** is $\mathbb{M}\mathrm{ad}(Y)=\mathbb E\big[|Y-\mathbb EY|\big]$ (2.83).
--
--   The book works with profit variables (larger is better), so $\mathbb{AV@R}_\alpha$ averages the *lowest* $\alpha$-fraction of outcomes; $\mathbb{AV@R}_1(Y)=\mathbb E Y$. These are the building blocks of the Kusuoka and Choquet representations of version-independent acceptability functionals.
--
--   **Formalization Note** $G$ is computed from the pushforward measure $\mathbb P\circ Y^{-1}$ on $\mathbb R$. The quantile function is the infimum of a set of reals; for a probability law and $0<p<1$ this set is nonempty and bounded below, so the value is the book's. Outside $(0,1)$ (and at $p=1$ when $G<1$ everywhere, where the book's value is $+\infty$) Lean's infimum returns a default value; every statement of this mission evaluates $G^{-1}$ only on $(0,1)$ or inside an integral over $(0,\alpha]$, where the single point $p=1$ is a null set. The integral in (2.15) is over $(0,\alpha]$. $\mathbb{AV@R}_\alpha$ is meaningful for $0<\alpha\le1$ and integrable $Y$; at $\alpha=0$ the definition returns $0$, a value no statement uses.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 6, Eq. (1.3); p. 48, Definition 2.33, Eq. (2.15); p. 95, Eq. (2.83)

import Mathlib

namespace RiskFunctionals.Kusuoka

open MeasureTheory

/-- The distribution function `G(u) = ℙ{Y ≤ u}` (Pflug & Römisch, *Modeling, Measuring and
Managing Risk*, World Scientific 2007, p. 6, §1.2.1), written for the law `μ` of `Y`, a
measure on `ℝ` (a probability measure in every theorem that uses it). -/
noncomputable def distributionFunction (μ : Measure ℝ) (u : ℝ) : ℝ :=
  μ.real (Set.Iic u)

/-- The quantile function (1.3), `G⁻¹(p) = inf {u : G(u) ≥ p}` for `0 < p ≤ 1` (p. 6): the
left-continuous inverse of the distribution function. The book's domain `0 < p ≤ 1` is not
built in: for a probability law and `0 < p < 1` the set is nonempty and bounded below, so the
value is the book's; outside `(0, 1)` (and at `p = 1` when `G < 1` everywhere) `sInf` returns a
junk value. Every theorem of this mission evaluates it only on `(0, 1)` or inside an integral
over `(0, α]`, where `p = 1` is a null set. -/
noncomputable def quantileFunction (μ : Measure ℝ) (p : ℝ) : ℝ :=
  sInf {u : ℝ | p ≤ distributionFunction μ u}

/-- The average value-at-risk (p. 48, Definition 2.33, (2.15)) of a random variable `Y` on
`(Ω, ℱ, P)` at level `α`, `0 < α ≤ 1`: `𝔸𝕍@ℝ_α(Y) = (1/α) ∫₀^α G⁻¹(u) du`, where `G` is the
distribution function of `Y` (its law is `P.map Y`). This is the *lower-tail* average of a
profit variable. The integral is over `(0, α]`. It is the book's value for integrable `Y` and
`0 < α ≤ 1`, which every theorem using it assumes; at `α = 0` it is the junk value `0`. -/
noncomputable def averageValueAtRisk {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (α : ℝ) : ℝ :=
  (1 / α) * ∫ u in Set.Ioc 0 α, quantileFunction (P.map Y) u

/-- The mean absolute deviation (p. 95, (2.83)): `𝕄ad(Y) = 𝔼[|Y − 𝔼Y|]`. -/
noncomputable def meanAbsoluteDeviation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) : ℝ :=
  ∫ ω, |Y ω - ∫ ω', Y ω' ∂P| ∂P

end RiskFunctionals.Kusuoka


