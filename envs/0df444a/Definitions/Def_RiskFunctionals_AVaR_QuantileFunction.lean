-- Prove2me | Definitions.Def_RiskFunctionals_AVaR_QuantileFunction
-- name    : RiskFunctionals_AVaR_QuantileFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:49.882864+00:00
-- url     : https://prove2.me/theorems/e1bda86e-e0f2-4d1f-a5cb-70a32bab8289
-- title:
--   The distribution function $G(u)=\mathbb P\{Y\le u\}$ and the quantile function $G^{-1}(p)=\inf\{u : G(u)\ge p\}$
-- statement:
--   Let $Y$ be a real random variable on a probability space $(\Omega,\mathcal F,\mathbb P)$ and let $\mu$ be its law, the probability measure $\mu(B)=\mathbb P\{Y\in B\}$ on the Borel sets of $\mathbb R$. The file defines the two basic functions of the law.
--
--   1. The **distribution function** of $Y$ is
--   $$G(u) = \mathbb P\{Y \le u\} = \mu\big((-\infty,u]\big), \qquad u\in\mathbb R .$$
--   2. The **quantile function** is the left-continuous inverse of $G$,
--   $$G^{-1}(p) = \inf\{u : G(u) \ge p\}, \qquad 0 < p \le 1. \tag{1.3}$$
--   For $0<p<1$ the infimum is attained and finite; at $p=1$ it is $+\infty$ when $G(u)<1$ for every $u$.
--
--   The average value-at-risk of this mission is an average of $G^{-1}$, and several of its representations evaluate $G$ at the quantile $G^{-1}(\alpha)$.
--
--   **Formalization Note** The functions take the law $\mu$ (a measure on $\mathbb R$) rather than a random variable; for a random variable $Y$ the law is the image measure of $\mathbb P$ under $Y$. The quantile function is real-valued and computed with `sInf`, which returns the junk value $0$ on an empty or unbounded-below set; the definition itself does not restrict $p$. Every theorem that evaluates it at a point $p=\alpha$ assumes that $\{u : G(u)\ge\alpha\}$ is nonempty (automatic for $\alpha<1$), and inside an integral over $(0,\alpha]$ the single point $p=1$ does not matter. The same two functions are defined in mission I of this series; drafts cannot import one another, so they are restated here.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 6, §1.2.1, Eq. (1.3)

import Mathlib

namespace RiskFunctionals.AVaR

open MeasureTheory

/-- The distribution function `G(u) = ℙ{Y ≤ u}` (Pflug & Römisch, *Modeling, Measuring and
Managing Risk*, World Scientific 2007, p. 6, §1.2.1), written for the law `μ` of `Y`, a
measure on `ℝ` (a probability measure in every theorem that uses it). -/
noncomputable def distributionFunction (μ : Measure ℝ) (u : ℝ) : ℝ :=
  μ.real (Set.Iic u)

/-- The quantile function (1.3), `G⁻¹(p) = inf {u : G(u) ≥ p}` for `0 < p ≤ 1` (p. 6): the
left-continuous inverse of the distribution function. The book's domain `0 < p ≤ 1` is not
built in. For a probability law and `0 < p < 1` the set is nonempty and bounded below; at
`p = 1` it is empty exactly when `G < 1` everywhere (the book's `G⁻¹(1) = +∞`), and then `sInf`
returns the junk value `0`. Every theorem that evaluates it at a single point assumes that the
set is nonempty; inside an integral over `(0, α]` the point `p = 1` is a null set. -/
noncomputable def quantileFunction (μ : Measure ℝ) (p : ℝ) : ℝ :=
  sInf {u : ℝ | p ≤ distributionFunction μ u}

end RiskFunctionals.AVaR


