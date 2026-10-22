-- Prove2me | Definitions.Def_RiskFunctionals_StochDominance_QuantileFunction
-- name    : RiskFunctionals_StochDominance_QuantileFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:54.616183+00:00
-- url     : https://prove2.me/theorems/27f4fe5c-dd7b-4e7b-a0f7-dda5911b654f
-- title:
--   The distribution function $G(u)=\mathbb P\{Y\le u\}$ and the quantile function $G^{-1}(p)=\inf\{u : G(u)\ge p\}$
-- statement:
--   Let $Y$ be a real random variable on a probability space $(\Omega,\mathcal F,\mathbb P)$ and let $\mu$ be its law, the probability measure $\mu(B)=\mathbb P\{Y\in B\}$ on the Borel sets of $\mathbb R$. The file defines the two basic functions of the law.
--
--   1. The **distribution function** of $Y$ is
--   $$G(u) = \mathbb P\{Y \le u\} = \mu\big((-\infty,u]\big), \qquad u\in\mathbb R .$$
--   It is nondecreasing and continuous from the right.
--   2. The **quantile function** is the left-continuous inverse of $G$,
--   $$G^{-1}(p) = \inf\{u : G(u) \ge p\}, \qquad 0 < p \le 1. \tag{1.3}$$
--   For $0<p<1$ the infimum is attained, and it is finite; at $p=1$ it is $+\infty$ when $G(u)<1$ for every $u$.
--
--   These two functions are the objects through which the book describes the law of a single profit variable; every order relation of the chapter is characterized in terms of them.
--
--   **Formalization Note** The functions take the law $\mu$ (a measure on $\mathbb R$) rather than a random variable, since every statement of this chapter depends on $Y$ only through its law. The quantile function is real-valued and computed with `sInf`, which returns the junk value $0$ on an empty or unbounded-below set; the definition itself does not restrict $p$. Every theorem that uses it restricts $p$ to $(0,1)$, or assumes that $\{u : G(u)\ge p\}$ is nonempty, so the junk value (which would stand for the book's $G^{-1}(1)=+\infty$, or for $p\le 0$) never enters a statement.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 6, §1.2.1, Eq. (1.3)

import Mathlib

namespace RiskFunctionals.StochDominance

open MeasureTheory

/-- The distribution function `G(u) = ℙ{Y ≤ u}` (Pflug & Römisch, *Modeling, Measuring and
Managing Risk*, World Scientific 2007, p. 6, §1.2.1), written for the law `μ` of `Y`, a
measure on `ℝ` (a probability measure in every theorem that uses it). -/
noncomputable def distributionFunction (μ : Measure ℝ) (u : ℝ) : ℝ :=
  μ.real (Set.Iic u)

/-- The quantile function (1.3), `G⁻¹(p) = inf {u : G(u) ≥ p}` for `0 < p ≤ 1` (p. 6): the
left-continuous inverse of the distribution function. The book's domain `0 < p ≤ 1` is not
built in; every theorem that uses it restricts `p` to `(0, 1)`, or to a `p` for which the set
`{u : G(u) ≥ p}` is nonempty, so the junk value `sInf ∅ = 0` (the book's `G⁻¹(1) = +∞` when
`G < 1` everywhere) and the value at `p ≤ 0` never enter a statement. -/
noncomputable def quantileFunction (μ : Measure ℝ) (p : ℝ) : ℝ :=
  sInf {u : ℝ | p ≤ distributionFunction μ u}

end RiskFunctionals.StochDominance


