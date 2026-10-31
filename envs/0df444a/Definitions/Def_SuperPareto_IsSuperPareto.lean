-- Prove2me | Definitions.Def_SuperPareto_IsSuperPareto
-- name    : SuperPareto_IsSuperPareto
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:16.490263+00:00
-- url     : https://prove2.me/theorems/b4137b6f-fec1-4573-ab7d-bd4a4acbf5c8
-- title:
--   Definition 1, p.4 — super-Pareto random variable
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $X$ a real random variable. Write $\mathrm{Pareto}(1)$ for the Pareto distribution with scale $1$ and tail index $1$, so that $Y\sim\mathrm{Pareto}(1)$ satisfies $P(Y>y)=1/y$ for $y\ge 1$.
--
--   $X$ is **super-Pareto** if there is a function $f:\mathbb R\to\mathbb R$ which is
--
--   1. increasing (in the non-strict sense),
--   2. convex,
--   3. non-constant,
--
--   such that $X\overset{d}{=}f(Y)$ for $Y\sim\mathrm{Pareto}(1)$, that is, the law of $X$ equals the image of the Pareto(1) law under $f$.
--
--   Super-Pareto laws are the increasing convex transforms of the Pareto(1) law. They include every Pareto law with tail index $\alpha\le 1$, generalized Pareto laws with $\xi\ge 1$ and Burr laws with $\alpha,\tau\in(0,1]$, and all of them have infinite mean. The class is the hypothesis of the paper's main theorem.
--
--   **Formalization Note** The function $f$ is defined on all of $\mathbb R$ (the paper leaves its domain unstated); an increasing convex function on $[1,\infty)$, the support of Pareto(1), extends to $\mathbb R$ by its value at $1$, and non-constancy on $\mathbb R$ is then equivalent to non-constancy on $[1,\infty)$. Pareto(1) is Mathlib's `paretoMeasure 1 1`, and $X\overset{d}{=}f(Y)$ is `P.map X = (paretoMeasure 1 1).map f`, which forces $X$ to be almost everywhere measurable when $P$ is a probability measure.
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, Definition 1, p.4; Pareto(α) distributions, p.4

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SuperPareto

/-- **Super-Pareto random variable.** Chen, Embrechts, Wang, *An unexpected stochastic dominance*,
arXiv:2208.08471v4, Definition 1, p.4: a random variable `X` is super-Pareto if `X =d f(Y)` for some
increasing, convex and non-constant function `f` and `Y ∼ Pareto(1)`.

Here `X : Ω → ℝ` is a random variable on `(Ω, P)`, Pareto(1) is Mathlib's
`paretoMeasure 1 1` (scale `1`, shape `1`, so `P(Y > y) = 1/y` for `y ≥ 1`), and `X =d f(Y)` is
the equality of laws `P.map X = (paretoMeasure 1 1).map f`.

**Formalization Note.** `f : ℝ → ℝ` is defined on all of `ℝ` (the paper does not state its domain;
an increasing convex function on `[1, ∞)` extends to `ℝ` by the constant `f 1`, and "non-constant on
`ℝ`" is equivalent to "non-constant on `[1, ∞)`" for an increasing convex `f`). "Increasing" is
non-strict (`Monotone`, p.2 of the paper). The equality of laws forces `X` to be a.e.-measurable
whenever `P` is a probability measure. -/
def IsSuperPareto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  ∃ f : ℝ → ℝ, Monotone f ∧ ConvexOn ℝ Set.univ f ∧ (∃ a b : ℝ, f a ≠ f b) ∧
    P.map X = (paretoMeasure 1 1).map f

end SuperPareto


