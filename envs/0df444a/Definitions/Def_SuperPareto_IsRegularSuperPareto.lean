-- Prove2me | Definitions.Def_SuperPareto_IsRegularSuperPareto
-- name    : SuperPareto_IsRegularSuperPareto
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:22.540926+00:00
-- url     : https://prove2.me/theorems/f5860ec7-559a-4cd8-9412-650bd37d7b31
-- title:
--   Definition 1, p.4 — regular super-Pareto random variable
-- statement:
--   A random variable $X$ on a probability space $(\Omega,\mathcal F,P)$ is **regular super-Pareto** if there is one function $f:\mathbb R\to\mathbb R$ that is increasing, convex and non-constant, with
--
--   $$
--   X\overset{d}{=}f(Y),\quad Y\sim\mathrm{Pareto}(1),\qquad f(0)=0,\qquad f(1)>0 .
--   $$
--
--   This is the paper's "Moreover, $X$ is regular if $f(0)=0$ and $f(1)>0$": the same $f$ that represents $X$ as a transform of Pareto(1) must vanish at $0$ and be positive at $1$. Every Pareto law with tail index $\alpha\le1$ is regular. Regularity is the extra hypothesis of part (ii) of the main theorem, where it controls how the tail of $X$ scales.
--
--   **Formalization Note** The same witness $f$ appears in all clauses. Since only the values of $f$ on $[1,\infty)$ affect the law of $f(Y)$, regularity says that this restriction admits an increasing convex extension to $[0,\infty)$ with $f(0)=0$; such an extension extends further to $\mathbb R$ by $0$ on the negative axis, so taking $f:\mathbb R\to\mathbb R$ loses nothing. Pareto(1) is `paretoMeasure 1 1`.
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, Definition 1, p.4

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SuperPareto

/-- **Regular super-Pareto random variable.** Chen, Embrechts, Wang, *An unexpected stochastic
dominance*, arXiv:2208.08471v4, Definition 1, p.4: `X` is super-Pareto, `X =d f(Y)` with `f`
increasing, convex, non-constant and `Y ∼ Pareto(1)`, and moreover `X` is regular if `f(0) = 0` and
`f(1) > 0`.

**Formalization Note.** The *same* `f` witnesses all clauses: the law identity
`P.map X = (paretoMeasure 1 1).map f`, the shape conditions, `f 0 = 0` and `0 < f 1`. The function
`f : ℝ → ℝ` is defined on all of `ℝ` (the paper evaluates `f(0)` but does not state the domain of
`f`; a regular `f` on `[0, ∞)` extends to `ℝ` by `0` on the negative axis, keeping it increasing and
convex). Pareto(1) is Mathlib's `paretoMeasure 1 1`. -/
def IsRegularSuperPareto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  ∃ f : ℝ → ℝ, Monotone f ∧ ConvexOn ℝ Set.univ f ∧ (∃ a b : ℝ, f a ≠ f b) ∧
    P.map X = (paretoMeasure 1 1).map f ∧ f 0 = 0 ∧ 0 < f 1

end SuperPareto


