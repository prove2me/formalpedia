-- Prove2me | Definitions.Def_BalkemaDeHaan_ParetoBounds_ResidualLife
-- name    : BalkemaDeHaan_ParetoBounds_ResidualLife
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:48:13.880794+00:00
-- url     : https://prove2.me/theorems/05bffa1b-b8b2-417a-a193-63d840e02cb1
-- title:
--   (1) — the residual life distribution $F_t(x) = P\{X - t \le x \mid X > t\}$
-- statement:
--   Let $X$ be a real random variable (a lifetime) with law $\mu$, a probability measure on $\mathbb R$, and let $F$ be its distribution function. For a time $t$ with $P\{X > t\} > 0$, the **residual life distribution function** at age $t$ is the distribution function of the remaining life $X - t$ given survival past $t$:
--
--   $$
--   F_t(x) = P\{X - t \le x \mid X > t\} = \frac{\mu\big((t,\, t + x]\big)}{\mu\big((t, \infty)\big)}, \qquad x \in \mathbb R .
--   $$
--
--   It vanishes for $x < 0$, since then the interval $(t, t+x]$ is empty. Every result of Balkema and de Haan (1974) on the behaviour of the residual life time at great age is a statement about $F_t$; in particular, for $t > 0$ the normed probability of Theorem 6 is $P\{(X - t)/t \le x \mid X > t\} = F_t(xt)$.
--
--   **Formalization Note** Only the law of $X$ matters, so the definition takes the measure $\mu$ and is written with $\mu$ of intervals (as real numbers via `toReal`) rather than with $1 - F$. Lean's division gives $0$ when $\mu((t,\infty)) = 0$; every theorem using this definition carries hypotheses under which $\mu((t,\infty)) > 0$ at the ages concerned.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 792 (PDF p. 1), (1)

import Mathlib

open MeasureTheory

namespace BalkemaDeHaan.ParetoBounds

/-- The residual life distribution function (1) of Balkema–de Haan (1974), p. 792:
for a lifetime `X` with law `μ`, `F_t(x) = P{X - t ≤ x | X > t}
= μ((t, t + x]) / μ((t, ∞))`. It is `0` for `x < 0` (empty interval). -/
noncomputable def residualLife (μ : Measure ℝ) (t x : ℝ) : ℝ :=
  (μ (Set.Ioc t (t + x))).toReal / (μ (Set.Ioi t)).toReal

end BalkemaDeHaan.ParetoBounds


