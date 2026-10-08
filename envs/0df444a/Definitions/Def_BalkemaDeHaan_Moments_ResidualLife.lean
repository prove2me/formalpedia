-- Prove2me | Definitions.Def_BalkemaDeHaan_Moments_ResidualLife
-- name    : BalkemaDeHaan_Moments_ResidualLife
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:25.002988+00:00
-- url     : https://prove2.me/theorems/e6e7ffa7-eb1d-4c1c-83d6-76b68528c9b3
-- title:
--   The tail $R$, the conditional d.f. $P\{X/t \le x \mid X > t\}$ and the conditional moment $E((X/t)^\xi \mid X > t)$
-- statement:
--   Let $X$ be a real random variable with law $\mu$ (a probability measure on $\mathbb R$) and distribution function $F$. Three objects are defined from $\mu$.
--
--   1. The **tail** $R(x) = 1 - F(x) = P\{X > x\} = \mu((x,\infty))$.
--   2. For $t > 0$, the **conditional distribution function of $X/t$ given $X > t$**,
--   $$
--   P\{X/t \le x \mid X > t\} = \frac{\mu((t, xt])}{\mu((t,\infty))}.
--   $$
--   It is $0$ for $x \le 1$, because the interval $(t, xt]$ is then empty.
--   3. For $t > 0$ and a real exponent $\xi$, the **conditional $\xi$-th moment of $X/t$ given $X > t$**,
--   $$
--   E\Big(\Big(\frac{X}{t}\Big)^{\xi} \,\Big|\, X > t\Big) = \frac{1}{\mu((t,\infty))}\int_{(t,\infty)} \Big(\frac{y}{t}\Big)^{\xi}\, \mu(dy).
--   $$
--
--   These are the quantities in which Balkema and de Haan state the moment characterization of the domain of residual life time attraction of $\Gamma_\alpha$ (Theorem 8(a)).
--
--   **Formalization Note** The quotients are meaningful only when $\mu((t,\infty)) > 0$ (Lean's real division returns $0$ when dividing by $0$); every statement that uses them assumes $F(x) < 1$ for all $x$, the paper's standing assumption. The integral is a Bochner integral, which Lean sets to $0$ for a non-integrable integrand; every statement that uses the moment asserts or assumes the integrability it needs. Only $t > 0$ is relevant (all statements are about $t \to \infty$), where the base $y/t$ of the real power is positive on $(t,\infty)$.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 803 (PDF p. 12), Theorem 8(a); tail R(x) from §1, p. 793 (PDF p. 2)

import Mathlib
import Definitions.Def_BalkemaDeHaan_LimitTypes_ResidualLife

namespace BalkemaDeHaan.Moments

open MeasureTheory

/-- The conditional distribution function of `X / t` given `X > t` (Theorem 8(a), p. 803):
`P{X/t ≤ x | X > t} = P{t < X ≤ x t} / P{X > t}` for `t > 0`. The quotient is meaningful only when
`P{X > t} > 0`; every statement using it assumes `F(x) < 1` for all `x`. -/
noncomputable def scaledResidualCDF (μ : Measure ℝ) (t x : ℝ) : ℝ :=
  (μ (Set.Ioc t (x * t))).toReal / (μ (Set.Ioi t)).toReal

/-- The conditional moment `E((X/t)^ξ | X > t) = (∫_{(t,∞)} (y/t)^ξ dF(y)) / P{X > t}`
(Theorem 8(a), p. 803), for `t > 0` (so that the base `y / t` of the real power is positive on the
domain of integration). The integral is a Bochner integral: it is meaningful only when the integrand
is integrable, which the statements using it assert or assume explicitly. -/
noncomputable def condMoment (μ : Measure ℝ) (ξ t : ℝ) : ℝ :=
  (∫ y in Set.Ioi t, (y / t) ^ ξ ∂μ) / (μ (Set.Ioi t)).toReal

end BalkemaDeHaan.Moments


