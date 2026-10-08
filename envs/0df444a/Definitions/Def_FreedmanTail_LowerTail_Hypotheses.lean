-- Prove2me | Definitions.Def_FreedmanTail_LowerTail_Hypotheses
-- name    : FreedmanTail_LowerTail_Hypotheses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:51:12.706983+00:00
-- url     : https://prove2.me/theorems/671efae1-0f44-494a-a764-12e837549630
-- title:
--   Hypotheses (4.11a)–(4.11b) and (4.12a)–(4.12c) of Proposition (4.10)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $W$ a real random variable and $a$ a real number. With $e$ and $f$ as in Definition (1.2):
--
--   1. **Upper Laplace bound (4.11a).** $W$ satisfies, for every $\lambda\ge 0$,
--   $$
--   E\{\exp[-e(\lambda)W]\}\le \exp(-\lambda a).
--   $$
--   2. **Lower Laplace bound (4.11b).** $W$ satisfies, for every $\lambda\ge 0$,
--   $$
--   E\{\exp[-f(\lambda)W]\}\ge \exp(-\lambda(a+1)).
--   $$
--   3. **Parameter conditions (4.12).** The reals $\delta,a,b$ are positive and
--   $$
--   \delta<\tfrac13,\qquad \frac ba>\frac{9}{\delta^2},\qquad \frac{a^2}{b}>\frac{16}{\delta^2}\log\frac{64}{\delta^2}.
--   $$
--
--   In Freedman's paper $W=W_a$ is the conditional variance a martingale with increments bounded by $1$ uses to cross level $a$; for that variable (4.11a) and (4.11b) are Theorems (1.12) and (1.8). Proposition (4.10) isolates the analytic step: any nonnegative variable with these two Laplace-transform bounds has a lower bound on $P\{W<b\}$.
--
--   **Formalization Note** The expectations are Bochner integrals with respect to $P$. For $\lambda\ge0$ and $W\ge0$ both integrands take values in $(0,1]$, so they are integrable whenever $W$ is measurable and the integrals are genuine expectations (no default value $0$ enters). The three conditions are separate `Prop`s so that each milestone can assume exactly the ones its statement needs.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 109 (PDF p. 10), (4.10) Proposition, displays (4.11a), (4.11b), (4.12a)–(4.12c)

import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.11a), p. 109: for every `λ ≥ 0`,
`E{exp[−e(λ)W]} ≤ exp(−λa)`. For `λ ≥ 0` and `W ≥ 0` the integrand lies in `(0, 1]`,
so the Bochner integral is a genuine expectation. -/
def LaplaceUpper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : Ω → ℝ) (a : ℝ) : Prop :=
  ∀ lam : ℝ, 0 ≤ lam → ∫ ω, Real.exp (-(e lam * W ω)) ∂P ≤ Real.exp (-(lam * a))

/-- Freedman (1975), (4.11b), p. 109: for every `λ ≥ 0`,
`E{exp[−f(λ)W]} ≥ exp(−λ(a + 1))`. -/
def LaplaceLower {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : Ω → ℝ) (a : ℝ) : Prop :=
  ∀ lam : ℝ, 0 ≤ lam → Real.exp (-(lam * (a + 1))) ≤ ∫ ω, Real.exp (-(f lam * W ω)) ∂P

/-- Freedman (1975), (4.12a)–(4.12c), p. 109: `δ, a, b` positive with
`δ < 1/3`, `b/a > 9/δ²` and `a²/b > (16/δ²) log(64/δ²)`. -/
def ParamConditions (δ a b : ℝ) : Prop :=
  0 < δ ∧ 0 < a ∧ 0 < b ∧ δ < 1 / 3 ∧ 9 / δ ^ 2 < b / a ∧
    16 / δ ^ 2 * Real.log (64 / δ ^ 2) < a ^ 2 / b

end FreedmanTail.LowerTail


