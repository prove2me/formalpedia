-- Prove2me | Definitions.Def_SennottDP_ResidualLife_Distributions
-- name    : SennottDP_ResidualLife_Distributions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T10:13:18.238949+00:00
-- url     : https://prove2.me/theorems/b1c8c81f-1d9e-4adb-a28a-f02f2ad2487a
-- title:
--   Geometric, negative binomial (number of trials) and truncated Poisson distributions on {1,2,…}
-- statement:
--   Three distributions on the positive integers, as used in Section 9.2.
--
--   1. **Geometric** $\mathrm{geo}(\mu)$: the number $Y$ of independent Bernoulli trials with success probability $\mu$ up to and including the first success,
--   $$P(Y=y) = \mu(1-\mu)^{y-1}, \qquad y \ge 1,$$
--   so that $F^*(y) = (1-\mu)^y$.
--   2. **Negative binomial** $\mathrm{neg\,bin}(\mu, r)$: the number $Y$ of independent Bernoulli trials with success probability $\mu$ until exactly $r$ successes are achieved,
--   $$P(Y=y) = \binom{y-1}{r-1}\mu^r(1-\mu)^{y-r}, \qquad y \ge r,$$
--   and $P(Y = y) = 0$ for $y < r$. For $r = 1$ it is the geometric distribution.
--   3. **Truncated Poisson** $\mathrm{trun\,Pois}(\lambda)$: a Poisson($\lambda$) variable conditioned to be positive,
--   $$P(Y=y) = \left(\frac{e^{-\lambda}}{1-e^{-\lambda}}\right)\frac{\lambda^y}{y!}, \qquad y \ge 1.$$
--
--   The parameters are intended in the ranges $0 < \mu < 1$, $r \ge 1$, $\lambda > 0$; the results that use these distributions state their parameter range explicitly.
--
--   **Formalization Note** Each distribution is a function $\mathbb N \to [0,\infty]$ (value $0$ below the support), with real parameters $\mu, \lambda$ and the real formula mapped in by `ENNReal.ofReal`. Mathlib's `geometricPMF` counts failures from $0$; the book's geometric counts trials from $1$, which is what is defined here.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), pp. 205–206, proof of Proposition 9.2.6 (geo(μ), neg bin(μ, r)); p. 206, Eq. (9.14) (trun Pois(λ))

import Mathlib

open scoped ENNReal

namespace SennottDP.ResidualLife

/-- Sennott (1999), p. 205: the geometric distribution `geo(μ)` of the number `Y` of independent
Bernoulli trials with success probability `μ` up to and including the first success:
`P(Y = y) = μ (1 - μ)^{y-1}` for `y ≥ 1`, and `0` at `y = 0`. Intended for `0 < μ < 1`. -/
noncomputable def geomTrials (μ : ℝ) (y : ℕ) : ℝ≥0∞ :=
  if 1 ≤ y then ENNReal.ofReal (μ * (1 - μ) ^ (y - 1)) else 0

/-- Sennott (1999), pp. 205–206: the negative binomial distribution `neg bin(μ, r)` of the number
`Y` of independent Bernoulli trials with success probability `μ` until exactly `r` successes are
achieved: `P(Y = y) = C(y-1, r-1) μ^r (1 - μ)^{y-r}` for `y ≥ r`, and `0` for `y < r`.
Intended for `0 < μ < 1` and `r ≥ 1`. -/
noncomputable def negBinTrials (μ : ℝ) (r : ℕ) (y : ℕ) : ℝ≥0∞ :=
  if r ≤ y then ENNReal.ofReal ((Nat.choose (y - 1) (r - 1) : ℝ) * μ ^ r * (1 - μ) ^ (y - r))
  else 0

/-- Sennott (1999), (9.1) and (9.14), p. 206: the truncated Poisson distribution `trun Pois(λ)`,
`P(Y = y) = (e^{-λ} / (1 - e^{-λ})) λ^y / y!` for `y ≥ 1`, and `0` at `y = 0`.
Intended for `λ > 0`. -/
noncomputable def truncPoisson (lam : ℝ) (y : ℕ) : ℝ≥0∞ :=
  if 1 ≤ y then
    ENNReal.ofReal (Real.exp (-lam) / (1 - Real.exp (-lam)) * lam ^ y / (y.factorial : ℝ))
  else 0

end SennottDP.ResidualLife


