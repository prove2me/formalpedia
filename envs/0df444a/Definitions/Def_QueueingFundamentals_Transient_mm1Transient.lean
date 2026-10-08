-- Prove2me | Definitions.Def_QueueingFundamentals_Transient_mm1Transient
-- name    : QueueingFundamentals_Transient_mm1Transient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T07:49:31.331241+00:00
-- url     : https://prove2.me/theorems/574bee2b-338e-4a5f-879a-82f0f475f2a3
-- title:
--   The Bessel-function expression (2.75) for the transient M/M/1 probabilities
-- statement:
--   Let $\lambda, \mu > 0$ be the arrival and service rates of the M/M/1 queue, $\rho = \lambda/\mu$, and $i \ge 0$ the initial number in the system. For $n \ge 0$ and $t \ge 0$ put $y = 2t\sqrt{\lambda\mu}$ and
--
--   $$
--   p_n(t) = e^{-(\lambda+\mu)t}\Big[\rho^{(n-i)/2} I_{n-i}(y) + \rho^{(n-i-1)/2} I_{n+i+1}(y) + (1-\rho)\rho^n \sum_{j=n+i+2}^{\infty} \rho^{-j/2} I_j(y)\Big],
--   $$
--
--   where $I_m$ is the modified Bessel function of the first kind (with $I_{-m} = I_m$).
--
--   This is the right-hand side of the book's formula (2.75); the goal theorem of the mission asserts that it is the transient law of the M/M/1 queue started with $i$ customers.
--
--   **Formalization Note** The half-integer powers of $\rho$ are real powers (`Real.rpow`), well defined because $\rho > 0$ whenever $\lambda > 0$. The infinite sum is a `tsum` indexed by $j - (n+i+2) \in \mathbb N$; its convergence is part of the goal theorem.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.100, Eq. (2.75)

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_besselI

namespace QueueingFundamentals.Transient

/-- The right-hand side of (2.75): the probability that the M/M/1 queue started with `N(0) = i`
has `n` customers at time `t`, with `ρ = λ/μ` and `y = 2t√(λμ)`:
`p_n(t) = e^{-(λ+μ)t} [ ρ^{(n-i)/2} I_{n-i}(y) + ρ^{(n-i-1)/2} I_{n+i+1}(y)
  + (1-ρ) ρ^n ∑_{j ≥ n+i+2} ρ^{-j/2} I_j(y) ]`.
Powers of `ρ` with half-integer exponents are real powers (`ρ > 0` when `λ > 0`), and
`I_{n-i}` uses `I_{-m} = I_m`. -/
noncomputable def mm1Transient (lam mu : ℝ) (i n : ℕ) (t : ℝ) : ℝ :=
  let ρ : ℝ := lam / mu
  let y : ℝ := 2 * t * Real.sqrt (lam * mu)
  Real.exp (-(lam + mu) * t) *
    (ρ ^ (((n : ℝ) - (i : ℝ)) / 2) * besselIZ ((n : ℤ) - (i : ℤ)) y
      + ρ ^ (((n : ℝ) - (i : ℝ) - 1) / 2) * besselI (n + i + 1) y
      + (1 - ρ) * ρ ^ n *
          ∑' j : ℕ, ρ ^ (-(((j + n + i + 2 : ℕ) : ℝ)) / 2) * besselI (j + n + i + 2) y)

end QueueingFundamentals.Transient


