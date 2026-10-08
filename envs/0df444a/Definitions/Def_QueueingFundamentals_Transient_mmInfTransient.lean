-- Prove2me | Definitions.Def_QueueingFundamentals_Transient_mmInfTransient
-- name    : QueueingFundamentals_Transient_mmInfTransient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T07:32:26.036911+00:00
-- url     : https://prove2.me/theorems/8c809686-15e3-400e-92fb-83e072a107f6
-- title:
--   The M/M/∞ transient probabilities
-- statement:
--   Let $\lambda, \mu > 0$ be the arrival rate and the per-customer service rate of the M/M/∞ queue. For $n \ge 0$ and $t \ge 0$ put
--
--   $$
--   p_n(t) = \frac{1}{n!}\Big((1-e^{-\mu t})\frac{\lambda}{\mu}\Big)^n \exp\Big(-(1-e^{-\mu t})\frac{\lambda}{\mu}\Big),
--   $$
--
--   a Poisson distribution with mean $(1-e^{-\mu t})\lambda/\mu$. The mission's M/M/∞ milestone asserts that this is the transient law of the M/M/∞ queue started empty.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.101, expansion of Eq. (2.77)

import Mathlib

namespace QueueingFundamentals.Transient

/-- The M/M/∞ transient probabilities of p.101 for `N(0) = 0`:
`p_n(t) = (1/n!) ((1 - e^{-μt}) λ/μ)^n exp(-(1 - e^{-μt}) λ/μ)`. -/
noncomputable def mmInfTransient (lam mu : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((1 - Real.exp (-mu * t)) * (lam / mu)) ^ n / (Nat.factorial n : ℝ)
    * Real.exp (-((1 - Real.exp (-mu * t)) * (lam / mu)))

end QueueingFundamentals.Transient


