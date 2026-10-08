-- Prove2me | Definitions.Def_QueueingFundamentals_Transient_besselI
-- name    : QueueingFundamentals_Transient_besselI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T07:32:02.445993+00:00
-- url     : https://prove2.me/theorems/66cd318c-f5a9-4b0b-96b8-7987936b0b48
-- title:
--   Modified Bessel functions of the first kind $I_n$
-- statement:
--   For an integer $n \ge 0$ and real $y$, the **modified Bessel function of the first kind** of order $n$ is given by the series
--
--   $$
--   I_n(y) = \sum_{k=0}^{\infty} \frac{(y/2)^{n+2k}}{k!\,(n+k)!},
--   $$
--
--   which converges for every real $y$. For a negative integer order we use the standard convention $I_{-m}(y) = I_m(y)$ for $m \in \mathbb N$, so that $I_m$ is defined for every $m \in \mathbb Z$.
--
--   These functions express the transient probabilities of the M/M/1 queue, formula (2.75), and the busy-period density of the M/M/1 queue.
--
--   **Formalization Note** `besselI n y` is the series for $n : \mathbb N$; `besselIZ m y` is the integer-order version, defined as `besselI m.natAbs y`. The book states the series "for $n > -1$"; the negative-index convention is needed by (2.75) for the term $I_{n-i}$ when $n < i$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.101, series for I_n(y) following Eq. (2.75)

import Mathlib

namespace QueueingFundamentals.Transient

/-- The modified Bessel function of the first kind of nonnegative integer order `n`, given by the
book's series (p.101): `I_n(y) = ∑_{k ≥ 0} (y/2)^{n+2k} / (k! (n+k)!)`. -/
noncomputable def besselI (n : ℕ) (y : ℝ) : ℝ :=
  ∑' k : ℕ, (y / 2) ^ (n + 2 * k) / ((Nat.factorial k : ℝ) * (Nat.factorial (n + k) : ℝ))

/-- The modified Bessel function of integer order, with the standard convention `I_{-m} = I_m`
for `m ∈ ℕ`; (2.75) needs this for the index `n - i` when `n < i`. -/
noncomputable def besselIZ (m : ℤ) (y : ℝ) : ℝ :=
  besselI m.natAbs y

end QueueingFundamentals.Transient


