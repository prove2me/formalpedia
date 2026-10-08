-- Prove2me | Definitions.Def_QueueingFundamentals_Transient_busyPeriodDensity
-- name    : QueueingFundamentals_Transient_busyPeriodDensity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T07:49:53.538996+00:00
-- url     : https://prove2.me/theorems/1b24a31a-4108-4ea1-af63-b0f6298b26f6
-- title:
--   The M/M/1 busy-period density
-- statement:
--   Let $\lambda, \mu > 0$. For $t > 0$ put
--
--   $$
--   f(t) = \frac{\sqrt{\mu/\lambda}\; e^{-(\lambda+\mu)t}\, I_1(2\sqrt{\lambda\mu}\,t)}{t},
--   $$
--
--   where $I_1$ is the modified Bessel function of the first kind of order one. The book identifies $f$ with the density $p_0'(t)$ of the length of an M/M/1 busy period.
--
--   **Formalization Note** The function is only used on $t > 0$; at $t = 0$ Lean's convention $x/0 = 0$ gives the value $0$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.102, busy-period density (§2.12)

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_besselI

namespace QueueingFundamentals.Transient

/-- The M/M/1 busy-period density of p.102, for `t > 0`:
`f(t) = √(μ/λ) e^{-(λ+μ)t} I₁(2√(λμ) t) / t`. (At `t ≤ 0` the value is irrelevant: every
statement uses it on `(0, ∞)` only; Lean's `x / 0 = 0` makes it `0` at `t = 0`.) -/
noncomputable def busyPeriodDensity (lam mu : ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (mu / lam) * Real.exp (-(lam + mu) * t) * besselI 1 (2 * Real.sqrt (lam * mu) * t) / t

end QueueingFundamentals.Transient


