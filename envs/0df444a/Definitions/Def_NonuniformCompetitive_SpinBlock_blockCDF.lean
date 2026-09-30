-- Prove2me | Definitions.Def_NonuniformCompetitive_SpinBlock_blockCDF
-- name    : NonuniformCompetitive_SpinBlock_blockCDF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:51:23.731888+00:00
-- url     : https://prove2.me/theorems/0436e769-ffda-4152-87de-7086078f763e
-- title:
--   The blocking-time distribution $\pi(t)=(e^{t/C}-1)/(e-1)$ of the randomized spin-block algorithm
-- statement:
--   The randomized spin-block algorithm of Karlin, Manasse, McGeoch and Owicki blocks at a random time whose cumulative distribution is
--   $$\pi(t)=\begin{cases}\dfrac{e^{t/C}-1}{e-1}, & 0\le t\le C,\\[1ex] 1, & t>C,\end{cases}$$
--   where $C>0$ is the context-switch cost and $\pi(t)$ is the probability that the algorithm blocks sometime before time $t$. The function increases continuously from $\pi(0)=0$ to $\pi(C)=1$.
--
--   It is the distribution that attains the optimal competitive factor $e/(e-1)$ in Theorem 10.
--
--   **Formalization Note** The definition is a real function of $(C,t)$; only its values for $t\ge0$ are meaningful, and for $t<0$ the first branch is used (these values are never evaluated by the mission's statements). The denominator $e-1$ is positive.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), pp. 559–560, proof of Theorem 10, display for π(t)

import Mathlib

namespace NonuniformCompetitive.SpinBlock

/-- The cumulative distribution `π(t)` of the blocking time of the paper's randomized spin-block
algorithm (§4.1, pp. 559–560): `π(t) = (e^{t/C} − 1)/(e − 1)` for `0 ≤ t ≤ C` and `π(t) = 1` for
`t > C`, where `π(t)` is the probability that the algorithm blocks sometime before time `t`.
Only its values at `t ≥ 0` are meaningful; for `t < 0` the first branch is used. -/
noncomputable def blockCDF (C t : ℝ) : ℝ :=
  if t ≤ C then (Real.exp (t / C) - 1) / (Real.exp 1 - 1) else 1

end NonuniformCompetitive.SpinBlock


