-- Prove2me | Definitions.Def_RobustMeanCov_OnePoint_twoPointValue
-- name    : RobustMeanCov_OnePoint_twoPointValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:39:02.21899+00:00
-- url     : https://prove2.me/theorems/487bbcfa-2691-4630-952a-b56e1cfe90d5
-- title:
--   The two-point objective $U(p,x)$ of (8)
-- statement:
--   Let $u:\mathbb R\to\mathbb R$, $m\in\mathbb R$, $s\ge 0$ and $p\in(0,1)$. The two-point law $r_p$ with mean $m$ and variance $s^2$ puts mass $p$ on $b(p)=m+\sqrt{(1-p)/p}\,s$ and mass $1-p$ on $a(p)=m-\sqrt{p/(1-p)}\,s$. Its expected utility is
--
--   $$
--   U(p)=p\,u\!\Big(m+\sqrt{\tfrac{1-p}{p}}\,s\Big)+(1-p)\,u\!\Big(m-\sqrt{\tfrac{p}{1-p}}\,s\Big),
--   $$
--
--   which is $U(p,x)$ of display (8) with $\mu_x=m$ and $\sigma_x=s$.
--
--   As $p$ ranges over $(0,1)$ these are all two-point distributions in $\mathbb M_{(m,s^2)}$, so $\inf_{p} U(p)$ is an upper bound on the robust objective (display (7)); Definition 3 and Proposition 7 describe when it is attained in the limit $p\to 0$ or $p\to 1$.
--
--   **Formalization Note** The formula is only used for $p\in(0,1)$: every statement restricts $p$ to the open interval or approaches its endpoints from inside, so Lean's conventions for division by $0$ and square roots of negative numbers never enter.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 101, Proposition 4, (8); two-point laws: p. 101, proof of Proposition 2

import Mathlib

namespace RobustMeanCov.OnePoint

/-- `U(p, x)` of (8) (Popescu 2007, p. 101) with `μ_x = m`, `σ_x = s`: the expected utility
`E[u(r_p)]` of the two-point law with mass `p` at `m + √((1-p)/p)·s` and mass `1 - p` at
`m - √(p/(1-p))·s`. Only meaningful for `p ∈ (0, 1)`; every statement restricts `p` to that
interval or approaches its endpoints from inside. -/
noncomputable def twoPointValue (u : ℝ → ℝ) (m s p : ℝ) : ℝ :=
  p * u (m + Real.sqrt ((1 - p) / p) * s) + (1 - p) * u (m - Real.sqrt (p / (1 - p)) * s)

end RobustMeanCov.OnePoint


