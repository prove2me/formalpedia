-- Prove2me | Definitions.Def_SaglamGV_Analytic
-- name    : SaglamGV_Analytic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:46:12.6222+00:00
-- url     : https://prove2.me/theorems/369e27b3-31f6-4375-b7fd-aeb2d9a3f5f3
-- title:
--   The functions $s(z)=\sinh z-z$ and $\gamma(\rho)$
-- statement:
--   Two real functions used in the transition estimate:
--
--   $$
--   s(z)=\sinh z-z,
--   \qquad
--   \gamma(\rho)=-\frac\rho2\lg\rho-2(1-\rho)\lg(1-\rho)-1+\Big(1-\frac{3\rho}2\Big)\lg(2-3\rho),
--   $$
--
--   with $\lg=\log_2$. The function $s$ collects the odd terms of index at least $3$ of the exponential series; $\gamma$ is the exponent gain in the third-moment bound for polynomials of degree at most $w=\rho n$.
--
--   **Formalization Note** `sMinus z := Real.sinh z - z`; `gammaKS ρ` with `Real.logb 2`. The formula for $\gamma$ is meaningful for $0<\rho<2/3$; the statements use $0<\rho<1/2$.
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §3.3, p.4 (s); Appendix A, p.6 (γ)

import Mathlib

namespace SaglamGV

/-- `s(z) = sinh z − z` (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027
submission manuscript (held version, sha256 ac6f2bba…), §3.3, p.4: "Set s(z) := sinh z − z"). -/
noncomputable def sMinus (z : ℝ) : ℝ := Real.sinh z - z

/-- The exponent `γ(ρ) = −(ρ/2) lg ρ − 2(1 − ρ) lg(1 − ρ) − 1 + (1 − 3ρ/2) lg(2 − 3ρ)` of the
third-moment bound (Saglam, Appendix A, p.6).

**Formalization Note** `lg` is `Real.logb 2`. The formula is meaningful for `0 < ρ < 2/3`; Lean's
`logb` returns `0` at `0` and uses `|x|` for negative `x`, values the statements never use (they take
`0 < ρ < 1/2`). -/
noncomputable def gammaKS (ρ : ℝ) : ℝ :=
  -(ρ / 2) * Real.logb 2 ρ - 2 * (1 - ρ) * Real.logb 2 (1 - ρ) - 1
    + (1 - 3 * ρ / 2) * Real.logb 2 (2 - 3 * ρ)

end SaglamGV


