-- Prove2me | Definitions.Def_JailletLu_R
-- name    : JailletLu_R
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:26:25.264215+00:00
-- url     : https://prove2.me/theorems/2d8f48bb-d7c7-4fbc-84f3-a049cc6eea73
-- title:
--   The function $R(f,\beta,s)$
-- statement:
--   For reals $f,\beta,s$, with $e$ Euler's number,
--   $$
--   R(f,\beta,s)=\frac1f\Big(1-e^{-f}+\frac1e\,\frac{s}{\beta}\,g(f,\beta)-\frac1{2e}\big(e^{-1}(s-\beta)+g(1,\beta)\big)^2+\frac1{2e}\,g(f,\beta)^2\Big).
--   $$
--   It is the lower bound for the per-advertiser ratio in terms of the three numbers $f_a$, $\beta_a$, $s_a$; Claim 4 bounds it below by $0.706$.
--
--   **Formalization Note** Lean reads $1/0$ and $s/0$ as $0$; the theorems using $R$ assume $f>0$ and, for Claim 4, $\beta=0\Rightarrow s=0$.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15, last display

import Mathlib
import Definitions.Def_JailletLu_g

namespace JailletLu

/-- **The function `R(f, β, s)`.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15, last display:
"(1/f_a)(1 − e^{−f_a} + (1/e)(s_a/β_a) g(f_a, β_a) − (1/(2e))(e^{−1}(s_a − β_a) + g(1, β_a))² +
(1/(2e)) g(f_a, β_a)²) ≜ R(f_a, β_a, s_a)".

**Formalization Note.** `e = Real.exp 1`. Divisions by `f = 0` or `β = 0` give Lean's `0`; the
theorems using `R` assume `0 < f` and (for Claim 4) `β = 0 → s = 0`. -/
noncomputable def R (f β s : ℝ) : ℝ :=
  (1 / f) * (1 - Real.exp (-f) + (1 / Real.exp 1) * (s / β) * g f β
    - (1 / (2 * Real.exp 1)) * (Real.exp (-1) * (s - β) + g 1 β) ^ 2
    + (1 / (2 * Real.exp 1)) * g f β ^ 2)

end JailletLu


