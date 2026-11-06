-- Prove2me | Definitions.Def_ReserveLB_effSizeLaw
-- name    : ReserveLB_effSizeLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:59.958291+00:00
-- url     : https://prove2.me/theorems/a4ab500a-b98c-4a5f-89e5-f40419d5b9e4
-- title:
--   Effective size $\beta_b$ under a listed law
-- statement:
--   For an integer base $b > 1$ and a random variable $Z$, the **effective size** is
--   $$
--   \beta_b(Z) = \frac{\ln \mathbb E\, b^{Z}}{\ln b},
--   $$
--   and $\beta_1(Z) = \mathbb E Z$. Here $Z = g(X)$ for a size $X$ with a listed finite law.
--
--   Effective sizes are the risk coefficients $v_{jq}$ and $w_{jqrh}$ of the system (4).
--
--   **Formalization Note** $b^z$ is written $e^{(\ln b) z}$, as in the platform definition `StochLoadBal.Makespan.effSize`, with which this finite formula agrees on the law's measure.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 2.2, p.4

import Mathlib
import Definitions.Def_ReserveLB_lawExpect

namespace ReserveLB

/-- **Effective size `β_b` under a listed law.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 2.2, p.4: "For integer b > 1, write βb(Z) = ln E b^Z / ln b, and set
β1(Z) = EZ."

For a listed law `μ` of `X`, a base `b` and a function `g`, `effSizeLaw μ b g = β_b(g(X))`:
`E g(X)` if `b = 1`, and `ln E[b^(g(X))] / ln b` otherwise.

**Formalization Note.** `b^z` is written `exp(ln b · z)`, as in the platform's
`StochLoadBal.Makespan.effSize`, with which it agrees on the law's measure. Only bases `b ≥ 1`
occur. -/
noncomputable def effSizeLaw (μ : List (ℚ × ℚ)) (b : ℕ) (g : ℝ → ℝ) : ℝ :=
  if b = 1 then lawExpect μ g
  else Real.log (lawExpect μ fun x => Real.exp (Real.log b * g x)) / Real.log b

end ReserveLB


