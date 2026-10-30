-- Prove2me | Definitions.Def_HighDimProbAudit_Grothendieck_GlobalSeries
-- name    : HighDimProbAudit_Grothendieck_GlobalSeries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:35:20.854858+00:00
-- url     : https://prove2.me/theorems/250e8fd3-b159-4552-843a-c678c1320e4a
-- title:
--   Global power-series representation (3.29)
-- statement:
--   Let $a=(a_k)_{k\ge0}$ be real coefficients and let $f:\mathbb R\to\mathbb R$. A global power-series representation means
--   $$\forall x\in\mathbb R,\qquad \sum_{k=0}^\infty a_kx^k=f(x),$$
--   where the series genuinely converges to the displayed value at every real input. The coefficients are not required to be nonnegative by this definition.
--   This is the shared convention in Exercises 3.7.5(c) and 3.7.6. Lean uses `HasSum`, so a divergent series cannot satisfy the predicate by a default value of `tsum`.
-- source:
--   Vershynin, High-Dimensional Probability: An Introduction with Applications in Data Science, Cambridge University Press, 2018, author-corrected electronic copy dated June 9, 2020, https://doi.org/10.1017/9781108231596, Exercise 3.7.5(c), Eq. (3.29), printed pp. 71–72 (PDF pp. 79–80); Exercise 3.7.6, printed p. 72 (PDF p. 80).

import Mathlib

set_option autoImplicit false

namespace HighDimProbAudit.Grothendieck

/-- One power series about zero, converging to f at every real input, as in (3.29). -/
def GlobalPowerSeries (a : ℕ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, HasSum (fun k : ℕ => a k * x ^ k) (f x)

end HighDimProbAudit.Grothendieck


