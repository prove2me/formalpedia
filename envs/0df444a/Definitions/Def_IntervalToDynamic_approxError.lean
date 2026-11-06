-- Prove2me | Definitions.Def_IntervalToDynamic_approxError
-- name    : IntervalToDynamic_approxError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:48.211119+00:00
-- url     : https://prove2.me/theorems/7fa954cf-d95f-431c-aa3b-2f52669b51fb
-- title:
--   Eq. (5): the interval-to-dynamic approximation error
-- statement:
--   For an interval $I=[a,b]$, a comparator $z$ and a dynamic comparator sequence $u_t$,
--   $$
--   \text{Err}_I(z)=\sum_{t\in I}h_t(z)-\sum_{t\in I}h_t(u_t).
--   $$
--
--   Interval regret and approximation error add up to the dynamic regret on $I$.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Eq. (5), p.5

import Mathlib

namespace IntervalToDynamic

/-- The interval-to-dynamic approximation error on `I = [a, b]`. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Eq. (5), p.5:
`Err_I(z_I) = ∑_{t ∈ I} f_t(z_I) − ∑_{t ∈ I} f_t(u_t)`. -/
def approxError {E : Type*} (h : ℕ → E → ℝ) (u : ℕ → E) (a b : ℕ) (z : E) : ℝ :=
  ∑ t ∈ Finset.Icc a b, (h t z - h t (u t))

end IntervalToDynamic


