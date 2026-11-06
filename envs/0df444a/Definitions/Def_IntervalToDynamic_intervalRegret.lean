-- Prove2me | Definitions.Def_IntervalToDynamic_intervalRegret
-- name    : IntervalToDynamic_intervalRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:45.531194+00:00
-- url     : https://prove2.me/theorems/46ae8940-4d9c-46ec-8d80-cb3dc8450e19
-- title:
--   Eq. (1): interval regret
-- statement:
--   For an interval $I=[a,b]$ and a comparator $z$, the interval regret of the decisions $y_t$ on the losses $h_t$ is
--   $$
--   \text{I-Reg}_I(z)=\sum_{t\in I}h_t(y_t)-\sum_{t\in I}h_t(z).
--   $$
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Eq. (1), p.1

import Mathlib

namespace IntervalToDynamic

/-- Interval regret on `I = [a, b]` against the comparator `z`. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Eq. (1), p.1:
`I-Reg_I(z_I) = ∑_{t ∈ I} f_t(x_t) − ∑_{t ∈ I} f_t(z_I)`. -/
def intervalRegret {E : Type*} (h : ℕ → E → ℝ) (y : ℕ → E) (a b : ℕ) (z : E) : ℝ :=
  ∑ t ∈ Finset.Icc a b, (h t (y t) - h t z)

end IntervalToDynamic


