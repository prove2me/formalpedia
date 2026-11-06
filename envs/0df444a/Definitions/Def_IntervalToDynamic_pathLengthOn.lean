-- Prove2me | Definitions.Def_IntervalToDynamic_pathLengthOn
-- name    : IntervalToDynamic_pathLengthOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:48.123112+00:00
-- url     : https://prove2.me/theorems/5c288fe7-2134-4220-b9e5-4a376c9dbb2c
-- title:
--   The local path length $P_I$
-- statement:
--   For $I=[a,b]$ the local path length of $u$ is
--   $$
--   P_I=\sum_{t=a+1}^b\|u_t-u_{t-1}\|_2 .
--   $$
--   In particular $P_{[a,a]}=0$.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Lemma 11, p.29

import Mathlib

namespace IntervalToDynamic

/-- The local path length `P_I = ∑_{t=a+1}^b ‖u_t − u_{t−1}‖₂` of `I = [a, b]`. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Lemma 11,
p.29. In particular `P_{[a,a]} = 0`. -/
def pathLengthOn {E : Type*} [NormedAddCommGroup E] (u : ℕ → E) (a b : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc (a + 1) b, ‖u t - u (t - 1)‖

end IntervalToDynamic


