-- Prove2me | Definitions.Def_ApproxVI_tSeq
-- name    : ApproxVI_tSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:30.192229+00:00
-- url     : https://prove2.me/theorems/269e67de-f005-4626-a416-c1ada9f31654
-- title:
--   The time grid $t_n=\sum_{m<n}a(m)$
-- statement:
--   For step sizes $a(n)$, the time grid is $t_0=0$ and
--
--   $$
--   t_n=\sum_{m=0}^{n-1}a(m),\qquad n\ge1.
--   $$
--
--   It places the $n$-th iterate of a stochastic approximation at time $t_n$, which is how the iterates are compared with trajectories of a differential inclusion.
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, §6.1, p.22

import Mathlib

namespace ApproxVI

/-- The time grid of Ramaswamy & Bhatnagar, *Analyzing Approximate Value Iteration Algorithms*,
arXiv:1709.04673v5, §6.1, p.22: `t₀ := 0` and `tₙ := Σ_{m=0}^{n−1} a(m)` for `n ≥ 1`. -/
def tSeq (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, a m

end ApproxVI


