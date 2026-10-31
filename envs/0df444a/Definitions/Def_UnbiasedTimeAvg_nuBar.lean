-- Prove2me | Definitions.Def_UnbiasedTimeAvg_nuBar
-- name    : UnbiasedTimeAvg_nuBar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:37.299749+00:00
-- url     : https://prove2.me/theorems/9cea56fb-0736-427b-a7c0-95f558680939
-- title:
--   The tail sums $\bar\nu(j)=\sum_{i\ge j}\sqrt{\nu(i)/(i+1)}$
-- statement:
--   For a nonnegative sequence $\nu$ with $\sum_i\sqrt{\nu(i)/(i+1)}<\infty$, the paper sets
--   $$\bar\nu(j):=\sum_{i=j}^\infty\sqrt{\frac{\nu(i)}{i+1}},\qquad j\ge0.$$
--   $\bar\nu$ is finite, non-increasing (strictly decreasing when $\nu>0$) and tends to $0$. The constants of every bound in the mission are written in terms of $\bar\nu$.
--
--   **Formalization Note** A real `tsum`, equal to the paper's value whenever (2.4) holds, which every statement using it assumes.
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), §2.2, p.5 (definition of ω̄, used with ω = ν)

import Mathlib

namespace UnbiasedTimeAvg

/-- **The tail sums `ν̄(j)`.** Kahalé, arXiv:2209.09581v1, §2.2, p.5: "Given a non-negative
sequence `(ω(i), i ≥ 0)` such that `Σ_{i=0}^∞ √(ω(i)/(i + 1))` is finite, set
`ω̄(j) := Σ_{i=j}^∞ √(ω(i)/(i + 1))`, for `j ≥ 0`." The mission uses it with `ω = ν`.

`nuBar ν j = Σ_{i ≥ j} √(ν(i)/(i + 1))`, written as `Σ_{i ≥ 0} √(ν(i + j)/(i + j + 1))`.

**Formalization Note.** This is a real `tsum`; it is the paper's value whenever (2.4) holds, which
every statement using it assumes (`A1Sequence ν`). -/
noncomputable def nuBar (ν : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑' i : ℕ, Real.sqrt (ν (i + j) / (((i + j : ℕ) : ℝ) + 1))

end UnbiasedTimeAvg


