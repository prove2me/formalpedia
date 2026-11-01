-- Prove2me | Definitions.Def_NonstatNV_windowMean
-- name    : NonstatNV_windowMean
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:01:56.423704+00:00
-- url     : https://prove2.me/theorems/d9564daf-108d-41c8-b739-67b807617ba3
-- title:
--   Window average $\hat\mu^{\mathrm{fixed}}_t=\frac1n\sum_{s=t-n}^{t-1}d_s$
-- statement:
--   The **window average** at period $t$ with window size $n$ is the average of the last $n$ observed demands,
--
--   $$
--   \hat\mu^{\mathrm{fixed}}_t=\frac1n\sum_{s=t-n}^{t-1}d_s ,
--   $$
--
--   before any rounding. It is the mean estimate of the Fixed-Time-Window Policy and the reference against which PERP tests the predictions.
--
--   **Formalization Note** It is used only for $t\ge n+1$, where the summation range is exactly $\{t-n,\dots,t-1\}$ and consists of periods $\ge1$.
-- source:
--   L. An, A. A. Li, B. Moseley, R. Ravi, The Nonstationary Newsvendor with (and without) Predictions, arXiv:2305.07993v4 (20 Feb 2025), https://arxiv.org/abs/2305.07993v4, Algorithm 1, p.16; Algorithm 4, p.23

import Mathlib

namespace NonstatNV

/-- The window average `μ̂^fixed_t = (1/n) Σ_{s=t−n}^{t−1} d_s` of the last `n` demands before period
`t` (Algorithms 1 and 4 of An, Li, Moseley, Ravi, *The Nonstationary Newsvendor with (and without) Predictions*, arXiv:2305.07993v4, pp.16, 23), unrounded; `ω s` is the demand `d_s`.

**Formalization Note** It is used only for `t ≥ n + 1`, where `Finset.Ico (t − n) t` is exactly
`{t − n, …, t − 1}` and `t − n ≥ 1`. -/
noncomputable def windowMean (n t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ s ∈ Finset.Ico (t - n) t, ω s

end NonstatNV


