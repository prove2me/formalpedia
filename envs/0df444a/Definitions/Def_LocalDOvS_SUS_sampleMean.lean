-- Prove2me | Definitions.Def_LocalDOvS_SUS_sampleMean
-- name    : LocalDOvS_SUS_sampleMean
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:09.938477+00:00
-- url     : https://prove2.me/theorems/93934a08-b33d-4da1-ade8-b0cd039379ee
-- title:
--   Empirical mean $\hat F_n(x)$
-- statement:
--   The **empirical mean** of the first $n$ outputs of decision $x$:
--
--   $$
--   \hat F_n(x):=\frac1n\sum_{j=1}^nF(x,\xi_{x,j}).
--   $$
--
--   **Formalization Note** Outputs are indexed from $0$; at $n=0$ the value is $0$, and the algorithm only uses $n\ge1$.
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, §1.2, p.7

import Mathlib

namespace LocalDOvS.SUS

/-- The empirical mean `F̂_n(x) := (1/n) Σ_{j=1}^n F(x, ξ_{x,j})` of the first `n` outputs of
decision `x` (Zhang–Zheng–Lavaei, arXiv:2012.02427v2, §1.2, p.7), where `D x j` is the
`(j + 1)`-th output of `x`.

**Formalization Note.** Outputs are 0-indexed (`j < n`). At `n = 0` the value is `0`; the
algorithm uses only `n ≥ 1`. -/
noncomputable def sampleMean (D : ℕ → ℕ → ℝ) (x n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, D x j) / n

end LocalDOvS.SUS


