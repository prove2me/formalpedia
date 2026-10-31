-- Prove2me | Definitions.Def_AccelSGDGrowth_cumWeight
-- name    : AccelSGDGrowth_cumWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:29:27.064076+00:00
-- url     : https://prove2.me/theorems/1c92e677-e2d8-4b32-9dd6-7eff76bd1de4
-- title:
--   The cumulative weight $A_k=\sum_{i=1}^k a_i$
-- statement:
--   For a weight sequence $(a_i)_{i\ge1}$, the cumulative weight is
--   $$
--   A_k=\sum_{i=1}^k a_i ,\qquad A_0=0 .
--   $$
--   It is the normalizer of the dual-averaging scheme, and $\rho_k=A_{k-1}/A_k$ is the contraction rate of Theorem 4.1.
--
--   **Formalization Note** The weights are an $\mathbb N$-indexed sequence with index 0 unused; the sum is over `Finset.Icc 1 k`.
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, (4.2), p.14

import Mathlib

namespace AccelSGDGrowth

/-- The cumulative weight $A_k = \sum_{i=1}^k a_i$ of Chen, Na, Kolar, arXiv:2006.06782v4, (4.2), p.14.

**Formalization Note.** Weights are an `ℕ`-indexed sequence with index 0 unused, and the sum runs
over `Finset.Icc 1 k`, so `A_0 = 0`. -/
noncomputable def cumWeight (a : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 k, a i

end AccelSGDGrowth


