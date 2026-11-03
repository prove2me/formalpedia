-- Prove2me | Definitions.Def_SparseBatchBandit_lambdaM
-- name    : SparseBatchBandit_lambdaM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:29:57.608796+00:00
-- url     : https://prove2.me/theorems/874a7f3c-7421-4116-b53f-6152a2881d24
-- title:
--   Lasso penalty $\lambda_m$
-- statement:
--   The penalty of the $m$-th Lasso step is
--
--   $$
--   \lambda_m=10\sqrt{\frac{2\log K\,(\log d+2\log T)}{|T^{(m)}|}}.
--   $$
--
--   **Formalization Note** Logarithms are natural. If $T^{(m)}$ is empty, division by zero gives $\lambda_m=0$; this occurs only for small $T$ and the statements do not exclude it.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Algorithm 1, p.16

import Mathlib
import Definitions.Def_SparseBatchBandit_sample

namespace SparseBatchBandit

/-- The Lasso penalty `λ_m = 10 · √(2 log K (log d + 2 log T) / |T^{(m)}|)`, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, Algorithm 1,
p.16 (PDF 16).

**Formalization Note.** Logs are natural. If `T^{(m)}` is empty the division gives `λ_m = 0`, and
the least-squares term of the objective is `0` as well, so nothing is estimated. The mission's
statements do not exclude that case: it occurs only for small `T`. -/
noncomputable def lambdaM (T d K s₀ M m : ℕ) : ℝ :=
  10 * Real.sqrt (2 * Real.log K * (Real.log d + 2 * Real.log T) / (sample T s₀ M m).card)

end SparseBatchBandit


