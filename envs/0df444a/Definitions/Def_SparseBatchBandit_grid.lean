-- Prove2me | Definitions.Def_SparseBatchBandit_grid
-- name    : SparseBatchBandit_grid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:46.343219+00:00
-- url     : https://prove2.me/theorems/ad54a01a-b467-4da9-a376-deae77c93235
-- title:
--   Static grid $\{t_1,\dots,t_M\}$
-- statement:
--   The **static grid** of LBGL is $0=t_0,t_1,\dots,t_M$ with $t_M=T$ and $t_m$ given by the recursion for $1\le m<M$. It is fixed before any data are seen, and batch $m$ ends at round $t_m$.
--
--   **Formalization Note** With floors, a value of $b$ for which the recursion itself lands on $T$ need not exist, so the last point is set to $T$, which is the paper's requirement.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, §4.1 and Algorithm 1, p.16

import Mathlib
import Definitions.Def_SparseBatchBandit_gridRaw

namespace SparseBatchBandit

/-- The static grid `𝒯 = {t₁, …, t_M}` of LBGL, with `t₀ = 0` and `t_M = T`, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, §4.1 and
Algorithm 1, p.16 (PDF 16). The points `t_m`, `m < M`, are those of `gridRaw`.

**Formalization Note.** With floors a `b` giving `t_M = T` by the recursion alone need not exist, so
the last point is set to `T`, which is the page's requirement. -/
noncomputable def grid (T s₀ M : ℕ) (m : ℕ) : ℕ :=
  if m = M then T else gridRaw T s₀ M m

end SparseBatchBandit


