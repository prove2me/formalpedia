-- Prove2me | Definitions.Def_SparseBatchBandit_batch
-- name    : SparseBatchBandit_batch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:38.3482+00:00
-- url     : https://prove2.me/theorems/a9d57eb0-9a86-4f4b-850a-fc4a36ecc8d7
-- title:
--   Rounds of batch $m$
-- statement:
--   Batch $m$ is the set of rounds $\{t_{m-1}+1,\dots,t_m\}$, that is, the rounds whose batch index is $m$.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Algorithm 1, p.16

import Mathlib
import Definitions.Def_SparseBatchBandit_batchIndex

namespace SparseBatchBandit

/-- The rounds `{t_{m−1} + 1, …, t_m}` of batch `m`, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, Algorithm 1, p.16 (PDF 16). -/
noncomputable def batch (T s₀ M m : ℕ) : Finset (Fin T) :=
  Finset.univ.filter (fun t => batchIndex T s₀ M t = m)

end SparseBatchBandit


