-- Prove2me | Definitions.Def_SparseBatchBandit_batchIndex
-- name    : SparseBatchBandit_batchIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:45.235277+00:00
-- url     : https://prove2.me/theorems/442ccbcf-74db-4c88-b478-2fada9e9460b
-- title:
--   Batch of a round
-- statement:
--   The batch of round $t$ is the least $m\ge1$ with $t\le t_m$. When the grid is increasing this is the unique $m$ with $t_{m-1}<t\le t_m$.
--
--   **Formalization Note** Rounds are elements of `Fin T`, so the paper's round number is the Lean index plus one. Since $t_M=T$, the batch of a round lies in $\{1,\dots,M\}$ when $M\ge1$. The definition does not need the grid to be increasing.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Algorithm 1, p.16

import Mathlib
import Definitions.Def_SparseBatchBandit_grid

namespace SparseBatchBandit

/-- The batch of a round: the least `m ≥ 1` with `t ≤ t_m`, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, Algorithm 1, p.16 (PDF 16).

**Formalization Note.** A round is `t : Fin T`, the round number of the page being `t + 1`. For
`1 ≤ M` the set is nonempty, because `t_M = T`, and its least element is at most `M`. When the grid
increases this says `t_{m−1} < t + 1 ≤ t_m`; the definition does not rely on the grid increasing. -/
noncomputable def batchIndex (T s₀ M : ℕ) (t : Fin T) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ t.val + 1 ≤ grid T s₀ M m}

end SparseBatchBandit


