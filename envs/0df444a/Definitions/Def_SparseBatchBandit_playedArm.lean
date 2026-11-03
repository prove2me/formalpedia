-- Prove2me | Definitions.Def_SparseBatchBandit_playedArm
-- name    : SparseBatchBandit_playedArm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:45.231594+00:00
-- url     : https://prove2.me/theorems/43418d6f-04df-4d6b-8f87-76deab8481df
-- title:
--   Step (a) of LBGL
-- statement:
--   Given estimates $\hat\theta_0,\hat\theta_1,\dots$, a round $t$ of batch $m$ plays the greedy action for $\hat\theta_{m-1}$:
--
--   $$
--   a_t=\operatorname*{argmax}_{a\in[K]}x_{t,a}^\top\hat\theta_{m-1}.
--   $$
--
--   The estimate used in a batch does not change during the batch, which is the batch constraint.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Algorithm 1, p.16

import Mathlib
import Definitions.Def_SparseBatchBandit_batchIndex
import Definitions.Def_SparseBatchBandit_greedyArm

namespace SparseBatchBandit

/-- Step (a) of Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, Algorithm 1, p.16 (PDF 16): in batch `m`, round `t` plays
`a_t = argmax_a x_{t,a}⊤θ̂_{m−1}`, where `est k` stands for `θ̂_k`.

**Formalization Note.** `batchIndex` is at least `1` on every round when `1 ≤ M`, so `− 1` is exact. -/
noncomputable def playedArm {T K d : ℕ} [NeZero K] (s₀ M : ℕ) (c : Fin T → Fin K → Fin d → ℝ)
    (est : ℕ → Fin d → ℝ) (t : Fin T) : Fin K :=
  greedyArm (c t) (est (batchIndex T s₀ M t - 1))

end SparseBatchBandit


