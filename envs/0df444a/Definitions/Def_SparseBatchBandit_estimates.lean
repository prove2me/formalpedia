-- Prove2me | Definitions.Def_SparseBatchBandit_estimates
-- name    : SparseBatchBandit_estimates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:31:25.001097+00:00
-- url     : https://prove2.me/theorems/70926d13-2e6e-4f5e-bc18-aaa1e3c1f995
-- title:
--   Estimates of LBGL, computed batch by batch
-- statement:
--   Given realized contexts and noises, the estimates of LBGL are computed recursively: $\hat\theta_0=0$, and after batch $m$ the estimate $\hat\theta_m$ is the output of the selection rule on the design $(x_{t,a_t})_{t\in T^{(m)}}$ and the rewards $(r_{t,a_t})_{t\in T^{(m)}}$. Those rounds lie in batches $1,\dots,m$, so their actions use only $\hat\theta_0,\dots,\hat\theta_{m-1}$.
--
--   **Formalization Note** The recursion keeps the whole table of estimates; entry $k$ after step $m\ge k$ is $\hat\theta_k$, and entries beyond the current step are $0$ and never read.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Algorithm 1, p.16

import Mathlib
import Definitions.Def_SparseBatchBandit_LassoSelector
import Definitions.Def_SparseBatchBandit_playedArm
import Definitions.Def_SparseBatchBandit_reward

namespace SparseBatchBandit

/-- The estimates of LBGL, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, Algorithm 1, p.16 (PDF 16), computed batch by batch from realized
contexts `c` and noises `e`. After step `m`, entry `k ≤ m` of `estimates … m` is `θ̂_k`: `θ̂₀ = 0`, and
`θ̂_{m+1}` is the output of the rule `sel` on the design and rewards of `T^{(m+1)}`, whose rounds
played the estimates `θ̂₀, …, θ̂_m`.

**Formalization Note.** Entries beyond the current step are `0` and are never read: a round of
`T^{(m+1)}` is in a batch `m' ≤ m + 1` and reads `θ̂_{m'−1}`. -/
noncomputable def estimates {T K d : ℕ} [NeZero K] (s₀ M : ℕ) (sel : LassoSelector T s₀ M d)
    (c : Fin T → Fin K → Fin d → ℝ) (e : Fin T → ℝ) (θstar : Fin d → ℝ) : ℕ → ℕ → Fin d → ℝ
  | 0 => fun _ => 0
  | m + 1 =>
    let est := estimates s₀ M sel c e θstar m
    let o := (sample T s₀ M (m + 1)).orderEmbOfFin rfl
    Function.update est (m + 1)
      (sel (m + 1) (fun i => c (o i) (playedArm s₀ M c est (o i)))
        (fun i => reward c e θstar (playedArm s₀ M c est) (o i)))

end SparseBatchBandit


