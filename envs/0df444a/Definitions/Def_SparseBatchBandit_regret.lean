-- Prove2me | Definitions.Def_SparseBatchBandit_regret
-- name    : SparseBatchBandit_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:55.424401+00:00
-- url     : https://prove2.me/theorems/056e9d1b-3537-4973-bea5-71826381fe05
-- title:
--   Regret $R_T$ (Definition 1)
-- statement:
--   The **regret** of a sequence of actions $a_1,\dots,a_T$ is
--
--   $$
--   R_T=\sum_{t=1}^T\Big(\max_{a\in[K]}x_{t,a}^\top\theta^\star-x_{t,a_t}^\top\theta^\star\Big).
--   $$
--
--   It is random, and it compares with the best arm of each round, the arm an oracle knowing $\theta^\star$ would play.
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, Definition 1, p.8

import Mathlib
import Definitions.Def_SparseBatchBandit_maxArm
open Matrix

namespace SparseBatchBandit

/-- **Definition 1**, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, p.8 (PDF 8): `R_T = ∑_{t=1}^T (max_{a∈[K]} x_{t,a}⊤θ⋆ − x_{t,a_t}⊤θ⋆)`,
for the actions `a` of any algorithm. It is random through the contexts and the actions, and it
compares with the best arm of each round. -/
noncomputable def regret {T K d : ℕ} [NeZero K] (c : Fin T → Fin K → Fin d → ℝ)
    (θstar : Fin d → ℝ) (a : Fin T → Fin K) : ℝ :=
  ∑ t, (maxArm (fun b => c t b ⬝ᵥ θstar) - c t (a t) ⬝ᵥ θstar)

end SparseBatchBandit


