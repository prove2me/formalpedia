-- Prove2me | Definitions.Def_TightQLearning_syncQ
-- name    : TightQLearning_syncQ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:35.341685+00:00
-- url     : https://prove2.me/theorems/11ce4bb1-edca-4187-8917-d6aa20f7b36e
-- title:
--   (4)–(6), Algorithm 1 — the synchronous Q-learning iterates
-- statement:
--   Given a table of samples $s_t(s,a)$, learning rates $\eta_t$, a discount factor $\gamma$ and an initial estimate $Q_0$, **synchronous Q-learning** updates all entries at once:
--   $$Q_t(s,a)=(1-\eta_t)\,Q_{t-1}(s,a)+\eta_t\Big(r(s,a)+\gamma\max_{a'\in\mathcal A}Q_{t-1}\big(s_t(s,a),a'\big)\Big),\qquad t\ge1.$$
--   The value estimate is $V_t(s)=\max_a Q_t(s,a)$.
--
--   This is Algorithm 1 of the paper, one deterministic run for each sample table. Randomness enters by evaluating it at a random table.
--
--   **Formalization Note** The index $t$ agrees with the paper's, so $\eta_0$ and $s_0$ are never read.
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), (4)–(6), pp.6–7; Algorithm 1, p.7

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting

namespace TightQLearning

/-- The synchronous Q-learning iterates of Algorithm 1 (arXiv:2102.06548v4, p.7), updates (4)–(5),
p.6, pathwise on a table of samples: with `σ t s a` the sample `s_t(s,a)`,
`Q_t(s,a) = (1 − η_t) Q_{t−1}(s,a) + η_t (r(s,a) + γ max_{a'} Q_{t−1}(s_t(s,a), a'))`.

**Formalization Note.** Lean's `t` is the paper's `t`: `syncQ … 0 = Q₀`, and step `t + 1` uses
`η (t + 1)` and `σ (t + 1)`; `η 0` and `σ 0` are never read. The value estimate (6) is
`V_t = vmax (syncQ … t)`. -/
noncomputable def syncQ {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
    [Nonempty A] (M : QLearning.Convergence.FiniteMDP X A) (γ : ℝ) (η : ℕ → ℝ) (Q0 : X → A → ℝ)
    (σ : ℕ → X → A → X) : ℕ → X → A → ℝ
  | 0 => Q0
  | t + 1 => fun s a =>
      (1 - η (t + 1)) * syncQ M γ η Q0 σ t s a
        + η (t + 1) *
          (M.R s a + γ * QLearning.Convergence.vmax (syncQ M γ η Q0 σ t) (σ (t + 1) s a))

end TightQLearning


