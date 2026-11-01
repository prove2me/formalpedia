-- Prove2me | Definitions.Def_TightQLearning_valuePi
-- name    : TightQLearning_valuePi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:16.419682+00:00
-- url     : https://prove2.me/theorems/49e3f443-20e1-42c5-8bb2-de39fc18537c
-- title:
--   §2 — the value function $V^\pi$
-- statement:
--   For a policy $\pi$, a discount factor $\gamma$ and a state $s$, the **value function** is
--   $$V^\pi(s)=\mathbb E\Big[\sum_{k=0}^\infty\gamma^k r(s_k,a_k)\,\Big|\,s_0=s\Big],$$
--   where $(s_k,a_k)_{k\ge0}$ is the trajectory of the MDP under $\pi$.
--
--   **Formalization Note** The definition applies the published `PolicyValue`, the series $\sum_k\gamma^k\sum_{s'}\Pr(s_k=s'\mid s_0=s)\sum_a\pi(a\mid s')r(s',a)$, to the policy's probability table. That series is the displayed expectation computed term by term.
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), §2, p.6

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_TightQLearning_Policy

namespace TightQLearning

/-- The value function `V^π(s) = E[∑_{k≥0} γ^k r(s_k, a_k) | s_0 = s]` (arXiv:2102.06548v4, §2, p.6).

**Formalization Note.** This is the published `PolicyValue` of Mohri et al.: the series
`∑'_k γ^k ∑_{s'} P(s_k = s' | s_0 = s) · ∑_a π(a|s') r(s',a)`, which computes the trajectory
expectation of the page state by state. -/
noncomputable def valuePi {X A : Type} [Fintype X] [DecidableEq X] [Fintype A]
    (M : QLearning.Convergence.FiniteMDP X A) (γ : ℝ) (π : Policy X A) (s : X) : ℝ :=
  FoundationsML.ReinforcementLearning.PolicyValue (fun x a => (π x : A → ℝ) a) M.P M.R γ s

end TightQLearning


