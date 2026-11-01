-- Prove2me | Definitions.Def_TightQLearning_vStar
-- name    : TightQLearning_vStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:20.186018+00:00
-- url     : https://prove2.me/theorems/5f05925e-5370-4d55-a7e2-eff9705175fd
-- title:
--   §2 — the optimal value function $V^\star$
-- statement:
--   The **optimal value function** is $V^\star(s):=\max_\pi V^\pi(s)$, the maximum over all policies, for each state $s$.
--
--   **Formalization Note** The maximum is a supremum over the nonempty type of policies. For $\gamma\in(0,1)$ on a finite model the family is bounded, so the supremum is meaningful; its attainment by a deterministic policy is part of the milestone `bellman_facts`.
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), §2, p.6

import Mathlib
import Definitions.Def_TightQLearning_valuePi

namespace TightQLearning

/-- The optimal value function `V⋆(s) := max_π V^π(s)` (arXiv:2102.06548v4, §2, p.6).

**Formalization Note.** The supremum runs over the nonempty type `Policy X A` of the paper's
policies. It is a real `⨆`, which is meaningful because the family is bounded for `γ ∈ (0,1)` on a
finite model; that the maximum is attained is part of `bellman_facts`. -/
noncomputable def vStar {X A : Type} [Fintype X] [DecidableEq X] [Fintype A]
    (M : QLearning.Convergence.FiniteMDP X A) (γ : ℝ) (s : X) : ℝ :=
  ⨆ π : Policy X A, valuePi M γ π s

end TightQLearning


