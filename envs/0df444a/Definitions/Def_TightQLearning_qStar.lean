-- Prove2me | Definitions.Def_TightQLearning_qStar
-- name    : TightQLearning_qStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:03.443843+00:00
-- url     : https://prove2.me/theorems/f18e5f27-1630-46f0-81d1-4b628355b2ee
-- title:
--   §2 — the optimal Q-function $Q^\star$
-- statement:
--   The **optimal Q-function** is $Q^\star(s,a):=\max_\pi Q^\pi(s,a)$, the maximum over all policies, for each state-action pair $(s,a)$. This is the target of synchronous Q-learning.
--
--   **Formalization Note** As for $V^\star$, the maximum is a supremum over the nonempty type of policies. $Q^\star$ is not defined through the Bellman equation; that it solves the equation is a milestone, not a definition.
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), §2, p.6

import Mathlib
import Definitions.Def_TightQLearning_qPi

namespace TightQLearning

/-- The optimal Q-function `Q⋆(s,a) := max_π Q^π(s,a)` (arXiv:2102.06548v4, §2, p.6).

**Formalization Note.** As for `vStar`: a real `⨆` over the nonempty type `Policy X A`, a bounded
family for `γ ∈ (0,1)` on a finite model. `Q⋆` is not defined as the solution of the Bellman
equation; the paper's fixed-point statement is the milestone `bellman_facts`. -/
noncomputable def qStar {X A : Type} [Fintype X] [DecidableEq X] [Fintype A]
    (M : QLearning.Convergence.FiniteMDP X A) (γ : ℝ) (s : X) (a : A) : ℝ :=
  ⨆ π : Policy X A, qPi M γ π s a

end TightQLearning


