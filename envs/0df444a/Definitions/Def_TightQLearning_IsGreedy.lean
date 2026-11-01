-- Prove2me | Definitions.Def_TightQLearning_IsGreedy
-- name    : TightQLearning_IsGreedy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:37.381844+00:00
-- url     : https://prove2.me/theorems/503f2e53-efda-43d1-8507-4099df0a1131
-- title:
--   (27)–(28) — greedy selections
-- statement:
--   A deterministic policy $\pi$ is a **greedy selection** of $Q$ if $Q(s,\pi(s))=\max_{a}Q(s,a)$ for every state $s$, which is property (28) of the policy $\pi_t$ defined in (27).
--
--   **Formalization Note** (27) fixes the smallest maximizing index. This predicate accepts every tie-break, including that one, so statements using it hold in particular for (27).
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), (27)–(28), p.12

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting

namespace TightQLearning

/-- `π` is a greedy selection of `Q`: `Q(s, π(s)) = V(s) = max_a Q(s, a)` for every state, the
property (28) of the policy `π_t` of (27) (arXiv:2102.06548v4, §4.1, p.12).

**Formalization Note.** (27) takes the smallest maximizing index. This predicate accepts every
tie-break, including that one, and needs no order on the actions. -/
def IsGreedy {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (Q : X → A → ℝ) (π : X → A) : Prop :=
  ∀ s, Q s (π s) = QLearning.Convergence.vmax Q s

end TightQLearning


