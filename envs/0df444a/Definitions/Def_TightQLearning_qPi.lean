-- Prove2me | Definitions.Def_TightQLearning_qPi
-- name    : TightQLearning_qPi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:10.590049+00:00
-- url     : https://prove2.me/theorems/a0b73424-2393-4fad-895e-b9327ca307b8
-- title:
--   §2 — the Q-function $Q^\pi$
-- statement:
--   For a policy $\pi$ the **Q-function** is
--   $$Q^\pi(s,a)=\mathbb E\Big[\sum_{k=0}^\infty\gamma^k r(s_k,a_k)\,\Big|\,s_0=s,\ a_0=a\Big],$$
--   the trajectory following $\pi$ except for the fixed first action $a_0=a$.
--
--   **Formalization Note** The definition applies the published `QFunction`, $r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V^\pi(s')$, which writes out the first step of that trajectory.
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), §2, p.6

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction
import Definitions.Def_TightQLearning_Policy

namespace TightQLearning

/-- The Q-function `Q^π(s,a) = E[∑_{k≥0} γ^k r(s_k, a_k) | s_0 = s, a_0 = a]` (arXiv:2102.06548v4,
§2, p.6), the trajectory following `π` "except a_0".

**Formalization Note.** This is the published `QFunction` of Mohri et al.:
`r(s,a) + γ ∑_{s'} P(s'|s,a) V^π(s')`, the first step of that trajectory written out. -/
noncomputable def qPi {X A : Type} [Fintype X] [DecidableEq X] [Fintype A]
    (M : QLearning.Convergence.FiniteMDP X A) (γ : ℝ) (π : Policy X A) (s : X) (a : A) : ℝ :=
  FoundationsML.ReinforcementLearning.QFunction (fun x a => (π x : A → ℝ) a) M.P M.R γ s a

end TightQLearning


