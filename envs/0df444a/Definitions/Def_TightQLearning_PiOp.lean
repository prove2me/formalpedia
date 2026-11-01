-- Prove2me | Definitions.Def_TightQLearning_PiOp
-- name    : TightQLearning_PiOp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:40.225174+00:00
-- url     : https://prove2.me/theorems/033ea010-206d-4845-a69f-862f15983af4
-- title:
--   (24) — the operator $P^\pi$
-- statement:
--   For a deterministic policy $\pi$ and a function $f$ on $\mathcal S\times\mathcal A$, the operator $P^\pi=P\Pi^\pi$ of (24) acts by
--   $$(P^\pi f)(s,a)=\sum_{s'}P(s'\mid s,a)\,f\big(s',\pi(s')\big).$$
--   It is a state-action transition matrix, and it is the operator through which the error recursion of the mission propagates.
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), (24), p.11

import Mathlib
import Definitions.Def_QLearning_Convergence_Setting

namespace TightQLearning

/-- The matrix `P^π = PΠ^π` of (24) (arXiv:2102.06548v4, §4.1, p.11) for a deterministic policy
`π`, acting on `f : S × A → ℝ`: `(P^π f)(s,a) = ∑_{s'} P(s'|s,a) f(s', π(s'))`. -/
noncomputable def PiOp {X A : Type} [Fintype X] (M : QLearning.Convergence.FiniteMDP X A)
    (π : X → A) (f : X → A → ℝ) (s : X) (a : A) : ℝ :=
  ∑ s', M.P s a s' * f s' (π s')

end TightQLearning


