-- Prove2me | Definitions.Def_TightQLearning_detPolicy
-- name    : TightQLearning_detPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:17.497988+00:00
-- url     : https://prove2.me/theorems/76fbc6ff-27d6-4cca-a46e-99363b938342
-- title:
--   §2 — a deterministic policy as a point-mass policy
-- statement:
--   A deterministic policy $\pi:\mathcal S\to\mathcal A$ is identified with the policy that puts all its mass on the action $\pi(s)$ in each state $s$.
--
--   This embedding lets the statement "a deterministic policy attains $V^\star$ and $Q^\star$" compare a map $\mathcal S\to\mathcal A$ with the suprema over randomized policies.
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), §2, p.6

import Mathlib
import Definitions.Def_TightQLearning_Policy

namespace TightQLearning

/-- A deterministic policy `π : S → A` seen as a policy (arXiv:2102.06548v4, §2, p.6: "If π is a
deterministic policy, then we denote by π(s) the action selected by π in state s"): the point mass
at `π s` in each state. -/
noncomputable def detPolicy {X A : Type} [Fintype A] [DecidableEq A] (π : X → A) : Policy X A :=
  fun s => ⟨Pi.single (π s) 1, single_mem_stdSimplex ℝ (π s)⟩

end TightQLearning


