-- Prove2me | Definitions.Def_TightQLearning_Policy
-- name    : TightQLearning_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:22.81114+00:00
-- url     : https://prove2.me/theorems/29277da7-f0da-4745-a211-92cf3504326f
-- title:
--   §2 — stationary randomized policies $\pi:\mathcal S\to\Delta(\mathcal A)$
-- statement:
--   A **policy** assigns to every state $s\in\mathcal S$ a probability distribution $\pi(\cdot\mid s)\in\Delta(\mathcal A)$ on the finite action set.
--
--   This is the class over which the optimal value $V^\star$ and the optimal Q-function $Q^\star$ are taken. It is the paper's only notion of policy, and the suprema of the mission range over exactly this class.
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), §2, p.6

import Mathlib

namespace TightQLearning

/-- A policy `π : S → Δ(A)` (Li, Cai, Chen, Wei & Chi, arXiv:2102.06548v4, §2, p.6): a stationary,
possibly randomized action selection rule, `π(· | s) ∈ Δ(A)`.

**Formalization Note.** A term of `Policy X A` is a map into the subtype `stdSimplex ℝ A`, so a
supremum over `Policy X A` ranges over exactly the paper's policies. -/
abbrev Policy (X A : Type) [Fintype A] : Type := X → stdSimplex ℝ A

end TightQLearning


