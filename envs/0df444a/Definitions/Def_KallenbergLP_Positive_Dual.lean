-- Prove2me | Definitions.Def_KallenbergLP_Positive_Dual
-- name    : KallenbergLP_Positive_Dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:04:52.838679+00:00
-- url     : https://prove2.me/theorems/eb63f2e1-72f6-494c-a333-d222d1bc8e30
-- title:
--   Equation (3.5.2) — positive dynamic programming dual linear program
-- statement:
--   Let $\beta_j>0$ be a positive weight for every state. The **dual program** (3.5.2) maximizes
--   $$
--   \sum_{i\in E}\sum_{a\in A(i)}r_{ia}x_{ia}
--   $$
--   over nonnegative state-action flows $x_{ia}$ subject to
--   $$
--   \sum_{a\in A(j)}x_{ja}-\sum_{i\in E}\sum_{a\in A(i)}p_{iaj}x_{ia}\le\beta_j\qquad(j\in E).
--   $$
--   Its feasible region is a subset of the vector space whose coordinates are exactly the admissible state-action pairs. A feasible $x$ is optimal if its objective is at least that of every other feasible flow. Notation 3.1.1 defines $E_x=\{i:\sum_{a\in A(i)}x_{ia}>0\}$.
--
--   The positive weights and the direction of the balance inequalities are essential to the policy extraction theorem.
--
--   **Formalization Note** The state-action coordinate space is a dependent function type: no coordinates exist for inadmissible actions. Extreme points are taken in this feasible region, before the slack variables of equation (3.5.4) are introduced.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 35 (PDF p. 43), Notation 3.1.1; p. 78 (PDF p. 86), equation (3.5.2)

import Definitions.Def_KallenbergLP_Positive_Value

namespace KallenbergLP.Positive

variable {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- Coordinates of the dual program are indexed only by admissible state-action pairs. -/
abbrev Flow (M : MDP N α) := (i : Fin N) → M.actions i → ℝ

/-- Notation 3.1.1: states with positive total flow. -/
def occupiedStates (M : MDP N α) (x : Flow M) : Set (Fin N) :=
  {i | 0 < ∑ a : M.actions i, x i a}

/-- Left side of (3.5.2) for the state `j`. -/
def dualBalance (M : MDP N α) (x : Flow M) (j : Fin N) : ℝ :=
  (∑ a : M.actions j, x j a) -
    ∑ i : Fin N, ∑ a : M.actions i, M.transition i a.val j * x i a

/-- The feasible region of (3.5.2), with its `≤ β_j` balance constraints. -/
def dualFeasible (M : MDP N α) (β : Fin N → ℝ) : Set (Flow M) :=
  {x | (∀ i (a : M.actions i), 0 ≤ x i a) ∧
    ∀ j, dualBalance M x j ≤ β j}

/-- Objective of (3.5.2). -/
def dualObjective (M : MDP N α) (x : Flow M) : ℝ :=
  ∑ i : Fin N, ∑ a : M.actions i, M.reward i a.val * x i a

/-- An optimal solution among all feasible dual flows. -/
def IsDualOptimal (M : MDP N α) (β : Fin N → ℝ) (x : Flow M) : Prop :=
  x ∈ dualFeasible M β ∧
    ∀ y ∈ dualFeasible M β, dualObjective M y ≤ dualObjective M x

end KallenbergLP.Positive


