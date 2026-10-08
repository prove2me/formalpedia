-- Prove2me | Definitions.Def_SuttonBartoRL_ImportanceSampling_InfiniteVarianceExample
-- name    : SuttonBartoRL_ImportanceSampling_InfiniteVarianceExample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:30:41.001984+00:00
-- url     : https://prove2.me/theorems/8ee386af-de5d-4751-ab90-1f90a9bae1f7
-- title:
--   The one-state MDP of Example 5.5 (Figure 5.4) with its target and behaviour policies
-- statement:
--   The MDP of Example 5.5 has one nonterminal state $s$, a terminal state, and two actions, **left** and **right**. From $s$:
--
--   1. **right** moves to termination with reward $0$;
--   2. **left** moves back to $s$ with probability $0.9$ and reward $0$, or to termination with probability $0.1$ and reward $+1$.
--
--   The **target policy** always selects left, $\pi(\text{left} \mid s) = 1$. The **behaviour policy** selects left and right with equal probability, $b(\text{left} \mid s) = \tfrac12$.
--
--   The example shows that ordinary importance sampling can have infinite variance when trajectories contain loops.
--
--   **Formalization Note** The reward set is $\{0, 1\}$. The terminal state is made absorbing with reward $0$ so that the dynamics are a probability distribution in every state; transitions out of the terminal state are never used by an episode.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Example 5.5 and Figure 5.4, pp. 106–107

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_MDP

namespace SuttonBartoRL.ImportanceSampling

/-- The states of Example 5.5, p. 106: one nonterminal state `s` and the terminal state. -/
inductive ExState
  | s
  | terminal
  deriving DecidableEq

instance : Fintype ExState :=
  ⟨{ExState.s, ExState.terminal}, by intro x; cases x <;> simp⟩

/-- The actions of Example 5.5, p. 106: `left` and `right`. -/
inductive ExAction
  | left
  | right
  deriving DecidableEq

instance : Fintype ExAction :=
  ⟨{ExAction.left, ExAction.right}, by intro x; cases x <;> simp⟩

/-- The MDP of Example 5.5 (Figure 5.4), p. 106: `right` moves from `s` to termination with reward
`0`; `left` moves from `s` back to `s` with probability `0.9` and reward `0`, or to termination
with probability `0.1` and reward `+1`. Rewards lie in `{0, 1}`. The terminal state is absorbing
with reward `0` (its transitions are never used by an episode). -/
noncomputable def exampleMDP : MDP ExState ExAction where
  R := {0, 1}
  p := fun x a y r =>
    match x, a, y with
    | .s, .left, .s => if r = 0 then 9 / 10 else 0
    | .s, .left, .terminal => if r = 1 then 1 / 10 else 0
    | .s, .right, .s => 0
    | .s, .right, .terminal => if r = 0 then 1 else 0
    | .terminal, _, .s => 0
    | .terminal, _, .terminal => if r = 0 then 1 else 0
  p_nonneg := by
    intro x a y r
    cases x <;> cases a <;> cases y <;> dsimp only <;> (try split_ifs) <;> norm_num
  p_sum := by
    intro x a
    have hu : (Finset.univ : Finset ExState) = {ExState.s, ExState.terminal} := rfl
    cases x <;> cases a <;> simp [hu] <;> norm_num

/-- The terminal states of Example 5.5. -/
def exampleTerminal : Finset ExState := {ExState.terminal}

/-- The target policy of Example 5.5: always `left`, `π(left|s) = 1`. -/
noncomputable def exampleTarget : SuttonBartoRL.FiniteMDP.Policy ExState ExAction where
  prob := fun _ a => if a = ExAction.left then 1 else 0
  nonneg := by intro _ a; split_ifs <;> norm_num
  sum_one := by intro _; simp

/-- The behaviour policy of Example 5.5: `left` and `right` with equal probability,
`b(left|s) = 1/2`. -/
noncomputable def exampleBehavior : SuttonBartoRL.FiniteMDP.Policy ExState ExAction where
  prob := fun _ _ => 1 / 2
  nonneg := by intro _ _; norm_num
  sum_one := by
    intro _
    have hu : (Finset.univ : Finset ExAction) = {ExAction.left, ExAction.right} := rfl
    rw [hu, Finset.sum_pair (by decide)]; norm_num

end SuttonBartoRL.ImportanceSampling


