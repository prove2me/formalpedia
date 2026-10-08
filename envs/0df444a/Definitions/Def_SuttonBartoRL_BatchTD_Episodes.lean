-- Prove2me | Definitions.Def_SuttonBartoRL_BatchTD_Episodes
-- name    : SuttonBartoRL_BatchTD_Episodes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:15:03.882579+00:00
-- url     : https://prove2.me/theorems/a6d40b0a-645a-4a8f-b671-2f092b9ee566
-- title:
--   Observed episodes, the return $G_t$ and the TD error $\delta_t$ (6.5) of a fixed value array
-- statement:
--   An **episode** of a Markov reward process with nonterminal state set $\mathcal S$ is a finite sequence
--
--   $$
--   S_0, R_1, S_1, R_2, \dots, S_{T-1}, R_T, S_T
--   $$
--
--   in which $S_0, \dots, S_{T-1} \in \mathcal S$ are nonterminal states, $R_1, \dots, R_T$ are real rewards, and $S_T$ is the terminal state. We store it as the list of its $T$ transitions $(S_0, R_1), \dots, (S_{T-1}, R_T)$; the state $S_t$ for $t \ge T$ is the terminal state. Write $\mathcal S^+ = \mathcal S \cup \{\text{terminal}\}$.
--
--   A **value array** $V : \mathcal S \to \mathbb R$ is extended to $\mathcal S^+$ by the convention $V(\text{terminal}) = 0$. For a discount rate $\gamma$, the **return** after time $t$ is
--
--   $$
--   G_t = \sum_{k=t+1}^{T} \gamma^{k-t-1} R_k \qquad (G_T = 0),
--   $$
--
--   and the **TD error** of the fixed array $V$ at time $t < T$ is
--
--   $$
--   \delta_t = R_{t+1} + \gamma V(S_{t+1}) - V(S_t).
--   $$
--
--   For action values, an episode of state–action pairs lists $((S_t, A_t), R_{t+1})$ for $t < T$; an array $Q(s, a)$ is extended by $Q(\text{terminal}, \cdot) = 0$, and its TD error is $\delta_t = R_{t+1} + \gamma Q(S_{t+1}, A_{t+1}) - Q(S_t, A_t)$.
--
--   These are the objects of the TD prediction section: the return $G_t$ is the Monte Carlo target of (6.1), and $\delta_t$ is the quantity in brackets of the TD(0) update (6.2).
--
--   **Formalization Note** The terminal state is `none : Option X`; `stateAt e t` returns it for every $t \ge T$. `nextReward e t` is $R_{t+1}$ and is $0$ for $t \ge T$, where no transition takes place. The return is written $\sum_{k=t}^{T-1}\gamma^{k-t}R_{k+1}$, which is (3.11) with the index shifted by one. The state type `X` is left arbitrary, so the same definitions serve state values (`X = S`) and action values (`X = S × A`).
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, TD(0) box and Eq. (6.2), p. 120; TD error (6.5), p. 121; action-value TD error (6.7) and Exercise 6.8, p. 129; return (3.11), p. 57

import Mathlib

namespace SuttonBartoRL.BatchTD

/-- An observed episode `S_0, R_1, S_1, R_2, …, S_{T-1}, R_T, S_T` of a Markov reward process
(Sutton & Barto, §6.1, pp. 119–121), stored as the list of its `T` transitions
`[(S_0, R_1), (S_1, R_2), …, (S_{T-1}, R_T)]`. Every listed state is nonterminal; the state `S_T`
after the last transition is the terminal state, which is not stored. The length of the list is
the episode length `T`. The state type `X` is the set `S` of nonterminal states (or, for action
values, the set of state–action pairs). -/
abbrev Episode (X : Type) := List (X × ℝ)

variable {X : Type}

/-- The state `S_t` at time `t` of an episode, as an element of `S⁺ = Option X`: `some (S_t)` for
`t < T`, and `none` (the terminal state) for `t ≥ T`. In particular `S_T` is terminal. -/
def stateAt (e : Episode X) (t : ℕ) : Option X :=
  (e[t]?).map Prod.fst

/-- The reward `R_{t+1}` received on the transition from `S_t` (for `t < T`); `0` for `t ≥ T`,
where no transition takes place (the value is never used there). -/
def nextReward (e : Episode X) (t : ℕ) : ℝ :=
  match e[t]? with
  | some p => p.2
  | none => 0

/-- A value array on nonterminal states, extended to `S⁺ = Option X` by the convention
`V(terminal) = 0` of the tabular TD(0) box (p. 120). -/
def extV (V : X → ℝ) : Option X → ℝ
  | some x => V x
  | none => 0

/-- The return `G_t = Σ_{k=t+1}^{T} γ^{k-t-1} R_k` (Eq. (3.11)), written with `k` shifted by one:
`G_t = Σ_{k=t}^{T-1} γ^{k-t} R_{k+1}`. In particular `G_T = 0`. -/
noncomputable def ret (γ : ℝ) (e : Episode X) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico t e.length, γ ^ (k - t) * nextReward e k

/-- The TD error (6.5) `δ_t = R_{t+1} + γ V(S_{t+1}) − V(S_t)` of a fixed array `V`, with
`V(terminal) = 0`. -/
noncomputable def tdError (γ : ℝ) (V : X → ℝ) (e : Episode X) (t : ℕ) : ℝ :=
  nextReward e t + γ * extV V (stateAt e (t + 1)) - extV V (stateAt e t)

/-- An action-value array `Q(s, a)` on nonterminal states, extended to the terminal state by
`Q(terminal, ·) = 0` (p. 129: "If `S_{t+1}` is terminal, then `Q(S_{t+1}, A_{t+1})` is defined as
zero"). An episode of state–action pairs is an `Episode (S × A)`: the list
`[((S_0, A_0), R_1), …, ((S_{T-1}, A_{T-1}), R_T)]`. -/
def extQ {S A : Type} (Q : S → A → ℝ) : Option (S × A) → ℝ
  | some p => Q p.1 p.2
  | none => 0

/-- The action-value TD error `δ_t = R_{t+1} + γ Q(S_{t+1}, A_{t+1}) − Q(S_t, A_t)` of a fixed
array `Q` (Exercise 6.8, p. 129; the Sarsa error of (6.7)), with `Q(terminal, ·) = 0`. -/
noncomputable def qTdError {S A : Type} (γ : ℝ) (Q : S → A → ℝ) (e : Episode (S × A)) (t : ℕ) :
    ℝ :=
  nextReward e t + γ * extQ Q (stateAt e (t + 1)) - extQ Q (stateAt e t)

end SuttonBartoRL.BatchTD


