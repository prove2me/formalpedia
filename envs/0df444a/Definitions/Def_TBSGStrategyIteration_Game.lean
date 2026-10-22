-- Prove2me | Definitions.Def_TBSGStrategyIteration_Game
-- name    : TBSGStrategyIteration_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T23:58:28.790751+00:00
-- url     : https://prove2.me/theorems/200b3181-c344-4e03-af41-86be0b07eae1
-- title:
--   2-player turn-based discounted stochastic game (Definitions 2.1–2.3)
-- statement:
--   A **2-player turn-based discounted stochastic game** (2TBSG) $G = (S_1, S_2, A, \gamma)$ consists of a finite set $S$ of states, a finite set $A$ of actions and a discount factor $\gamma$ with $0 < \gamma < 1$. The states are partitioned into the set $S_1$ controlled by player 1 (the minimizer) and the set $S_2 = S \setminus S_1$ controlled by player 2 (the maximizer).
--
--   Every action $a$ is a triplet $(s(a), p(a), c(a))$: $s(a) \in S$ is the state from which $a$ can be played, $p(a)$ is a probability distribution on $S$ (the next state is drawn from it when $a$ is played), and $c(a) \in \mathbb{R}$ is the cost of $a$, paid by player 1 to player 2. Writing $P_{a,j} = p(a)_j$ for the **probability matrix** $P \in \mathbb{R}^{m \times n}$,
--   $$P_{a,j} \ge 0, \qquad \sum_{j \in S} P_{a,j} = 1 \quad \text{for every action } a.$$
--   For every state $i$ the set $A_i = \{a \in A : s(a) = i\}$ of actions playable from $i$ is nonempty. Throughout, $n = |S|$ and $m = |A|$; $m$ counts the actions of both players.
--
--   **Formalization Note.** `S1 : Finset S` is $S_1$; $S_2$ is its complement, so $S_1 \cap S_2 = \emptyset$ and $S = S_1 \cup S_2$ hold by construction. `src a` is $s(a)$, `P a j` is $P_{a,j}$, `c a` is $c(a)$. The standing assumptions $0 < \gamma < 1$, stochastic rows and $A_i \neq \emptyset$ are fields of the structure. `S` may be empty (the paper does not exclude it).
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 3, Definitions 2.1–2.3

import Mathlib

namespace TBSGStrategyIteration

/-- A 2-player turn-based discounted stochastic game `G = (S₁, S₂, A, γ)`
(Hansen–Miltersen–Zwick, arXiv:1008.0530v1, Definitions 2.1–2.3, pp. 3).

* `S` is the finite set of states, `A` the finite set of actions; `n = |S|`, `m = |A|`
  (`m` counts the actions of both players).
* `S1` is the set `S₁` of states controlled by player 1 (the minimizer); the states controlled
  by player 2 (the maximizer) are `S₂ = S \ S₁`, so `S₁ ∩ S₂ = ∅` and `S = S₁ ∪ S₂`.
* Every action `a` is a triplet `(s(a), p(a), c(a))`: `src a = s(a)` is the state from which
  `a` can be played, `P a` is the probability distribution `p(a)` of the next state
  (`P a j = P_{a,j}`, the probability matrix of Def. 2.3), and `c a = c(a)` is its cost.
* `γ` is the discount factor, `0 < γ < 1`.
* Every state has at least one action (`A_i ≠ ∅`). -/
structure Game (S A : Type*) [Fintype S] where
  /-- `S₁`: the states controlled by player 1; player 2 controls the complement `S₂`. -/
  S1 : Finset S
  /-- `s(a)`: the state from which action `a` can be played. -/
  src : A → S
  /-- `P a j = p(a)_j`: probability of moving to state `j` when `a` is played. -/
  P : A → S → ℝ
  P_nonneg : ∀ a j, 0 ≤ P a j
  P_sum_one : ∀ a, ∑ j, P a j = 1
  /-- `c(a)`: the cost of action `a` (paid by player 1 to player 2). -/
  c : A → ℝ
  /-- The discount factor. -/
  γ : ℝ
  γ_pos : 0 < γ
  γ_lt_one : γ < 1
  /-- `A_i = {a | s(a) = i}` is nonempty for every state `i`. -/
  actions_nonempty : ∀ i : S, ∃ a : A, src a = i

end TBSGStrategyIteration


