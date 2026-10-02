-- Prove2me | Definitions.Def_TheoryOfGames_PerfectInfo_Strategy
-- name    : TheoryOfGames_PerfectInfo_Strategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T01:51:27.679245+00:00
-- url     : https://prove2.me/theorems/9be57715-f47b-4932-a713-e3bb3d635fea
-- title:
--   Pure strategies and the normalized form $\mathcal H(\tau_1,\tau_2)$ of a game tree (11.1.1, 11.2.3)
-- statement:
--   Let $\Gamma$ be a finite zero-sum two-person game with perfect information, given as a game tree.
--
--   A **pure strategy** $\tau_1$ of player 1 is a complete plan: it specifies an alternative at every personal move of player 1 in the tree, whether or not that move is reached in a given play. A pure strategy $\tau_2$ of player 2 does the same at every personal move of player 2. Equivalently, following 15.4.2 and 15.5.1: in a game of length $0$ each player has exactly one strategy; if the first move is a chance move or a move of the opponent, a strategy of player $k$ specifies a strategy of player $k$ in every $\Gamma_{\sigma_1}$; if it is a move of player $k$, a strategy specifies an alternative $\sigma_1^0$ together with a strategy of player $k$ in every $\Gamma_{\sigma_1}$.
--
--   Each player has finitely many pure strategies, and at least one.
--
--   The **normalized form** is the function
--   $$\mathcal H(\tau_1, \tau_2) = \text{the mathematical expectation of the payoff } \mathfrak F_1(\pi) \text{ to player 1}$$
--   of the play $\pi$ produced when player 1 uses $\tau_1$ and player 2 uses $\tau_2$, the expectation being over the chance moves. Recursively: at a leaf $w$ it is $w$; at a chance move it is $\sum_{\sigma_1} p_1(\sigma_1)\, \mathcal H_{\sigma_1}(\tau_{\sigma_1/1}, \tau_{\sigma_1/2})$, the formula of 15.4.2; at a personal move it is $\mathcal H$ of the subgame chosen by the moving player's strategy. Player 2 receives $-\mathcal H(\tau_1, \tau_2)$.
--
--   This is the passage from the extensive to the normalized form (§11) on which the definitions of $v_1$ and $v_2$ rest.
--
--   **Formalization Note** A strategy is a dependent type defined by recursion on the tree (`Strategy1 t`, `Strategy2 t`), with `Fintype` and `Nonempty` instances by the same recursion. At its own move a strategy stores a choice and a sub-strategy for every subgame, including those its choice excludes; the book's description in 15.5.1 keeps only the chosen subgame. The two descriptions give the same set of functions $\tau_2 \mapsto \mathcal H(\tau_1, \tau_2)$ (duplicated rows), so the same $v_1$ and $v_2$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 79, 11.1.1; p. 83, 11.2.3; p. 98, 14.1.1; pp. 118–121, 15.4.2, 15.5.1

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_GameTree

namespace TheoryOfGames.PerfectInfo

namespace GameTree

/-- A pure strategy of player 1: a complete plan choosing an alternative at every personal
move of player 1 in the tree, reached or not. -/
def Strategy1 : GameTree → Type
  | leaf _ => Unit
  | chance α _ next _ _ => (σ : Fin α) → Strategy1 (next σ)
  | move1 α _ next => Fin α × ((σ : Fin α) → Strategy1 (next σ))
  | move2 α _ next => (σ : Fin α) → Strategy1 (next σ)

/-- A pure strategy of player 2: a complete plan choosing an alternative at every personal
move of player 2 in the tree, reached or not. -/
def Strategy2 : GameTree → Type
  | leaf _ => Unit
  | chance α _ next _ _ => (σ : Fin α) → Strategy2 (next σ)
  | move1 α _ next => (σ : Fin α) → Strategy2 (next σ)
  | move2 α _ next => Fin α × ((σ : Fin α) → Strategy2 (next σ))

/-- Each player has finitely many pure strategies. -/
instance instFintypeStrategy1 : (t : GameTree) → Fintype (Strategy1 t)
  | leaf _ => inferInstanceAs (Fintype Unit)
  | chance α _ next _ _ =>
      letI := fun σ => instFintypeStrategy1 (next σ)
      inferInstanceAs (Fintype ((σ : Fin α) → Strategy1 (next σ)))
  | move1 α _ next =>
      letI := fun σ => instFintypeStrategy1 (next σ)
      inferInstanceAs (Fintype (Fin α × ((σ : Fin α) → Strategy1 (next σ))))
  | move2 α _ next =>
      letI := fun σ => instFintypeStrategy1 (next σ)
      inferInstanceAs (Fintype ((σ : Fin α) → Strategy1 (next σ)))

instance instFintypeStrategy2 : (t : GameTree) → Fintype (Strategy2 t)
  | leaf _ => inferInstanceAs (Fintype Unit)
  | chance α _ next _ _ =>
      letI := fun σ => instFintypeStrategy2 (next σ)
      inferInstanceAs (Fintype ((σ : Fin α) → Strategy2 (next σ)))
  | move1 α _ next =>
      letI := fun σ => instFintypeStrategy2 (next σ)
      inferInstanceAs (Fintype ((σ : Fin α) → Strategy2 (next σ)))
  | move2 α _ next =>
      letI := fun σ => instFintypeStrategy2 (next σ)
      inferInstanceAs (Fintype (Fin α × ((σ : Fin α) → Strategy2 (next σ))))

/-- Each player has at least one pure strategy (every personal move has `α ≥ 1`). -/
instance instNonemptyStrategy1 : (t : GameTree) → Nonempty (Strategy1 t)
  | leaf _ => inferInstanceAs (Nonempty Unit)
  | chance α _ next _ _ =>
      letI := fun σ => instNonemptyStrategy1 (next σ)
      inferInstanceAs (Nonempty ((σ : Fin α) → Strategy1 (next σ)))
  | move1 α hα next =>
      letI := fun σ => instNonemptyStrategy1 (next σ)
      letI : Nonempty (Fin α) := ⟨⟨0, hα⟩⟩
      inferInstanceAs (Nonempty (Fin α × ((σ : Fin α) → Strategy1 (next σ))))
  | move2 α _ next =>
      letI := fun σ => instNonemptyStrategy1 (next σ)
      inferInstanceAs (Nonempty ((σ : Fin α) → Strategy1 (next σ)))

instance instNonemptyStrategy2 : (t : GameTree) → Nonempty (Strategy2 t)
  | leaf _ => inferInstanceAs (Nonempty Unit)
  | chance α _ next _ _ =>
      letI := fun σ => instNonemptyStrategy2 (next σ)
      inferInstanceAs (Nonempty ((σ : Fin α) → Strategy2 (next σ)))
  | move1 α _ next =>
      letI := fun σ => instNonemptyStrategy2 (next σ)
      inferInstanceAs (Nonempty ((σ : Fin α) → Strategy2 (next σ)))
  | move2 α hα next =>
      letI := fun σ => instNonemptyStrategy2 (next σ)
      letI : Nonempty (Fin α) := ⟨⟨0, hα⟩⟩
      inferInstanceAs (Nonempty (Fin α × ((σ : Fin α) → Strategy2 (next σ))))

/-- The normalized form `ℋ(τ₁, τ₂)`: the mathematical expectation, over the chance moves, of
the payoff to player 1 of the play produced when player 1 uses `τ₁` and player 2 uses `τ₂`. -/
def payoff : (t : GameTree) → Strategy1 t → Strategy2 t → ℝ
  | leaf w, _, _ => w
  | chance _ p next _ _, τ₁, τ₂ => ∑ σ, p σ * payoff (next σ) (τ₁ σ) (τ₂ σ)
  | move1 _ _ next, τ₁, τ₂ => payoff (next τ₁.1) (τ₁.2 τ₁.1) (τ₂ τ₁.1)
  | move2 _ _ next, τ₁, τ₂ => payoff (next τ₂.1) (τ₁ τ₂.1) (τ₂.2 τ₂.1)

end GameTree

end TheoryOfGames.PerfectInfo


