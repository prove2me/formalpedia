-- Prove2me | Definitions.Def_TheoryOfGames_PerfectInfo_GameTree
-- name    : TheoryOfGames_PerfectInfo_GameTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T01:43:24.937825+00:00
-- url     : https://prove2.me/theorems/b4537d3b-0474-4d1c-b96f-83063e565487
-- title:
--   Zero-sum two-person game with perfect information as a finite game tree (§6, 15.1–15.3)
-- statement:
--   A **zero-sum two-person game with perfect information** $\Gamma$ is described here as a finite rooted tree. Every node is of one of four kinds.
--
--   1. A **leaf** $w$: the play has ended; player 1 receives the amount $\mathfrak F_1(\pi) = w \in \mathbb R$ and player 2 receives $-w$ (the game is zero-sum).
--   2. A **chance move** with $\alpha$ alternatives $\sigma = 1, \dots, \alpha$, chosen with probabilities $p(\sigma)$, where
--   $$p(\sigma) \geqq 0, \qquad \sum_{\sigma=1}^{\alpha} p(\sigma) = 1,$$
--   after which the game continues as the subtree $\Gamma_\sigma$.
--   3. A **personal move of player 1** with $\alpha \geqq 1$ alternatives, after each of which the game continues as $\Gamma_\sigma$.
--   4. A **personal move of player 2** with $\alpha \geqq 1$ alternatives, likewise.
--
--   The file also defines, for a game $\Gamma$, the set of games $\Gamma_{\sigma_1}$ ($\sigma_1 = 1, \dots, \alpha_1$) that remain after its first move $\mathfrak M_1$ has been made; it is empty for a game of length $0$ (a leaf).
--
--   Because every personal move is a node of the tree, the player making it knows the outcome of every earlier move: preliminarity and anteriority coincide, which is the book's definition of perfect information (6.4.1, 14.8). By (15:B) this is exactly the condition under which the whole sequence of games $\Gamma, \Gamma_{\sigma_1}, \Gamma_{\sigma_1,\sigma_2}, \dots$ of (15:1) can be formed, and that sequence is the tree.
--
--   **Formalization Note** The book's formal model (§§9–10) describes a game by partitions of the set of plays; this tree restates it for the perfect-information case and does not formalize §§9–10. Alternatives are numbered $0, \dots, \alpha - 1$ (`Fin α`) instead of $1, \dots, \alpha$. The number of alternatives, the kind of each move and the chance probabilities may depend on the earlier moves, as in the book ($\alpha_2 = \alpha_2(\sigma_1)$, $k_2(\sigma_1)$). The book fixes one length $\nu$ for all plays; the tree allows plays of different lengths, which contains the book's games (all leaves at depth $\nu$) as a special case. The conditions $\alpha \geqq 1$ at personal moves and $p \geqq 0$, $\sum p = 1$ at chance moves are fields of the constructors, so every tree satisfies them.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 51, 6.4.1; pp. 112–117, 15.1–15.3, (15:1), (15:B)

import Mathlib

namespace TheoryOfGames.PerfectInfo

/-- A finite zero-sum two-person game with perfect information, as a finite game tree.
A `leaf w` is a play that has ended, with payoff `w = 𝔉₁(π)` to player 1 (player 2 receives `-w`).
An internal node is a move `𝔐` with alternatives `σ : Fin α`:
* `chance α p next hp hsum` — a chance move whose alternative `σ` has probability `p σ`
  (`p σ ≥ 0`, `∑ σ, p σ = 1`), after which the game continues as `next σ`;
* `move1 α hα next` — a personal move of player 1 with `α ≥ 1` alternatives;
* `move2 α hα next` — a personal move of player 2 with `α ≥ 1` alternatives. -/
inductive GameTree : Type
  | leaf (w : ℝ) : GameTree
  | chance (α : ℕ) (p : Fin α → ℝ) (next : Fin α → GameTree)
      (hp : ∀ σ, 0 ≤ p σ) (hsum : ∑ σ, p σ = 1) : GameTree
  | move1 (α : ℕ) (hα : 0 < α) (next : Fin α → GameTree) : GameTree
  | move2 (α : ℕ) (hα : 0 < α) (next : Fin α → GameTree) : GameTree

namespace GameTree

/-- The games `Γ_{σ₁}` that remain after the first move `𝔐₁` of `Γ` (empty for a game of
length zero). -/
def firstMoveSubgames : GameTree → Set GameTree
  | leaf _ => ∅
  | chance _ _ next _ _ => Set.range next
  | move1 _ _ next => Set.range next
  | move2 _ _ next => Set.range next

end GameTree

end TheoryOfGames.PerfectInfo


