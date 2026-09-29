-- Prove2me | Definitions.Def_CoresConvexGames_Stability_Dominates
-- name    : CoresConvexGames_Stability_Dominates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:48:00.957287+00:00
-- url     : https://prove2.me/theorems/3434de1f-9d18-4a74-a4f5-4965030bf349
-- title:
--   Domination of payoff vectors (21)
-- statement:
--   Let $N$ be a finite set of players, $v$ a game, and $a(S)=\sum_{i\in S}a_i$. A payoff vector $b$ is **dominated** by a payoff vector $a$ if there is a nonempty coalition $S\subseteq N$ such that
--
--   $$
--   a(S)\le v(S)\quad\text{and}\quad a_i>b_i\ \text{ for all } i\in S .
--   $$
--
--   That is, the coalition $S$ can by itself secure its share under $a$, and every member of $S$ strictly prefers $a$ to $b$. Domination is the relation on which von Neumann–Morgenstern stable sets are built.
--
--   **Formalization Note** `Dominates f a b` reads "$a$ dominates $b$". Players are `Fin n` and a game is `f : Finset (Fin n) → ℝ`. The coalition must be nonempty and the coordinate inequalities are strict, as on the page.
-- source:
--   Shapley, Cores of Convex Games, Int. J. Game Theory 1, 1971, https://doi.org/10.1007/BF01753431, p. 24, §4.3, condition (21)

import Mathlib

namespace CoresConvexGames.Stability

/-- Shapley (1971), p. 24, §4.3, (21): `Dominates f a b` says the payoff vector `b` is
*dominated* by the payoff vector `a`: there is a nonempty coalition `S` with
`a(S) ≤ v(S)` and `a_i > b_i` for all `i ∈ S`. -/
def Dominates {n : ℕ} (f : Finset (Fin n) → ℝ) (a b : Fin n → ℝ) : Prop :=
  ∃ S : Finset (Fin n), S.Nonempty ∧ ∑ i ∈ S, a i ≤ f S ∧ ∀ i ∈ S, b i < a i

end CoresConvexGames.Stability


