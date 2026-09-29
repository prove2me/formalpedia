-- Prove2me | Definitions.Def_CoresConvexGames_Stability_IsFeasible
-- name    : CoresConvexGames_Stability_IsFeasible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:45:59.729989+00:00
-- url     : https://prove2.me/theorems/3d937a65-c56d-49f3-936d-ac7839da9f0e
-- title:
--   Feasible payoff vector: $a(N) \le v(N)$
-- statement:
--   Let $N$ be a finite set of players and $v$ a game on the subsets of $N$. For a payoff vector $a\in\mathbb R^N$ write $a(S)=\sum_{i\in S}a_i$. The vector $a$ is **feasible** for $v$ if
--
--   $$
--   a(N)\le v(N).
--   $$
--
--   Feasible vectors are the ones the grand coalition can actually pay out. Stable sets (von Neumann–Morgenstern solutions) are defined in this paper as sets of feasible vectors, and dominance is tested against every feasible vector.
--
--   **Formalization Note** Players are `Fin n` and a game is `f : Finset (Fin n) → ℝ`. The paper's footnote mentions an optional lower bound on $a(N)$ that it does not use; only the upper bound is encoded, as in the paper.
-- source:
--   Shapley, Cores of Convex Games, Int. J. Game Theory 1, 1971, https://doi.org/10.1007/BF01753431, p. 16, §3, first paragraph (definition of feasible)

import Mathlib

namespace CoresConvexGames.Stability

/-- Shapley (1971), p. 16, §3: a payoff vector `a ∈ E^N` is *feasible* for the game `v`
if `a(N) ≤ v(N)`. Players are `Fin n`, a game is `f : Finset (Fin n) → ℝ`, and
`a(S) = ∑ i ∈ S, a i`. -/
def IsFeasible {n : ℕ} (f : Finset (Fin n) → ℝ) (a : Fin n → ℝ) : Prop :=
  ∑ i, a i ≤ f Finset.univ

end CoresConvexGames.Stability


