-- Prove2me | Definitions.Def_Supermodularity_Games_IsEquilibrium
-- name    : Supermodularity_Games_IsEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:30:35.528388+00:00
-- url     : https://prove2.me/theorems/81f87d43-6f28-48d1-bb83-18fb89097179
-- title:
--   An equilibrium point of a noncooperative game
-- statement:
--   With $S$ and $f$ as in `BestResponse`, a feasible joint strategy $x' \in S$ is an
--   **equilibrium point** if
--   $$
--   f_i(y_i, x'_{-i}) \;\le\; f_i(x') \qquad \text{for every player } i \text{ and every } y_i \in S_i(x'_{-i}).
--   $$
--   Equivalently, $x'_i \in Y_i(x'_{-i})$ for every player $i$: at an equilibrium point,
--   no player can strictly improve their own payoff by unilaterally deviating while
--   every other player's strategy stays fixed.
--
--   **Formalization Note** As in `BestResponse`, the deviation `y_i` is expressed by
--   substituting `y` for `x'`'s own `i`-th coordinate via `Function.update x' i y`,
--   matching the book's $f_i(y_i, x'_{-i})$.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 191, Chapter 4 (definition of an equilibrium point)

import Mathlib

namespace Supermodularity.Games

/-- `IsEquilibrium S f x'` says `x'` is an equilibrium point of the noncooperative
game with feasible joint strategy set `S` and payoff functions `f`: `x'` is
feasible, and no player `i` can strictly improve `f i` by unilaterally deviating
to any other feasible strategy `y`, the other players' strategies (`x'` with its
`i`-th coordinate overwritten) held fixed. -/
def IsEquilibrium {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (x' : ∀ i, Fin (m i) → ℝ) : Prop :=
  x' ∈ S ∧ ∀ i, ∀ y : Fin (m i) → ℝ, Function.update x' i y ∈ S →
    f i (Function.update x' i y) ≤ f i x'

end Supermodularity.Games


