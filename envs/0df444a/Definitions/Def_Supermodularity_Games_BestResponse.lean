-- Prove2me | Definitions.Def_Supermodularity_Games_BestResponse
-- name    : Supermodularity_Games_BestResponse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:29:33.571207+00:00
-- url     : https://prove2.me/theorems/ebeb9d0c-cd31-40b5-b563-ca342d106017
-- title:
--   Player i's best-response set Y_i(x_{-i}) in a noncooperative game
-- statement:
--   Consider a **noncooperative game** $(N, S, \{f_i : i \in N\})$: a finite player set
--   $N$, a set $S$ of **feasible joint strategies** (each a tuple $x = (x_i)_{i \in N}$
--   with $x_i$ player $i$'s own strategy, here $x_i \in \mathbb{R}^{m_i}$), and a payoff
--   function $f_i$ for each player $i$. Write $x_{-i}$ for the strategies of every
--   player but $i$, and $S_i(x_{-i}) = \{y_i : (y_i, x_{-i}) \in S\}$ for the **section**
--   of $S$ at $x_{-i}$ — player $i$'s feasible strategies when the others play
--   $x_{-i}$.
--
--   Player $i$'s **best-response set** is
--   $$
--   Y_i(x_{-i}) \;=\; \operatorname*{argmax}_{y_i \in S_i(x_{-i})} f_i(y_i, x_{-i}),
--   $$
--   the set of feasible $y_i$ maximizing $f_i$ against the reference $x_{-i}$.
--
--   **Formalization Note** A joint strategy is `∀ i, Fin (m i) → ℝ` (a dependent
--   function assigning each player their own $\mathbb{R}^{m_i}$-valued strategy), and
--   `x_{-i}` is represented implicitly: `BestResponse` takes a full joint strategy `x`
--   and only ever reads its coordinates other than `i`, since every feasible-set and
--   payoff membership test substitutes in a candidate `y` for `x`'s own `i`-th
--   coordinate via `Function.update x i y`. This mirrors the book's own convention that
--   $f_i(y_i, x_{-i})$ ignores whatever value $x_i$ itself carried.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 178, Chapter 4 (definition of the best-response correspondence)

import Mathlib

namespace Supermodularity.Games

/-- `BestResponse S f i x` is player `i`'s best-response set `Y_i(x_{-i})` in the
noncooperative game with feasible joint strategy set `S` and payoff functions `f`:
the set of `y` maximizing `f i` over the feasible section of `S` at `x_{-i}`, where
`x` supplies the other players' strategies and its own `i`-th coordinate is
ignored (overwritten by `y`). -/
def BestResponse {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℕ}
    (S : Set (∀ i, Fin (m i) → ℝ)) (f : ι → (∀ i, Fin (m i) → ℝ) → ℝ)
    (i : ι) (x : ∀ i, Fin (m i) → ℝ) : Set (Fin (m i) → ℝ) :=
  {y : Fin (m i) → ℝ | Function.update x i y ∈ S ∧
    ∀ z : Fin (m i) → ℝ, Function.update x i z ∈ S →
      f i (Function.update x i z) ≤ f i (Function.update x i y)}

end Supermodularity.Games


