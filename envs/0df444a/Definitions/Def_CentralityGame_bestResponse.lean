-- Prove2me | Definitions.Def_CentralityGame_bestResponse
-- name    : CentralityGame_bestResponse
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:27.402988+00:00
-- url     : https://prove2.me/theorems/31aec679-be23-48b7-8957-f1a1c97bcba8
-- title:
--   Best response set $\mathcal B_i(x_{-i})$
-- statement:
--   The **best response set** of a player $i$ to an action profile $x_{-i}$ of the other players is
--
--   $$
--   \mathcal B_i(x_{-i})=\{a\in\mathcal A_i\mid u_i(a,x_{-i})\ge u_i(b,x_{-i}),\ \forall b\in\mathcal A_i\}.
--   $$
--
--   It is the set of actions that maximize the player's PageRank centrality given the others' choices. Theorem 1 describes its structure.
--
--   **Formalization Note** The argument is a full configuration $x$, and $(a,x_{-i})$ is the configuration with coordinate $i$ replaced by $a$, so the set depends on $x_{-i}$ only. It is defined through utilities, not hitting times; the characterization by hitting times is Proposition 2.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §3, p.8

import Mathlib
import Definitions.Def_CentralityGame_IsAction
import Definitions.Def_CentralityGame_utility

namespace CentralityGame

/-- The **best response set** of player `i` (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §3, p.8):
`B_i(x_{-i}) = {a ∈ A_i | u_i(a, x_{-i}) ≥ u_i(b, x_{-i}), ∀ b ∈ A_i}`.

**Formalization Note** The argument is the full configuration `x`; `(a, x_{-i})` is
`Function.update x i a`, so the coordinate `x i` is overwritten and `bestResponse` depends on
`x_{-i}` only. It is defined from utilities, not from hitting times. -/
def bestResponse {V : Type*} [Fintype V] [DecidableEq V] (d : V → ℕ) (β : ℝ) (η : V → ℝ)
    (x : V → Finset V) (i : V) : Set (Finset V) :=
  {a | IsAction d i a ∧ ∀ b, IsAction d i b →
    utility β η (Function.update x i b) i ≤ utility β η (Function.update x i a) i}

end CentralityGame


