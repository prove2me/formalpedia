-- Prove2me | Definitions.Def_CentralityGame_utility
-- name    : CentralityGame_utility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:19.18679+00:00
-- url     : https://prove2.me/theorems/74b2ac7b-efdc-4fda-9ee4-e33e7322827e
-- title:
--   Utility $u_i(x)$
-- statement:
--   The **utility** of a player $i$ in a configuration $x$ is the $i$-th entry of the PageRank centrality vector of $\mathcal G(x)$:
--
--   $$
--   u_i(x)=\pi_i(x),\qquad\pi(x)=(1-\beta)(I-\beta R^\top(x))^{-1}\eta.
--   $$
--
--   Each node thus wires its out-links to maximize its own centrality in the resulting graph.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §3, p.8

import Mathlib
import Definitions.Def_CentralityGame_pageRank

namespace CentralityGame

/-- The utility `u_i(x)` of player `i` in the configuration `x` (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §3, p.8):
the `i`-th entry of the PageRank centrality vector `π(x) = (1 - β) (I - β Rᵀ(x))⁻¹ η` of `G(x)`. -/
noncomputable def utility {V : Type*} [Fintype V] [DecidableEq V] (β : ℝ) (η : V → ℝ)
    (x : V → Finset V) (i : V) : ℝ :=
  pageRank x β η i

end CentralityGame


