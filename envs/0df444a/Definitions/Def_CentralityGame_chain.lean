-- Prove2me | Definitions.Def_CentralityGame_chain
-- name    : CentralityGame_chain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:40.423453+00:00
-- url     : https://prove2.me/theorems/f84c32e8-ed8b-4ada-a7b4-53208aeaaf77
-- title:
--   PageRank Markov chain $P$
-- statement:
--   The **transition matrix** of the PageRank random walk is
--
--   $$
--   P=\beta R+(1-\beta)\mathbf 1\eta^\top,\qquad\text{that is,}\qquad P_{jk}=\beta R_{jk}+(1-\beta)\eta_k.
--   $$
--
--   From $j$, with probability $\beta$ the next state is uniform among the out-neighbours of $j$, and with probability $1-\beta$ it is sampled from $\eta$. All hitting times of the mission are those of this chain.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §2, (3), p.6, and p.7

import Mathlib
import Definitions.Def_CentralityGame_normAdj

namespace CentralityGame

/-- The stochastic matrix of (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §2, (3), p.6): `P = β R + (1 - β) 1 ηᵀ`, that is,
`P_jk = β R_jk + (1 - β) η_k`. This is the transition matrix of the chain `(V_t)` of p.7. -/
noncomputable def chain {V : Type*} [DecidableEq V] (N : V → Finset V) (β : ℝ) (η : V → ℝ) :
    Matrix V V ℝ :=
  Matrix.of fun j k => β * normAdj N j k + (1 - β) * η k

end CentralityGame


