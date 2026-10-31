-- Prove2me | Definitions.Def_CentralityGame_normAdj
-- name    : CentralityGame_normAdj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:11:43.994049+00:00
-- url     : https://prove2.me/theorems/dd884414-e0fa-4b10-ac04-d030735e5054
-- title:
--   Normalized adjacency matrix $R$
-- statement:
--   The **normalized adjacency matrix** of a graph is the matrix $R\in\mathbb R^{\mathcal V\times\mathcal V}$ with entries
--
--   $$
--   R_{ij}=\begin{cases}1/d_i&\text{if } j\in\mathcal N_i,\\ 0&\text{if } j\in\mathcal V\setminus\mathcal N_i.\end{cases}
--   $$
--
--   For a graph it is row-stochastic, and it gives the random-walk part of the PageRank chain.
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, §2, (1), p.6

import Mathlib

namespace CentralityGame

/-- The **normalized adjacency matrix** `R` of (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, §2, (1), p.6):
`R_ij = 1 / d_i` if `j ∈ N_i` and `R_ij = 0` if `j ∈ V ∖ N_i`. -/
noncomputable def normAdj {V : Type*} [DecidableEq V] (N : V → Finset V) : Matrix V V ℝ :=
  Matrix.of fun i j => if j ∈ N i then 1 / ((N i).card : ℝ) else 0

end CentralityGame


