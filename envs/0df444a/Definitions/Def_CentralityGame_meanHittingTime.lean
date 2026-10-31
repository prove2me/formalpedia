-- Prove2me | Definitions.Def_CentralityGame_meanHittingTime
-- name    : CentralityGame_meanHittingTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:42.915998+00:00
-- url     : https://prove2.me/theorems/0f5ee997-3033-4546-b4d9-1b51167144cf
-- title:
--   Averaged hitting time $\tau^i_\eta$
-- statement:
--   The expected hitting time of $i$ from a start sampled from $\eta$ is
--
--   $$
--   \tau^i_\eta=\sum_{j\in\mathcal V}\eta_j\tau^i_j.
--   $$
--
--   It appears in the system (4) and in the PageRank formula (5).
-- source:
--   Catalano, Castaldo, Como, Fagnani, On a Network Centrality Maximization Game, arXiv:2211.03685v3, Lemma 1, (5), p.7

import Mathlib
import Definitions.Def_CentralityGame_hittingTime

namespace CentralityGame

/-- The quantity `τ^i_η = ∑_{j ∈ V} η_j τ^i_j` of (Catalano, Castaldo, Como, Fagnani, *On a Network Centrality Maximization Game*, arXiv:2211.03685v3, Lemma 1, (5), p.7). -/
noncomputable def meanHittingTime {V : Type*} [Fintype V] [DecidableEq V] (N : V → Finset V)
    (β : ℝ) (η : V → ℝ) (i : V) : ℝ :=
  ∑ j, η j * hittingTime N β η i j

end CentralityGame


