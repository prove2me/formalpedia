-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_ThresholdRanking
-- name    : FlowAllocationGames_UnitRanking_ThresholdRanking
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:14:55.402982+00:00
-- url     : https://prove2.me/theorems/39dc5253-f78e-4bc0-8620-5730751fdbef
-- title:
--   Threshold-ranking data
-- statement:
--   In a **threshold-ranking strategy**, every player $v$ chooses a permutation $\pi_v$ of its outgoing edges $E^+(v)$ and a threshold $\tau_e$ for every edge $e \in E^+(v)$. The data of a whole profile is a list of all edges (a global order, whose restriction to $E^+(v)$ is $\pi_v$) and the thresholds $\tau_e$, one per edge.
--
--   This is the compact representation of the strong equilibrium of Theorem 9.
--
--   **Formalization Note** Every family of per-player permutations is the restriction of a global order of the edges, and conversely.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23

import Mathlib

namespace FlowAllocationGames.UnitRanking

/-- **Threshold-ranking data.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23: "In a threshold-ranking strategy, every firm v chooses a permutation πv over E⁺(v) and
thresholds τe."

A threshold ranking is a pair `(ord, τ)` of a list of edges `ord` (a global order of the edges)
and thresholds `τ e`, one per edge. The permutation `πv` of player `v` is `ord` restricted to the
edges with tail `v`.

**Formalization Note.** Every family of per-player permutations `(πv)v∈V` is the restriction of a
global order of the edges, and conversely, so the encoding loses nothing. -/
abbrev ThresholdRanking (m : ℕ) : Type := List (Fin m) × (Fin m → ℕ)

end FlowAllocationGames.UnitRanking


