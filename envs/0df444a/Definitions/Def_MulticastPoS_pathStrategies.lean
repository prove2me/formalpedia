-- Prove2me | Definitions.Def_MulticastPoS_pathStrategies
-- name    : MulticastPoS_pathStrategies
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:37.557069+00:00
-- url     : https://prove2.me/theorems/2db06bfc-3c90-46ad-8c51-0ae986652bdd
-- title:
--   Strategies of the multicast game: simple source–sink paths
-- statement:
--   Let $G=(V,E)$ be a finite undirected graph, $t\in V$ the common **sink**, and $s_i\in V$ the **source** of player $i$. Player $i$ chooses a **simple path** $P_i$ from $s_i$ to $t$, recorded as its set of edges. The strategy family of player $i$ is
--
--   $$
--   \Sigma_i=\{\,E(p) : p \text{ a simple } s_i\text{–}t \text{ path in } G\,\}.
--   $$
--
--   A player whose source is $t$ has exactly one strategy, the empty path.
--
--   These are the strategy sets of the undirected multicast Shapley network design game; they are connecting *paths*, not arbitrary connecting edge sets.
--
--   **Formalization Note** The graph is a `SimpleGraph` on a finite vertex type, edges are elements of `Sym2 V`, and a simple path is a walk with `IsPath`; the strategy is the finite set `p.edges.toFinset`.
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Section 1, p.1; Section 2, p.4

import Mathlib

namespace MulticastPoS

/-- The strategies of player `i` (Huang–Yuan, *An O(log log n) Upper Bound on the Price of
Stability for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript (sha256
dd0e08d0…f6d4), Section 1, p.1): player `i` chooses a simple path `Pᵢ` from their source `sᵢ` to
the common sink `t` in the finite undirected graph `G`. A strategy is recorded as the edge set
of such a path.

**Formalization Note** "Finite undirected graph" is a `SimpleGraph` on a `Fintype` of vertices;
edges are elements of `Sym2 V`. A simple path is a `G.Walk (s i) t` with `IsPath`, and the
strategy is its set of edges `p.edges.toFinset`. A player with `s i = t` has exactly one
strategy, the empty path `∅` (Section 2, p.4). -/
noncomputable def pathStrategies {V ι : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : V) (s : ι → V) : ι → Finset (Finset (Sym2 V)) :=
  fun i => (Set.toFinite
    {F : Finset (Sym2 V) | ∃ p : G.Walk (s i) t, p.IsPath ∧ p.edges.toFinset = F}).toFinset

end MulticastPoS


