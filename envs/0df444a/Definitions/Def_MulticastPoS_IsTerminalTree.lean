-- Prove2me | Definitions.Def_MulticastPoS_IsTerminalTree
-- name    : MulticastPoS_IsTerminalTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:52.85802+00:00
-- url     : https://prove2.me/theorems/42571588-1b41-4eca-9c77-d2df3c96015a
-- title:
--   Tree connecting all sources to the sink
-- statement:
--   A subgraph $S$ of $G$ is a **tree connecting all sources to $t$** if $S$ is a tree (connected and acyclic on its own vertex set), $t\in V(S)$, and $s_i\in V(S)$ for every player $i$.
--
--   The optimal tree $T^\star$ is a cheapest such tree, and $OPT=c(T^\star)$. The grouping procedure of Section 4.1 runs on any such tree.
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Section 1, p.1; Section 4.1, p.8

import Mathlib

namespace MulticastPoS

/-- A tree connecting all sources to the sink (Huang–Yuan, *An O(log log n) Upper Bound on the
Price of Stability for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript
(sha256 dd0e08d0…f6d4), Section 1, p.1): a subgraph `S` of `G` that is a tree and contains the
sink `t` and every source `s i`. The optimal tree `T⋆` is a cheapest one, and `OPT = c(T⋆)`.

**Formalization Note** `S.coe.IsTree` asks the subgraph, as a graph on its own vertex set, to be
connected and acyclic. -/
def IsTerminalTree {V ι : Type*} (G : SimpleGraph V) (t : V) (s : ι → V) (S : G.Subgraph) :
    Prop :=
  S.coe.IsTree ∧ t ∈ S.verts ∧ ∀ i, s i ∈ S.verts

end MulticastPoS


