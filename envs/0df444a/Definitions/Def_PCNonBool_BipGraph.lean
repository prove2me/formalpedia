-- Prove2me | Definitions.Def_PCNonBool_BipGraph
-- name    : PCNonBool_BipGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:59.573203+00:00
-- url     : https://prove2.me/theorems/f3f1a40c-370e-40fc-9b59-a67da4e4c3da
-- title:
--   Bipartite graph $G=(U\sqcup V,E)$ with decidable adjacency
-- statement:
--   A **bipartite graph** $G=(U\sqcup V,E)$ consists of a set $U$ of left vertices (the *pigeons*), a set $V$ of right vertices (the *holes*), and a set $E\subseteq U\times V$ of edges. Graphs are simple: there is at most one edge between a pigeon and a hole, and no edge joins two vertices of the same side.
--
--   This is the vertex and edge structure on which the graph functional pigeonhole principle FPHP($G$) and boundary expansion are defined.
--
--   **Formalization Note** $U$ and $V$ are types and $E$ is a decidable relation `Adj : U → V → Prop`.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.2 (Graph Theory, Basics), p.10 (PDF p.13)

import Mathlib

namespace PCNonBool

/-- A bipartite graph `G = (U ⊔ V, E)` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.2, p.10 (PDF p.13)): the pigeons are the
vertices of `U`, the holes the vertices of `V`, and `Adj i j` says that `(i, j)` is an edge.

**Formalization Note** The two sides are types `U` and `V`, and the edge set is a relation, so the
graph is simple ("all graphs in this paper are simple", p.10) and every edge has one endpoint on
each side. Adjacency is decidable so that neighbourhoods and boundaries are finite sets. -/
structure BipGraph (U V : Type*) where
  /-- `Adj i j`: pigeon `i` and hole `j` are adjacent -/
  Adj : U → V → Prop
  /-- adjacency is decidable -/
  [decAdj : DecidableRel Adj]

attribute [instance] BipGraph.decAdj

end PCNonBool


