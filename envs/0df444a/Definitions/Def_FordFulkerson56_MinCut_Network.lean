-- Prove2me | Definitions.Def_FordFulkerson56_MinCut_Network
-- name    : FordFulkerson56_MinCut_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T14:57:16.905993+00:00
-- url     : https://prove2.me/theorems/d92fc779-2bfd-4192-badd-1ed253df9a42
-- title:
--   Network: a finite graph with undirected (possibly parallel) arcs, a source, a sink and positive capacities
-- statement:
--   Following Ford and Fulkerson (§1, p. 399), a **graph** $G$ is a finite 1-dimensional complex made of **vertices** and **arcs**. Each arc joins two end vertices; arcs are undirected, and nothing prevents two different arcs from joining the same pair of vertices. Two distinct vertices are distinguished: the **source** $a$ and the **sink** $b$. Each arc $e$ carries a positive number $c(e)$, its **capacity**. The graph together with the capacities is a **network** $N$.
--
--   Formally, a network consists of
--
--   1. a vertex type $V$ and an arc type $E$;
--   2. for each arc $e$, two end vertices $\mathrm{tail}(e)\neq \mathrm{head}(e)$;
--   3. a source $a\in V$ and a sink $b\in V$ with $a\neq b$;
--   4. a capacity $c : E\to\mathbb R$ with $c(e)>0$ for every arc $e$.
--
--   This is the common model for every statement of the mission: chains, flows, disconnecting sets and cuts are all defined from it.
--
--   **Formalization Note** The names `tail` and `head` are labels for the two end vertices only; no direction is implied, and chains may traverse an arc either way. Arcs form a type, so parallel arcs are allowed, as in the paper's 1-complex. The requirement $\mathrm{tail}(e)\neq\mathrm{head}(e)$ (no loops) reflects that an arc of a 1-complex has two end vertices; a loop could lie on no chain anyway. Finiteness of $V$ and $E$ is imposed by `Fintype` instances in the statements that use the network.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 399, §1, definitions of graph, arc, source, sink, capacity and network

import Mathlib

namespace FordFulkerson56.MinCut

/-- A network in the sense of Ford and Fulkerson (1956), §1, p. 399: a finite graph whose arcs form a
type `E` (so two arcs may have the same end vertices), each arc `e` having two distinct end vertices
`tail e` and `head e` (the names are labels only: arcs are undirected), a distinguished source and sink,
which are two distinct vertices, and a positive capacity on every arc. -/
structure Network (V E : Type*) where
  tail : E → V
  head : E → V
  tail_ne_head : ∀ e, tail e ≠ head e
  source : V
  sink : V
  source_ne_sink : source ≠ sink
  cap : E → ℝ
  cap_pos : ∀ e, 0 < cap e

end FordFulkerson56.MinCut


