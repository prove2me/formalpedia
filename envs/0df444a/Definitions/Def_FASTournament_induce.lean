-- Prove2me | Definitions.Def_FASTournament_induce
-- name    : FASTournament_induce
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:51.589885+00:00
-- url     : https://prove2.me/theorems/4b05d062-6668-429f-8cc8-21f47e5bdf4c
-- title:
--   Induced subdigraph $G[U]$
-- statement:
--   For a digraph $G=(V,A)$ and $U\subseteq V$, $G[U]$ is the **subgraph of $G$ induced by $U$**: its vertex set is $U$ and its arcs are the arcs of $G$ with both ends in $U$.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.5

import Mathlib

namespace FASTournament

/-- **Induced subdigraph `G[U]`.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.5: "For each U ⊆ V, we use G[U] to denote the subgraph of G induced by U."

The digraph on the vertices of `U` whose arcs are the arcs of `G` with both ends in `U`. -/
def induce {V : Type*} (G : Digraph V) (U : Set V) : Digraph U where
  Adj a b := G.Adj a b

end FASTournament


