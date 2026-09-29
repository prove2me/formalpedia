-- Prove2me | Definitions.Def_NagamochiIbaraki_NodeConn_Multigraph
-- name    : NagamochiIbaraki_NodeConn_Multigraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:06:54.643784+00:00
-- url     : https://prove2.me/theorems/b0102cd9-a30a-4781-9172-7d95710aea44
-- title:
--   Graphs as edge maps into unordered node pairs, and the subgraph (V, F) spanned by an edge set F
-- statement:
--   A graph $G = (V, E)$ is given by a finite set of nodes $V$, a finite set of edges $E$, and for each edge $e \in E$ the unordered pair of its end nodes. Different edges may have the same pair of end nodes (parallel edges); an edge whose two end nodes coincide (a self-loop) is excluded by a separate hypothesis wherever the paper assumes it, and a graph is **simple** when no two edges have the same pair of end nodes.
--
--   For a set of edges $F \subseteq E$, the spanning subgraph $(V, F)$ has all nodes of $G$ and only the edges of $F$. This definition records which pairs of nodes are joined by at least one edge of $F$:
--
--   $$
--   u \sim_F v \iff u \neq v \text{ and some } e \in F \text{ has end nodes } \{u, v\}.
--   $$
--
--   Adjacency, paths and connectivity "in $F$" (or "in $(V, F)$") always refer to this graph. Multiplicities of parallel edges do not affect adjacency or connectivity.
--
--   **Formalization Note** The graph is a map `ends : E → Sym2 V`; the spanning subgraph is `edgeGraph ends F := SimpleGraph.fromEdgeSet (ends '' F)`, a Mathlib simple graph on `V`. Loop-freeness is the hypothesis `∀ e, ¬ (ends e).IsDiag` and simplicity is `Function.Injective ends`, both carried by the theorems.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), p. 583, §1 (standing assumptions); p. 589, §3 (simple graphs)

import Mathlib

namespace NagamochiIbaraki.NodeConn

/-! Finite graphs (Nagamochi–Ibaraki 1992, p. 583 and §3, p. 589).

A graph `G = (V, E)` is encoded by a node type `V`, an edge type `E` and the map
`ends : E → Sym2 V` sending each edge to its unordered pair of end nodes. Self-loops are
excluded by the hypothesis `∀ e, ¬ (ends e).IsDiag` carried by the theorems, and simplicity
(no two edges with the same pair of end nodes, assumed throughout §3) is
`Function.Injective ends`. An edge subset is a `Finset E`. -/

variable {V E : Type*}

/-- The simple graph on `V` recording which pairs of nodes are joined by at least one edge of
`F`. Adjacency, walks, paths and reachability "in `F`" are those of `edgeGraph ends F`. -/
def edgeGraph (ends : E → Sym2 V) (F : Finset E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (ends '' (F : Set E))

end NagamochiIbaraki.NodeConn


