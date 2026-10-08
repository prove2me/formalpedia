-- Prove2me | Definitions.Def_SnarkGen_OddFactors_Snark
-- name    : SnarkGen_OddFactors_Snark
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:00.661082+00:00
-- url     : https://prove2.me/theorems/ca5661c8-5a73-46cd-98aa-1c5326785024
-- title:
--   Colourable graphs, cyclic k-edge connectivity and snarks (Section 2)
-- statement:
--   All graphs are finite and simple. Let $G$ be a graph on a finite vertex set $V$.
--
--   1. $G$ is **colourable** if its edges admit a proper 3-colouring, i.e. an assignment of one of three colours to each edge such that edges sharing an endpoint receive different colours; equivalently, the chromatic index $\chi'(G)$ is at most 3. Following Isaacs, a cubic graph with chromatic index 3 is called colourable and one with chromatic index 4 **uncolourable**.
--   2. A connected component of a graph **contains a cycle** if one of its vertices lies on a cycle of the graph.
--   3. For an integer $k$, $G$ is **cyclically $k$-edge connected** if the deletion of fewer than $k$ edges from $G$ does not create two components both of which contain at least one cycle: for every set $S \subseteq E(G)$ with $|S| < k$, the graph $G - S$ has at most one component containing a cycle.
--   4. A **snark** is an uncolourable cyclically 4-edge connected cubic graph with girth at least 5, where the **girth** $g(G)$ is the number of vertices in a shortest cycle of $G$:
--   $$G \text{ is a snark} \iff G \text{ is cubic},\ \ \chi'(G) > 3,\ \ G \text{ is cyclically 4-edge connected},\ \ g(G) \ge 5.$$
--
--   These are the definitions of Section 2 of the paper. Snarks are the smallest potential counterexamples to many conjectures on cubic graphs (cycle double cover, 5-flow), which is why the paper generates them and tests conjectures on them.
--
--   **Formalization Note** A proper 3-edge-colouring is a proper vertex 3-colouring of the line graph (`G.lineGraph.Colorable 3`), never the vertex colouring `G.Colorable 3`. In cyclic connectivity the deleted set `S` is a `Finset (Sym2 V)` contained in the edge set of `G`, and both the components and their cycles are taken in `G.deleteEdges S`; "two components" means two distinct components. The girth is Mathlib's extended girth `egirth : ℕ∞` (the length of a shortest cycle, which equals its number of vertices; `⊤` for a forest). Cubic is Mathlib's `IsRegularOfDegree 3`.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 4, Section 2 (girth, cyclically k-edge connected, snark); p. 2 (colourable/uncolourable, after Isaacs)

import Mathlib
import Definitions.Def_SnarkGen_EdgeInsertion_Colourable
import Definitions.Def_SnarkGen_Zhang_CyclicallyEdgeConnected

namespace SnarkGen.OddFactors

variable {V : Type*}

/-- A connected component `c` of a graph `H` **contains a cycle** if some vertex of `c` carries a
closed walk of `H` that is a cycle. -/
def ComponentHasCycle {H : SimpleGraph V} (c : H.ConnectedComponent) : Prop :=
  ∃ v ∈ c.supp, ∃ p : H.Walk v v, p.IsCycle

/-- A **snark** (arXiv:1206.6690v3, p. 4, §2) is an uncolourable cyclically 4-edge connected cubic
graph with girth at least 5. The girth is the extended girth `egirth : ℕ∞` (length of a shortest
cycle, `⊤` for an acyclic graph). -/
def IsSnark [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.IsRegularOfDegree 3 ∧ ¬ SnarkGen.EdgeInsertion.Colourable G ∧ SnarkGen.Zhang.CyclicallyEdgeConnected G 4 ∧ 5 ≤ G.egirth

end SnarkGen.OddFactors


