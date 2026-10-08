-- Prove2me | Definitions.Def_SnarkGen_Zhang_IsSnark
-- name    : SnarkGen_Zhang_IsSnark
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:12.319454+00:00
-- url     : https://prove2.me/theorems/347af929-a8f3-48f3-a1db-db50bc49b45f
-- title:
--   Snark: uncolourable, cyclically 4-edge connected, cubic, girth at least 5 (Section 2)
-- statement:
--   Let $G$ be a finite simple graph. The **girth** $g(G)$ of $G$ is the number of vertices in a shortest cycle of $G$. A **snark** is an uncolourable cyclically $4$-edge connected cubic graph with girth at least $5$. That is, $G$ is a snark when all four of the following hold:
--
--   1. $G$ is **cubic**: every vertex has degree $3$;
--   2. $G$ is **uncolourable**: it has no proper $3$-edge-colouring;
--   3. $G$ is **cyclically $4$-edge connected**: deleting fewer than $4$ edges never leaves two distinct components that both contain a cycle;
--   4. $$g(G) \ge 5.$$
--
--   Snarks are the smallest possible counterexamples to many conjectures about cubic graphs (the cycle double cover conjecture, Tutte's 5-flow conjecture, the Berge–Fulkerson conjecture). The conditions on girth and cyclic connectivity exclude graphs that reduce to smaller uncolourable graphs.
--
--   **Formalization Note** The girth is Mathlib's extended girth `SimpleGraph.egirth`, valued in $\mathbb N \cup \{\infty\}$, which is $\infty$ for an acyclic graph; condition 4 is `5 ≤ G.egirth`. Degrees are computed with classical decidability, so the predicate applies to every finite simple graph without extra instance arguments; any other decidability instance gives the same degrees.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 4, Section 2

import Mathlib
import Definitions.Def_SnarkGen_EdgeInsertion_Colourable
import Definitions.Def_SnarkGen_Zhang_CyclicallyEdgeConnected

namespace SnarkGen.Zhang

open Classical in
/-- A *snark* (p. 4): an uncolourable cyclically 4-edge connected cubic graph with girth at
least 5. Degrees are computed with classical decidability, so the predicate applies to every
finite simple graph. The girth is `SimpleGraph.egirth` (`⊤` for an acyclic graph). -/
def IsSnark {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  G.IsRegularOfDegree 3 ∧ ¬ SnarkGen.EdgeInsertion.Colourable G ∧ CyclicallyEdgeConnected G 4 ∧ 5 ≤ G.egirth

end SnarkGen.Zhang


