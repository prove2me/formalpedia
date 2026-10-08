-- Prove2me | Definitions.Def_SnarkGen_EdgeInsertion_twoColourFactor
-- name    : SnarkGen_EdgeInsertion_twoColourFactor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:05:20.600501+00:00
-- url     : https://prove2.me/theorems/5c4b2cdd-06f5-45fc-8538-9e04421cc8a9
-- title:
--   The 2-factor induced by two colours of a 3-colouring (§3.1, p. 5)
-- statement:
--   Let $G = (V,E)$ be a simple graph, let $C : E \to \{0,1,2\}$ be a 3-colouring (proper edge colouring) of $G$, and let $i, j$ be two colours. The **subgraph induced by the colours $i$ and $j$** is the spanning subgraph
--   $$G_{ij} = \bigl(V,\ \{\, e \in E : C(e) = i \text{ or } C(e) = j \,\}\bigr)$$
--   of $G$, consisting of all vertices of $G$ and exactly the edges coloured $i$ or $j$.
--
--   When $G$ is cubic and $i \ne j$, every vertex meets exactly one edge of each colour, so $G_{ij}$ is a 2-factor whose cycles alternate between the two colours (the paper's "2-factor induced by two different colours"). Theorem 3.3 asks whether two edges lie on the same cycle of $G_{ij}$.
--
--   **Formalization Note** The colouring is `C : G.lineGraph.Coloring (Fin 3)`, a proper vertex colouring of the line graph with colours `Fin 3 = {0,1,2}`. The subgraph is `SimpleGraph.fromEdgeSet` of the set of edges of `G` coloured `i` or `j`; it is defined for any `i, j`, and the statements that use it assume `i ≠ j`.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 5, §3.1 (sentence before Theorem 3.3 and Theorem 3.3)

import Mathlib

namespace SnarkGen.EdgeInsertion

variable {V : Type*}

/-- The **subgraph induced by two colours** (arXiv:1206.6690v3, p. 5, §3.1): given a
3-edge-colouring `C` of `G` (a proper colouring of the line graph of `G` with colours `Fin 3`)
and two colours `i`, `j`, the spanning subgraph of `G` on all vertices of `G` whose edges are
exactly the edges of `G` coloured `i` or `j`. -/
def twoColourFactor {G : SimpleGraph V} (C : G.lineGraph.Coloring (Fin 3)) (i j : Fin 3) :
    SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ G.edgeSet, C ⟨e, h⟩ = i ∨ C ⟨e, h⟩ = j}

end SnarkGen.EdgeInsertion


