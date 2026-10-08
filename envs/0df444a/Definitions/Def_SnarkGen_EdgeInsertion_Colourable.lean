-- Prove2me | Definitions.Def_SnarkGen_EdgeInsertion_Colourable
-- name    : SnarkGen_EdgeInsertion_Colourable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:05:22.13742+00:00
-- url     : https://prove2.me/theorems/8cfa5c56-5818-43bc-976a-5a32be709ceb
-- title:
--   Colourable graph: chromatic index at most 3 (p. 2)
-- statement:
--   Let $G = (V,E)$ be a simple graph. A **3-colouring** of $G$ (in the sense of the paper: an edge colouring) is a map $C : E \to \{0,1,2\}$ such that any two distinct edges sharing an end-vertex receive different colours. Following Isaacs, the graph $G$ is called **colourable** if it admits a 3-colouring, that is,
--   $$\chi'(G) \le 3,$$
--   where $\chi'(G)$ is the chromatic index of $G$. A cubic graph that is not colourable is called **uncolourable**; for a cubic graph with at least one vertex, $\chi'(G) \in \{3,4\}$ by Vizing's theorem, so colourable means chromatic index exactly $3$.
--
--   Colourability is the central property of the paper: snarks are uncolourable by definition (p. 4), the edge insertion operation of §3.1 is shown to produce colourable graphs (Lemma 3.2, Theorem 3.3), and the cycle-cover bound of §7 is stated for colourable cubic graphs.
--
--   **Formalization Note** A proper edge colouring of $G$ is a proper vertex colouring of the line graph $L(G)$, so `Colourable G` is `G.lineGraph.Colorable 3`. It is *not* `G.Colorable 3`, which would be a vertex colouring. Cubicity is not part of the definition; every statement that uses it assumes `G.IsRegularOfDegree 3` separately.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 2 (Isaacs' terminology) and p. 5, §3.1

import Mathlib

namespace SnarkGen.EdgeInsertion

/-- Brinkmann–Goedgebeur–Hägglund–Markström, arXiv:1206.6690v3, p. 2: a graph is *colourable*
when its chromatic index is at most 3, i.e. it has a proper 3-edge-colouring. A proper
edge-colouring of `G` is a proper vertex colouring of its line graph; a *3-colouring* of `G`
(§3.1) is an element of `G.lineGraph.Coloring (Fin 3)`. -/
def Colourable {V : Type*} (G : SimpleGraph V) : Prop :=
  G.lineGraph.Colorable 3

end SnarkGen.EdgeInsertion


