-- Prove2me | Definitions.Def_TwoConnSS_IsTwoECSS
-- name    : TwoConnSS_IsTwoECSS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:44:01.758568+00:00
-- url     : https://prove2.me/theorems/741801e9-4e60-497d-9e78-dc0073aa302d
-- title:
--   2-edge-connected graphs and feasible 2ECSS solutions
-- statement:
--   For an edge set $S$ on $V$ write $(V, S)$ for the spanning subgraph it defines. A graph is **2-edge-connected (2EC)** if it is connected and has no bridge, where a bridge is an edge whose deletion increases the number of connected components.
--
--   A **2ECSS** of $G$ (a feasible solution of 2ECSS) is an edge set $F \subseteq E(G)$ such that $(V, F)$ is 2EC. The problem asks for one with the fewest edges; $\mathrm{opt}_E(G)$ denotes that minimum.
--
--   **Formalization Note** The graph on one vertex is 2EC and the graph on no vertex is not. The optimum is never written as an infimum: statements compare with every feasible $F'$.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §5, p.18; §6, pp.23–24

import Mathlib

namespace TwoConnSS

/-- The spanning subgraph `(V, S)` of an edge set `S`. Jabal Ameli (STOC 2027 submission,
manuscript sha256 22d0f2a8…), §6, p.23: "We identify an edge set S ⊆ E(G) with the spanning
subgraph (V(G), S), not with an induced subgraph." Diagonal elements of `S` are dropped. -/
def sg {V : Type*} (S : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (S : Set (Sym2 V))

/-- **2-edge-connected graph.** §6, p.23: "A graph is 2-edge-connected (2EC) if it is connected
and has no bridge." A bridge (p.24) is an edge whose deletion increases the number of connected
components; Mathlib's `IsBridge` says the two ends of the edge are no longer joined, which is the
same for an edge of the graph.

**Formalization Note.** Mathlib's `Connected` requires a nonempty vertex type, so the graph on no
vertex is not 2EC, and the graph on one vertex is 2EC (it is connected and has no edge). -/
def IsTwoEC {V : Type*} (H : SimpleGraph V) : Prop :=
  H.Connected ∧ ∀ e ∈ H.edgeSet, ¬ H.IsBridge e

/-- **A feasible solution of 2ECSS (a 2ECSS of `G`).**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §5, p.18: "The minimum
2-edge-connected spanning subgraph problem (2ECSS) asks for a spanning subgraph that remains
connected after any one edge is deleted"; §6, p.23.

`IsTwoECSS G F` says `F ⊆ E(G)` and the spanning subgraph `(V, F)` is 2EC.

**Formalization Note.** The optimum `opt_E(G)` is never written as an infimum: every statement
compares with "every `F'` with `IsTwoECSS G F'`". -/
def IsTwoECSS {V : Type*} (G : SimpleGraph V) (F : Finset (Sym2 V)) : Prop :=
  (F : Set (Sym2 V)) ⊆ G.edgeSet ∧ IsTwoEC (sg F)

end TwoConnSS


