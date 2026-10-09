-- Prove2me | Definitions.Def_NicerEars_TSP_Setting
-- name    : NicerEars_TSP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:00.703713+00:00
-- url     : https://prove2.me/theorems/6a7e3eef-1b90-4f25-a50b-599f2a0f85cc
-- title:
--   pp. 2, 5 — multigraphs, 2G, T-joins, connected-T-joins and tours, cuts, LP(G), 2-edge-connected spanning subgraphs, τ, OPT, OPT₂EC
-- statement:
--   This file fixes the graph-theoretic objects of §1 of Sebő and Vygen's paper.
--
--   1. **Graphs.** All graphs are finite and undirected; they may have parallel edges but no loops (p. 2). A graph $G$ has a vertex set $V(G)$ and an edge set $E(G)$, and each edge joins two distinct vertices.
--   2. **The doubled graph.** $2G$ is the graph obtained from $G$ by doubling every edge; a *multi-subgraph* of $G$ is a subgraph of $2G$, i.e. a set of edges in which each edge of $G$ occurs at most twice.
--   3. **Cuts and degrees.** For $W\subseteq V(G)$, $\delta(W)$ is the set of edges with exactly one endpoint in $W$; $\delta(v):=\delta(\{v\})$.
--   4. **T-joins.** For $T\subseteq V(G)$, a *$T$-join* is an edge set $F$ such that $T=\{v\in V(G): |\delta(v)\cap F| \text{ is odd}\}$. $\tau(G,T)$ is the minimum cardinality of a $T$-join $F\subseteq E(G)$.
--   5. **Connected-T-joins and tours (Definition 1).** A *connected-$T$-join* of $G$ is a $T$-join $F$ in $2G$ such that $(V(G),F)$ is connected; for $T=\emptyset$ it is a *tour*. $\mathrm{OPT}(G,T)$ is the minimum cardinality of a connected-$T$-join, and $\mathrm{OPT}(G)=\mathrm{OPT}(G,\emptyset)$ the minimum cardinality of a tour.
--   6. **Two-edge-connectivity.** An edge set $F$ spans a *2-edge-connected* subgraph if $(V(G),F)$ is connected and stays connected after deleting any single edge of $F$. $G$ is 2-edge-connected if $E(G)$ does. $\mathrm{OPT}_{2EC}(G)$ is the minimum number of edges of a 2-edge-connected spanning multi-subgraph of $G$.
--   7. **Two-vertex-connectivity.** $G$ is *2-vertex-connected* if it is 2-edge-connected and deleting any single vertex leaves a connected graph.
--   8. **The LP relaxation (p. 5).** A vector $x\in\mathbb R^{E(G)}$ is feasible for
--   $$\mathrm{LP}(G):=\min\Big\{x(E(G)) : x\in\mathbb R^{E(G)}_{\ge 0},\ x(\delta(W))\ge 2 \text{ for all } \emptyset\ne W\subsetneq V(G)\Big\},$$
--   where $x(S):=\sum_{e\in S}x_e$.
--
--   These are the objects in which the graphic TSP and its lower bounds are stated: a tour is exactly a closed walk in $2G$ visiting every vertex, and $\mathrm{LP}(G)$ is the lower bound against which the 7/5 guarantee is proved.
--
--   **Formalization Note.** A graph is a map from an edge type to unordered pairs of distinct vertices, so parallel edges are allowed. $2G$ has edge type $E\times\{0,1\}$, and a multi-subgraph is a finite set of such doubled edges. Connectivity of an edge set is connectivity of the simple graph of pairs joined by at least one of its edges. "2-vertex-connected" includes the one-vertex graph and two vertices joined by parallel edges and excludes a single edge (a bridge has no ear-decomposition); this is the reading the paper needs when it reduces to blocks. The minima $\tau$, $\mathrm{OPT}$, $\mathrm{OPT}_{2EC}$ are infima of sets of natural numbers; for a connected graph and $|T|$ even these sets are nonempty, and for an empty set the value would be $0$. $\mathrm{LP}(G)$ itself is not defined as a number: statements quantify over its feasible points.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 2 (Notation and Terminology, Definition 1, Problems), p. 5 (LP(G))

import Mathlib

namespace NicerEars.TSP

open Finset

/-- p. 2: a finite graph; parallel edges allowed, loops not. The edge `e` joins the two
vertices of `ends e`. -/
structure Graph (V E : Type) where
  ends : E → Sym2 V
  loopless : ∀ e, ¬ (ends e).IsDiag

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- 2G: every edge doubled (p. 2). A multi-subgraph of G is a `Finset (E × Fin 2)`. -/
def Graph.double (G : Graph V E) : Graph V (E × Fin 2) where
  ends p := G.ends p.1
  loopless p := G.loopless p.1

/-- The simple graph on V of pairs joined by at least one edge of `F` (multiplicity ignored).
`(V(G), F)` is connected iff this graph is. -/
def Graph.spanGraph {E' : Type} (G : Graph V E') (F : Finset E') : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (G.ends '' (F : Set E'))

/-- G is connected. -/
def Graph.IsConnected (G : Graph V E) : Prop := (G.spanGraph univ).Connected

/-- p. 2: `F` is a T-join: T is exactly the set of vertices of odd degree in `F`. -/
def Graph.IsTJoin {E' : Type} [Fintype E'] [DecidableEq E'] (G : Graph V E') (T : Finset V)
    (F : Finset E') : Prop :=
  ∀ v, Odd #(F.filter (fun e => v ∈ G.ends e)) ↔ v ∈ T

/-- Definition 1: a connected-T-join of G is a T-join F in 2G such that (V(G), F) is connected. -/
def Graph.IsConnectedTJoin (G : Graph V E) (T : Finset V) (F : Finset (E × Fin 2)) : Prop :=
  G.double.IsTJoin T F ∧ (G.double.spanGraph F).Connected

/-- Definition 1: a tour is a connected-∅-join. -/
def Graph.IsTour (G : Graph V E) (F : Finset (E × Fin 2)) : Prop := G.IsConnectedTJoin ∅ F

/-- δ(W): edges with exactly one endpoint in W. -/
def Graph.cut (G : Graph V E) (W : Finset V) : Finset E :=
  univ.filter (fun e => ∃ u ∈ W, ∃ v ∉ W, G.ends e = s(u, v))

/-- p. 5: x is feasible for LP(G): `x ≥ 0` and `x(δ(W)) ≥ 2` for all `∅ ≠ W ⊂ V(G)`. -/
def Graph.LPFeasible (G : Graph V E) (x : E → ℝ) : Prop :=
  (∀ e, 0 ≤ x e) ∧ ∀ W : Finset V, W.Nonempty → W ≠ univ → 2 ≤ ∑ e ∈ G.cut W, x e

/-- p. 2: F spans a 2-edge-connected subgraph: (V, F) is connected, and still connected after
deleting any single edge of F (a parallel copy keeps the adjacency, as it should). -/
def Graph.IsTwoECSpanning {E' : Type} [DecidableEq E'] (G : Graph V E') (F : Finset E') : Prop :=
  (G.spanGraph F).Connected ∧ ∀ e ∈ F, (G.spanGraph (F.erase e)).Connected

/-- G is 2-edge-connected. -/
def Graph.IsTwoEdgeConnected (G : Graph V E) : Prop := G.IsTwoECSpanning univ

/-- "2-vertex-connected" as the paper uses it (Prop. 4, Lemmas 10, 23, 28; Theorem 27):
2-edge-connected and no vertex whose deletion disconnects the rest. Disclosed convention: includes
the one-vertex graph and two vertices joined by parallel edges; excludes a single bridge. -/
def Graph.IsTwoVertexConnected (G : Graph V E) : Prop :=
  G.IsTwoEdgeConnected ∧ ∀ v, ((G.spanGraph univ).induce {w | w ≠ v}).Preconnected

/-- p. 2: τ(G, T), the minimum cardinality of a T-join `F ⊆ E(G)` (no doubling). -/
noncomputable def Graph.tau (G : Graph V E) (T : Finset V) : ℕ :=
  sInf {n | ∃ F : Finset E, G.IsTJoin T F ∧ #F = n}

/-- Definition 1: OPT(G, T), the minimum cardinality of a connected-T-join of G. -/
noncomputable def Graph.OPTJoin (G : Graph V E) (T : Finset V) : ℕ :=
  sInf {n | ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin T F ∧ #F = n}

/-- Definition 1: OPT(G) = OPT(G, ∅), the minimum cardinality of a tour. -/
noncomputable def Graph.OPT (G : Graph V E) : ℕ := G.OPTJoin ∅

/-- p. 2: OPT_2EC(G), the minimum number of edges of a 2-edge-connected spanning
multi-subgraph of G (a subgraph of 2G). -/
noncomputable def Graph.OPT2EC (G : Graph V E) : ℕ :=
  sInf {n | ∃ F : Finset (E × Fin 2), G.double.IsTwoECSpanning F ∧ #F = n}

end NicerEars.TSP


