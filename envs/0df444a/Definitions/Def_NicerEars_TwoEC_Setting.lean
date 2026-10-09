-- Prove2me | Definitions.Def_NicerEars_TwoEC_Setting
-- name    : NicerEars_TwoEC_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:12.227567+00:00
-- url     : https://prove2.me/theorems/1f7b77cf-c787-44c5-90d1-8d1ec72da549
-- title:
--   pp. 2, 5 — multigraphs, 2G, T-joins, connected-T-joins and tours, cuts, LP(G) and LP(G,T), 2-edge-connected spanning subgraphs, OPT, OPT_2EC, τ
-- statement:
--   This file fixes the graph-theoretic setting of Sebő and Vygen's paper.
--
--   1. **Graphs.** A graph $G$ has a finite vertex set $V(G)$ and a finite edge set $E(G)$; every edge $e$ has an unordered pair of distinct ends. Parallel edges are allowed, loops are not. $2G$ is the graph obtained from $G$ by doubling every edge, and a **multi-subgraph** of $G$ is an edge set of $2G$.
--   2. **T-joins.** For $T\subseteq V(G)$, a $T$-join is an edge set $F$ such that $T$ is exactly the set of vertices meeting an odd number of edges of $F$. $\tau(G,T)$ is the minimum size of a $T$-join $F\subseteq E(G)$.
--   3. **Connected-T-joins and tours** (Definition 1). A connected-$T$-join of $G$ is a $T$-join $F$ in $2G$ such that $(V(G),F)$ is connected; a tour is a connected-$\emptyset$-join. $\mathrm{OPT}(G,T)$ is the minimum size of a connected-$T$-join and $\mathrm{OPT}(G)=\mathrm{OPT}(G,\emptyset)$.
--   4. **2-edge-connectivity.** An edge set $F$ spans a 2-edge-connected subgraph if $(V(G),F)$ is connected and remains connected after deleting any single edge of $F$. $G$ is 2-edge-connected if $E(G)$ has this property. A **2ECSS** of $G$ is such an $F\subseteq E(G)$. $\mathrm{OPT}_{2EC}(G)$ is the minimum size of a 2-edge-connected spanning multi-subgraph of $G$.
--   5. **2-vertex-connectivity.** $G$ is 2-vertex-connected if it is 2-edge-connected and deleting any one vertex leaves the remaining vertices connected.
--   6. **LP relaxations** (p. 5). With $\delta(W)$ the set of edges with exactly one end in $W$, $\delta(\mathcal W)$ the set of edges joining different classes of a partition $\mathcal W$, and $x(S)=\sum_{e\in S}x_e$:
--   $$\mathrm{LP}(G)=\min\{x(E(G)) : x\ge 0,\ x(\delta(W))\ge 2\ \text{for all}\ \emptyset\ne W\subsetneq V(G)\},$$
--   and $\mathrm{LP}(G,T)$ keeps the cut constraints only for $W$ with $|W\cap T|$ even and adds $x(\delta(\mathcal W))\ge|\mathcal W|-1$ for every partition $\mathcal W$ of $V(G)$.
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** Edges carry their ends as `Sym2 V`, so parallel edges are distinct edges with the same ends; $2G$ has edge type $E\times\{0,1\}$. Connectivity of $(V(G),F)$ is that of the simple graph of pairs joined by at least one edge of $F$; 2-edge-connectivity deletes one *edge* of $F$ at a time, so two parallel edges are 2-edge-connected and a single edge is not. The optimum values $\mathrm{OPT}$, $\mathrm{OPT}_{2EC}$, $\tau$ are infima of sets of natural numbers and $\mathrm{LP}(G)$, $\mathrm{LP}(G,T)$ infima of real sets; for connected $G$ (and $|T|$ even) these sets are nonempty and bounded below, so the infima are the paper's minima. The convention for "2-vertex-connected" includes the one-vertex graph and two vertices joined by parallel edges, and excludes a single edge.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, pp. 2–3 (Notation, Definition 1, the 2ECSS problem) and p. 5 (LP(G), LP(G,T))

import Mathlib

namespace NicerEars.TwoEC

open Finset

/-- p. 2: a finite graph; parallel edges allowed, loops not. -/
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

/-- δ(𝒲): edges whose endpoints lie in different classes of the partition 𝒲 (p. 5). -/
def Graph.crossing (G : Graph V E) (P : Finpartition (univ : Finset V)) : Finset E :=
  univ.filter (fun e => ∃ u v, G.ends e = s(u, v) ∧ P.part u ≠ P.part v)

/-- p. 5: x is feasible for LP(G). -/
def Graph.LPFeasible (G : Graph V E) (x : E → ℝ) : Prop :=
  (∀ e, 0 ≤ x e) ∧ ∀ W : Finset V, W.Nonempty → W ≠ univ → 2 ≤ ∑ e ∈ G.cut W, x e

/-- p. 5: x is feasible for LP(G, T). -/
def Graph.LPTFeasible (G : Graph V E) (T : Finset V) (x : E → ℝ) : Prop :=
  (∀ e, 0 ≤ x e) ∧
  (∀ W : Finset V, W.Nonempty → W ≠ univ → Even #(W ∩ T) → 2 ≤ ∑ e ∈ G.cut W, x e) ∧
  ∀ P : Finpartition (univ : Finset V), (#P.parts : ℝ) - 1 ≤ ∑ e ∈ G.crossing P, x e

/-- p. 5: the optimum value LP(G) = min{x(E(G)) : x feasible for LP(G)}. The feasible set is
nonempty for connected G (x ≡ 2) and the objective is bounded below by 0, so this infimum is the
LP minimum. -/
noncomputable def Graph.lpValue (G : Graph V E) : ℝ :=
  sInf ((fun x : E → ℝ => ∑ e, x e) '' {x | G.LPFeasible x})

/-- p. 5: the optimum value LP(G, T). -/
noncomputable def Graph.lpTValue (G : Graph V E) (T : Finset V) : ℝ :=
  sInf ((fun x : E → ℝ => ∑ e, x e) '' {x | G.LPTFeasible T x})

/-- p. 2: F ⊆ E(G) spans a 2-edge-connected subgraph: connected, and still connected after deleting
any single edge of F (a parallel copy keeps the adjacency, as it should). -/
def Graph.IsTwoECSpanning {E' : Type} [DecidableEq E'] (G : Graph V E') (F : Finset E') : Prop :=
  (G.spanGraph F).Connected ∧ ∀ e ∈ F, (G.spanGraph (F.erase e)).Connected

def Graph.IsTwoEdgeConnected (G : Graph V E) : Prop := G.IsTwoECSpanning univ

/-- "2-vertex-connected" as the paper uses it (Prop. 4, Lemma 23): 2-edge-connected and no
vertex whose deletion disconnects the rest. Disclosed convention: includes the one-vertex graph and
two vertices joined by parallel edges; excludes a single bridge, which has no ear-decomposition. -/
def Graph.IsTwoVertexConnected (G : Graph V E) : Prop :=
  G.IsTwoEdgeConnected ∧ ∀ v, ((G.spanGraph univ).induce {w | w ≠ v}).Preconnected

/-- Definition 1: OPT(G, T), the minimum cardinality of a connected-T-join of G. -/
noncomputable def Graph.OPT (G : Graph V E) (T : Finset V) : ℕ :=
  sInf {n | ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin T F ∧ #F = n}

/-- Definition 1: OPT(G) = OPT(G, ∅), the minimum cardinality of a tour. -/
noncomputable def Graph.OPTTour (G : Graph V E) : ℕ := G.OPT ∅

/-- p. 2: OPT_2EC(G), the minimum number of edges of a 2-edge-connected spanning
multi-subgraph of G (a subgraph of 2G). -/
noncomputable def Graph.OPT2EC (G : Graph V E) : ℕ :=
  sInf {n | ∃ F : Finset (E × Fin 2), G.double.IsTwoECSpanning F ∧ #F = n}

/-- p. 2: τ(G, T), the minimum cardinality of a T-join F ⊆ E(G). -/
noncomputable def Graph.tau (G : Graph V E) (T : Finset V) : ℕ :=
  sInf {n | ∃ F : Finset E, G.IsTJoin T F ∧ #F = n}

end NicerEars.TwoEC


