-- Prove2me | Definitions.Def_NicerEars_TJoin_Setting
-- name    : NicerEars_TJoin_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:26:47.419721+00:00
-- url     : https://prove2.me/theorems/cb8fe0ac-639a-4a1f-b9c2-773090d7e97e
-- title:
--   pp. 2, 5 — multigraphs, 2G, T-joins, connected-T-joins, cuts, LP(G,T), 2-edge- and 2-vertex-connectivity
-- statement:
--   All graphs are finite and undirected; they may have **parallel edges but no loops** (Sebő–Vygen, p. 2). A graph $G$ is given by a finite vertex set $V(G)$, a finite edge set $E(G)$ and, for every edge, its unordered pair of distinct endpoints.
--
--   1. $2G$ is the graph obtained from $G$ by doubling every edge; a **multi-subgraph** of $G$ is a subgraph of $2G$, i.e. a choice of each edge of $G$ zero, one or two times.
--   2. For $T\subseteq V(G)$, a **$T$-join** in $G$ is a set $F\subseteq E(G)$ such that $T=\{v\in V(G): |\delta(v)\cap F| \text{ is odd}\}$.
--   3. (Definition 1) A **connected-$T$-join** of $G$ is a $T$-join $F$ in $2G$ such that $(V(G),F)$ is connected. For $T=\emptyset$ it is called a **tour**.
--   4. For $W\subseteq V(G)$, $\delta(W)$ is the set of edges with exactly one endpoint in $W$; for a partition $\mathcal W$ of $V(G)$, $\delta(\mathcal W)$ is the set of edges whose endpoints lie in different classes of $\mathcal W$; $x(S):=\sum_{e\in S}x_e$.
--   5. (p. 5) A vector $x\in\mathbb R^{E(G)}$ is **feasible for $\mathrm{LP}(G)$** if $x\ge 0$ and $x(\delta(W))\ge 2$ for all $\emptyset\ne W\subsetneq V(G)$. It is **feasible for $\mathrm{LP}(G,T)$** if $x\ge0$, $x(\delta(W))\ge 2$ for all $\emptyset\ne W\subsetneq V(G)$ with $|W\cap T|$ even, and
--   $$x(\delta(\mathcal W))\ \ge\ |\mathcal W|-1\qquad\text{for every partition }\mathcal W\text{ of }V(G).$$
--   The values $\mathrm{LP}(G)$ and $\mathrm{LP}(G,T)$ are the minima of $x(E(G))$ over these sets.
--   6. $F$ spans a **2-edge-connected** subgraph if $(V(G),F)$ is connected and remains connected after deleting any single edge of $F$; $G$ is 2-edge-connected if $E(G)$ does. $G$ is **2-vertex-connected** if it is 2-edge-connected and deleting any one vertex leaves the rest connected.
--   7. For $V'\subseteq V(G)$ and $E'\subseteq E(G)$ with every edge of $E'$ inside $V'$, $(V',E')$ is the corresponding sub-multigraph.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note.** A graph is a structure `Graph V E` with `ends : E → Sym2 V` and no diagonal pair. $2G$ has edge type `E × Fin 2`, so a multi-subgraph is a `Finset (E × Fin 2)`: each edge at most twice. Connectivity of $(V(G),F)$ is that of the simple graph of pairs joined by at least one edge of $F$; 2-edge-connectivity deletes single *edges* of $F$, so parallel edges count. The LP relaxations are given as feasibility predicates, not as minimum values. "2-vertex-connected" includes the one-vertex graph and two vertices joined by at least two parallel edges, and excludes a single edge; this is the reading under which the paper's ear-decomposition lemmas apply. The sub-multigraph lives on the subtypes of $V'$ and $E'$.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 2 (graphs, 2G, T-joins, Definition 1) and p. 5 (LP(G), δ(𝒲), LP(G,T))

import Mathlib

namespace NicerEars.TJoin

open Finset

/-- Sebő–Vygen, p. 2: a finite graph; parallel edges are allowed, loops are not. The vertex set is
the type `V`, the edge set the type `E`, and `ends e` is the unordered pair of endpoints of `e`. -/
structure Graph (V E : Type) where
  ends : E → Sym2 V
  loopless : ∀ e, ¬ (ends e).IsDiag

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- 2G: every edge doubled (p. 2). A multi-subgraph of G is a `Finset (E × Fin 2)`: the two copies
of an edge `e` are `(e, 0)` and `(e, 1)`. -/
def Graph.double (G : Graph V E) : Graph V (E × Fin 2) where
  ends p := G.ends p.1
  loopless p := G.loopless p.1

/-- The simple graph on `V` of pairs joined by at least one edge of `F` (multiplicity ignored).
`(V(G), F)` is connected iff this graph is. -/
def Graph.spanGraph {E' : Type} (G : Graph V E') (F : Finset E') : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (G.ends '' (F : Set E'))

/-- `G` is connected. -/
def Graph.IsConnected (G : Graph V E) : Prop := (G.spanGraph univ).Connected

/-- p. 2: `F ⊆ E(G)` is a T-join: `T` is exactly the set of vertices of odd degree in `F`. -/
def Graph.IsTJoin {E' : Type} [Fintype E'] [DecidableEq E'] (G : Graph V E') (T : Finset V)
    (F : Finset E') : Prop :=
  ∀ v, Odd #(F.filter (fun e => v ∈ G.ends e)) ↔ v ∈ T

/-- Definition 1 (p. 2): a connected-T-join of `G` is a T-join `F` in 2G such that `(V(G), F)` is
connected. -/
def Graph.IsConnectedTJoin (G : Graph V E) (T : Finset V) (F : Finset (E × Fin 2)) : Prop :=
  G.double.IsTJoin T F ∧ (G.double.spanGraph F).Connected

/-- Definition 1 (p. 2): a tour is a connected-∅-join. -/
def Graph.IsTour (G : Graph V E) (F : Finset (E × Fin 2)) : Prop := G.IsConnectedTJoin ∅ F

/-- δ(W): the edges with exactly one endpoint in `W` (p. 2). -/
def Graph.cut (G : Graph V E) (W : Finset V) : Finset E :=
  univ.filter (fun e => ∃ u ∈ W, ∃ v ∉ W, G.ends e = s(u, v))

/-- δ(𝒲) (p. 5): the edges whose endpoints lie in different classes of the partition `𝒲`. -/
def Graph.crossing (G : Graph V E) (P : Finpartition (univ : Finset V)) : Finset E :=
  univ.filter (fun e => ∃ u v, G.ends e = s(u, v) ∧ P.part u ≠ P.part v)

/-- p. 5: `x` is a feasible point of LP(G): `x ≥ 0` and `x(δ(W)) ≥ 2` for all `∅ ≠ W ⊊ V(G)`. -/
def Graph.LPFeasible (G : Graph V E) (x : E → ℝ) : Prop :=
  (∀ e, 0 ≤ x e) ∧ ∀ W : Finset V, W.Nonempty → W ≠ univ → 2 ≤ ∑ e ∈ G.cut W, x e

/-- p. 5: `x` is a feasible point of LP(G, T): `x ≥ 0`, `x(δ(W)) ≥ 2` for all `∅ ≠ W ⊊ V(G)` with
`|W ∩ T|` even, and `x(δ(𝒲)) ≥ |𝒲| − 1` for every partition `𝒲` of `V(G)`. -/
def Graph.LPTFeasible (G : Graph V E) (T : Finset V) (x : E → ℝ) : Prop :=
  (∀ e, 0 ≤ x e) ∧
  (∀ W : Finset V, W.Nonempty → W ≠ univ → Even #(W ∩ T) → 2 ≤ ∑ e ∈ G.cut W, x e) ∧
  ∀ P : Finpartition (univ : Finset V), (#P.parts : ℝ) - 1 ≤ ∑ e ∈ G.crossing P, x e

/-- `F ⊆ E(G)` spans a 2-edge-connected subgraph: `(V(G), F)` is connected and stays connected
after deleting any single edge of `F` (a parallel copy keeps the adjacency). -/
def Graph.IsTwoECSpanning {E' : Type} [DecidableEq E'] (G : Graph V E') (F : Finset E') : Prop :=
  (G.spanGraph F).Connected ∧ ∀ e ∈ F, (G.spanGraph (F.erase e)).Connected

/-- `G` is 2-edge-connected. -/
def Graph.IsTwoEdgeConnected (G : Graph V E) : Prop := G.IsTwoECSpanning univ

/-- "2-vertex-connected" as the paper uses it (Proposition 4, Lemmas 10, 23): 2-edge-connected and
no vertex whose deletion disconnects the rest. This includes the one-vertex graph and two vertices
joined by parallel edges, and excludes a single edge (a bridge). -/
def Graph.IsTwoVertexConnected (G : Graph V E) : Prop :=
  G.IsTwoEdgeConnected ∧ ∀ v, ((G.spanGraph univ).induce {w | w ≠ v}).Preconnected

omit [Fintype V] [DecidableEq V] in
/-- Every unordered pair with both entries in `V'` is the image of a pair of elements of `V'`. -/
theorem exists_sym2_lift (V' : Finset V) (s : Sym2 V) (h : ∀ v ∈ s, v ∈ V') :
    ∃ s' : Sym2 V', s'.map Subtype.val = s := by
  induction s using Sym2.ind with
  | h a b => exact ⟨s(⟨a, h a (Sym2.mem_mk_left a b)⟩, ⟨b, h b (Sym2.mem_mk_right a b)⟩), rfl⟩

/-- The sub-multigraph of `G` with vertex set `V'` and edge set `E'`, where every edge of `E'` has
both ends in `V'` (used for the blocks `G₁`, `G₂` of Proposition 4). -/
noncomputable def Graph.sub (G : Graph V E) (V' : Finset V) (E' : Finset E)
    (h : ∀ e ∈ E', ∀ v ∈ G.ends e, v ∈ V') : Graph V' E' where
  ends e := Classical.choose (exists_sym2_lift V' (G.ends e.1) (h e.1 e.2))
  loopless e hd := G.loopless e.1 (by
    rw [← Classical.choose_spec (exists_sym2_lift V' (G.ends e.1) (h e.1 e.2))]
    exact Sym2.IsDiag.map hd)

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
/-- The ends of an edge of `G.sub V' E' h` are its ends in `G`. -/
theorem Graph.sub_ends_map (G : Graph V E) (V' : Finset V) (E' : Finset E)
    (h : ∀ e ∈ E', ∀ v ∈ G.ends e, v ∈ V') (e : E') :
    ((G.sub V' E' h).ends e).map Subtype.val = G.ends e.1 :=
  Classical.choose_spec (exists_sym2_lift V' (G.ends e.1) (h e.1 e.2))

end NicerEars.TJoin


