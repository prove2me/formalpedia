-- Prove2me | Definitions.Def_NodeStableProj_Main_Graph
-- name    : NodeStableProj_Main_Graph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:57:04.435918+00:00
-- url     : https://prove2.me/theorems/cdbacc00-5711-4a7f-b2a7-49cf1a963a6b
-- title:
--   Labelled finite simple graphs, vertex deletion, node-neighbours, degrees, D-bounded and maximal bounded subgraphs, edge preservation
-- statement:
--   A **graph** $G=(V,E)$ is a finite set $V\subset\mathbb N$ of vertex labels and a finite set $E$ of unordered pairs $\{u,v\}$ with $u\ne v$ and $u,v\in V$. Labels are identities, so two graphs are equal exactly when their vertex sets and edge sets are equal. The degree $\deg_G(u)$ is the number of edges containing $u$. For a real $D$, $G$ is **$D$-bounded** ($G\in\mathcal G_D$) if $\deg_G(u)\le D$ for every $u\in V$. $H$ is a **spanning subgraph** of $G$ if $V(H)=V(G)$ and $E(H)\subseteq E(G)$; $G$ restricted to an edge set $F$ is the graph $(V(G),F\cap E(G))$.
--
--   $H$ is a **maximal $\hat D$-bounded subgraph** of $G$ if it is a $\hat D$-bounded spanning subgraph of $G$ and every edge $\{u,v\}\in E(G)\setminus E(H)$ has an endpoint $x$ with $\deg_H(x)+1>\hat D$ (adding it would exceed $\hat D$). $H$ is **edge-preserving for $D$** (Equation (1) of Lemma 3.3) if every $\{u,v\}\in E(G)\setminus E(H)$ has an endpoint $x$ with
--   $$\deg_H(x)\ \ge\ D .$$
--
--   $G_{-v}$ deletes $v$ and all its incident edges. $G'$ is obtained from $G$ by **adding a node** $v^*$ if $v^*\notin V(G)$, $V(G')=V(G)\cup\{v^*\}$ and $G'_{-v^*}=G$ (the edges at $v^*$ are arbitrary). $G,G'$ are **node-neighbours** (Definition 2.1) if one is obtained from the other by removing a vertex and its incident edges. $G,G'$ are **fixed-vertex node-neighbours** with differing node $v^*$ (Definition 2.3) if $V(G)=V(G')\ni v^*$, $G_{-v^*}=G'_{-v^*}$ and $v^*$ is isolated in one of them. $G$ is an **$n$-node graph** if $|V|=n$.
--
--   **Formalization Note.** `Graph` is a structure with fields `V : Finset ℕ`, `E : Finset (Sym2 ℕ)` and the two axioms; it carries the discrete σ-algebra `⊤`, so every set of graphs is an event. The edge attribute $x$ of the paper is omitted ($x\equiv1$), as in §3.
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 2 fn. 1; p. 9 §2, Definitions 2.1 and 2.3, Observation 2.2; p. 11 Equation (1)

import Mathlib

open MeasureTheory

namespace NodeStableProj.Main

/-!
# Labelled finite simple graphs, vertex deletion, node-neighbours and degree bounds

Aden-Ali, Sealfon, Smith, Steinke, Ullman, *Node Differential Privacy via Node-Stable Graph
Projections*, STOC 2027 submission (manuscript sha256 42f18565…), p. 2 fn. 1, p. 9 §2,
Definitions 2.1 and 2.3, Observation 2.2.

* A graph is a finite set `V` of vertex labels in `ℕ` and a finite set `E` of unordered pairs
  `s(u, v)` with `u ≠ v` and `u, v ∈ V`. Vertex labels are identities (footnote 4), so two
  graphs are equal iff they have the same vertex set and the same edge set. The edge attribute
  `x` of the paper is omitted (`x ≡ 1`), as in §3.
* `Graph` carries the discrete σ-algebra `⊤`: every set of graphs is an event.
-/

/-- A labelled finite simple graph: vertex labels in `ℕ`, edges unordered pairs of distinct
vertices of `V`. -/
@[ext]
structure Graph where
  /-- The vertex set. -/
  V : Finset ℕ
  /-- The edge set. -/
  E : Finset (Sym2 ℕ)
  /-- Edges are not loops. -/
  loopless : ∀ e ∈ E, ¬ e.IsDiag
  /-- Both endpoints of an edge are vertices. -/
  edge_subset : ∀ e ∈ E, ∀ x ∈ e, x ∈ V

instance : MeasurableSpace Graph := ⊤

/-- `deg_G(u)`: the number of edges of `G` containing `u`. -/
def Graph.deg (G : Graph) (u : ℕ) : ℕ := (G.E.filter (fun e => u ∈ e)).card

/-- `G` is `D`-bounded (`G ∈ G_D`, maximum degree at most `D`), for a real bound `D`. -/
def Graph.Bounded (D : ℝ) (G : Graph) : Prop := ∀ u ∈ G.V, (G.deg u : ℝ) ≤ D

/-- `H` is a subgraph of `G` with the same vertex set. -/
def Graph.SpanningSubgraph (H G : Graph) : Prop := H.V = G.V ∧ H.E ⊆ G.E

/-- `H` is a maximal `D̂`-bounded subgraph of `G`: a `D̂`-bounded spanning subgraph of `G` to
which no further edge of `G` can be added without exceeding degree `D̂` at an endpoint. -/
def Graph.IsMaximalBoundedSubgraph (Dhat : ℝ) (G H : Graph) : Prop :=
  H.SpanningSubgraph G ∧ H.Bounded Dhat ∧
    ∀ e ∈ G.E, e ∉ H.E → ∃ x ∈ e, Dhat < (H.deg x : ℝ) + 1

/-- Edge preservation, Equation (1) of Lemma 3.3: every edge of `G` omitted from `H` has an
endpoint of `H`-degree at least `D`. -/
def Graph.EdgePreserving (D : ℝ) (G H : Graph) : Prop :=
  ∀ e ∈ G.E, e ∉ H.E → ∃ x ∈ e, D ≤ (H.deg x : ℝ)

/-- `G_{−v}`: delete the vertex `v` and every edge incident to it. -/
def Graph.deleteVertex (G : Graph) (v : ℕ) : Graph where
  V := G.V.erase v
  E := G.E.filter (fun e => v ∉ e)
  loopless := fun e he => G.loopless e (Finset.mem_filter.1 he).1
  edge_subset := fun e he x hx => by
    obtain ⟨he, hv⟩ := Finset.mem_filter.1 he
    refine Finset.mem_erase.2 ⟨?_, G.edge_subset e he x hx⟩
    rintro rfl
    exact hv hx

/-- The edge set of `G_{−v}` computed from an edge set alone: the edges not incident to `v`. -/
def deleteVertexEdges (E : Finset (Sym2 ℕ)) (v : ℕ) : Finset (Sym2 ℕ) :=
  E.filter (fun e => v ∉ e)

/-- The spanning subgraph of `G` with edge set `F ∩ E(G)` (used to read an edge set as a graph on
`V(G)`). -/
def Graph.withEdges (G : Graph) (F : Finset (Sym2 ℕ)) : Graph where
  V := G.V
  E := F.filter (· ∈ G.E)
  loopless := fun e he => G.loopless e (Finset.mem_filter.1 he).2
  edge_subset := fun e he => G.edge_subset e (Finset.mem_filter.1 he).2

/-- `G'` is obtained from `G` by adding a new node `v* ∉ V(G)` together with arbitrary incident
edges (to vertices of `G`): `V(G') = V(G) ∪ {v*}`, `G'_{−v*} = G`. This is the ordered form of
the node-neighbour relation of Definition 2.1 (by Observation 2.2 every node-neighbouring pair is
of this form in one of its two orders). -/
def AddsNode (G G' : Graph) (vstar : ℕ) : Prop :=
  vstar ∉ G.V ∧ G'.V = insert vstar G.V ∧ G'.deleteVertex vstar = G

/-- Definition 2.1: `G, G'` are node-neighbours if one is obtained from the other by removing a
vertex and all its incident edges. -/
def NodeNeighbors (G G' : Graph) : Prop :=
  (∃ v ∈ G'.V, G'.deleteVertex v = G) ∨ (∃ v ∈ G.V, G.deleteVertex v = G')

/-- Definition 2.3: `G, G'` are fixed-vertex node-neighbours with differing node `v*`: same vertex
set, `v* ∈ V`, `G_{−v*} = G'_{−v*}`, and `v*` is isolated in one of them. -/
def FixedVertexNeighbors (G G' : Graph) (vstar : ℕ) : Prop :=
  G.V = G'.V ∧ vstar ∈ G.V ∧ G.deleteVertex vstar = G'.deleteVertex vstar ∧
    (G.deg vstar = 0 ∨ G'.deg vstar = 0)

/-- `G` is an `n`-node graph (`G ∈ G^n`): it has exactly `n` vertices. -/
def Graph.IsNNode (n : ℕ) (G : Graph) : Prop := G.V.card = n

end NodeStableProj.Main


