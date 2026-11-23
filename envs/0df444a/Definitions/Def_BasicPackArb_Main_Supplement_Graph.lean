-- Prove2me | Definitions.Def_BasicPackArb_Main_Supplement_Graph
-- name    : BasicPackArb_Main_Supplement_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:54:41.656809+00:00
-- url     : https://prove2.me/theorems/e0346854-4f76-4caa-809d-5a864ead6510
-- title:
--   Edge-identity multigraphs, rooted trees, orientations and nonempty-block partitions
-- statement:
--   An undirected graph has vertices $V$, a finite set $E$ of edge identities and an endpoint pair for each edge. Parallel edges remain distinct and loops are allowed. A rooted tree is a connected acyclic subgraph with a designated vertex $r$; the single vertex $r$ with no edge is permitted. Acyclicity uses the referenced edge-deletion predicate: after any selected edge is removed, its endpoints cannot be joined by a walk of the remaining selected edges.
--
--   An orientation chooses one direction for each edge, yielding the published digraph type. For $X\subseteq V$, $E(X)$ contains edges with both endpoints in $X$; $V(F)$ contains exactly the vertices incident to $F$. A partition $\mathcal P$ covers $V$ by pairwise disjoint nonempty blocks, and
--
--   $$e_G(\mathcal P)=|\{e\in E:\text{the endpoints of }e\text{ lie in different blocks}\}|.$$
--
--   These objects retain edge identities throughout orientation and tree packing. Endpoint order is a presentation choice, not a direction. The empty partition is permitted when $V$ is empty.
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, pp. 1–3, §1

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph
import Definitions.Def_InducedExpanderTest989_Structural_Supplement_NoisyLabels

set_option autoImplicit false

namespace BasicPackArb.Main.Supplement

/-- Edge identities preserve loops and parallel copies. Endpoint order is only a presentation. -/
structure Graph (V E : Type) where
  ends : E → V × V
  edges : Finset E

/-- All directions of the actual edges, with the same identities as the undirected graph. -/
def Graph.orient {V E : Type} (G : Graph V E) (σ : E → Bool) : Digraph V E :=
  ⟨fun e => if σ e then (G.ends e).1 else (G.ends e).2,
   fun e => if σ e then (G.ends e).2 else (G.ends e).1, G.edges⟩

/-- A tree subgraph rooted at a vertex, including the one-vertex tree.
Acyclicity uses the published multigraph predicate: deleting any selected edge disconnects
its endpoints, so loops and parallel 2-cycles are excluded. -/
structure RootedTree {V E : Type} [DecidableEq E] (G : Graph V E) where
  verts : Finset V
  edges : Finset E
  root : V
  edges_subset : edges ⊆ G.edges
  ends_mem : ∀ e ∈ edges, (G.ends e).1 ∈ verts ∧ (G.ends e).2 ∈ verts
  root_mem : root ∈ verts
  connected : ∀ v ∈ verts, Relation.ReflTransGen
    (InducedExpanderTest989.Structural.Supplement.edgeAdj G.ends edges) root v
  acyclic : InducedExpanderTest989.Structural.Supplement.IsAcyclicEdgeSet G.ends edges

noncomputable def Graph.inducedEdges {V E : Type} (G : Graph V E) (X : Finset V) : Finset E := by
  classical
  exact G.edges.filter (fun e => (G.ends e).1 ∈ X ∧ (G.ends e).2 ∈ X)

/-- Vertices incident with F, not all ambient vertices. -/
noncomputable def Graph.incident {V E : Type} (G : Graph V E) (F : Finset E) : Finset V := by
  classical
  exact F.biUnion (fun e => {(G.ends e).1, (G.ends e).2})

/-- Partitions include the empty partition of the empty carrier, never empty blocks. -/
def IsPartition {V : Type} [Fintype V] (P : Finset (Finset V)) : Prop :=
  (∀ X ∈ P, X.Nonempty) ∧
  (∀ X ∈ P, ∀ Y ∈ P, X ≠ Y → Disjoint X Y) ∧
  ∀ v : V, ∃ X ∈ P, v ∈ X

noncomputable def Graph.crossing {V E : Type} (G : Graph V E)
    (P : Finset (Finset V)) : ℕ := by
  classical
  exact (G.edges.filter (fun e => ¬ ∃ X ∈ P, (G.ends e).1 ∈ X ∧ (G.ends e).2 ∈ X)).card

end BasicPackArb.Main.Supplement


