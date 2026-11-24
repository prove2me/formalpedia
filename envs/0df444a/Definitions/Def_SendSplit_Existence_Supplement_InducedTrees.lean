-- Prove2me | Definitions.Def_SendSplit_Existence_Supplement_InducedTrees
-- name    : SendSplit_Existence_Supplement_InducedTrees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:47:20.933113+00:00
-- url     : https://prove2.me/theorems/817f4570-988a-48da-ad2d-2e62e3ae2718
-- title:
--   Section 4 — minimal containing trees, undirected paths and endpoint-inclusive separation
-- statement:
--   A tree subgraph has explicit nonempty vertex and arc sets, is connected by undirected simple paths, and satisfies the published arc-sensitive forest predicate. It lies in the original graph, preserving arc identities. An induced tree for a flow $x$ is any inclusion-minimal tree containing its entire support forest, rather than only one component or the positive-flow arcs with no connecting edges.
--
--   For vertices $u,v$ of a tree $T$, a vertex $i$ separates them precisely when it lies on the unique simple undirected path $u:v$, including either endpoint. For a demand root $\sigma$ and a face set $D$, write
--   $$S(T,\sigma,i,D)=\{v\in D:i\in\sigma:v\}.$$
--   Set separation means separation of every cross pair of vertices. These are the combinatorial objects of both clauses of Theorem 3.
--
--   **Formalization Note** Paths ignore arc direction; the forest predicate still regards antiparallel arcs as a two-edge cycle. Connectivity is weak and requires a nonempty graph. Paths are finite injective vertex sequences with adjacent successive vertices, including a zero-length path. Existence of a witnessing path expresses path membership without using a default nonexistent path. Empty support has minimal singleton containing trees; a null flow has no nonzero-demand root.
-- source:
--   Erickson, Monma and Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Mathematics of Operations Research 12(4) (1987), DOI 10.1287/moor.12.4.634, p. 646, Section 4, induced tree and separation definitions; p. 638, support and forest conventions (PDF 14, 6)

import Mathlib
import Definitions.Def_SendSplit_Existence_Network

set_option autoImplicit false

namespace SendSplit.Existence.Supplement

variable {n : ℕ}

/-- Undirected incidence of an arc, ignoring its orientation only for paths. -/
def Adjacent (F : Finset (Fin n × Fin n)) (u v : Fin n) : Prop :=
  (u, v) ∈ F ∨ (v, u) ∈ F

/-- A simple undirected path, including the zero-length path at a vertex.
The ambient forest uses original arc identities; it does not merge antiparallel arcs. -/
structure SimplePath (F : Finset (Fin n × Fin n)) (u v : Fin n) where
  length : ℕ
  vertex : Fin (length + 1) → Fin n
  start : vertex 0 = u
  finish : vertex (Fin.last length) = v
  injective_vertex : Function.Injective vertex
  step : ∀ k : Fin length, Adjacent F (vertex k.castSucc) (vertex k.succ)

/-- Standard nonempty weak connectivity, not strong connectivity. -/
def IsConnected (G : ArcGraph n) : Prop :=
  0 < n ∧ ∀ u v, Nonempty (SimplePath G.A u v)

/-- A nonempty tree subgraph of G. Node sets are explicit so a null flow can
induce a singleton tree. The published arc-sensitive forest predicate is reused. -/
structure TreeSubgraph (G : ArcGraph n) where
  nodes : Finset (Fin n)
  edges : Finset (Fin n × Fin n)
  nonempty_nodes : nodes.Nonempty
  edges_subset : edges ⊆ G.A
  ends_mem : ∀ e ∈ edges, e.1 ∈ nodes ∧ e.2 ∈ nodes
  forest : IsForest edges
  connected : ∀ u ∈ nodes, ∀ v ∈ nodes, Nonempty (SimplePath edges u v)

/-- Inclusion-minimal tree containing the entire support forest, not merely one
component. For empty support the minimal trees are the singleton subgraphs. -/
def IsInducedTree {G : ArcGraph n} (x : Fin n → Fin n → ℝ)
    (T : TreeSubgraph G) : Prop :=
  support G x ⊆ T.edges ∧
  ∀ S : TreeSubgraph G, support G x ⊆ S.edges → S.nodes ⊆ T.nodes → S.edges ⊆ T.edges →
    S.nodes = T.nodes ∧ S.edges = T.edges

/-- Membership in the unique simple path of a tree, including both endpoints.
The existential path presentation avoids a default value for nonexistent paths. -/
def LiesOnPath {G : ArcGraph n} (T : TreeSubgraph G) (u v i : Fin n) : Prop :=
  ∃ p : SimplePath T.edges u v, ∃ k, p.vertex k = i

/-- The part of a face set separated from root σ by i. -/
noncomputable def separated {G : ArcGraph n} (T : TreeSubgraph G)
    (σ i : Fin n) (D : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact D.filter fun v => LiesOnPath T σ v i

/-- Set separation is separation of every cross pair. It is meaningful also
when a piece is empty, and includes path endpoints. -/
def SeparatesSets {G : ArcGraph n} (T : TreeSubgraph G) (i : Fin n)
    (L R : Finset (Fin n)) : Prop :=
  ∀ u ∈ L, ∀ v ∈ R, LiesOnPath T u v i

end SendSplit.Existence.Supplement


