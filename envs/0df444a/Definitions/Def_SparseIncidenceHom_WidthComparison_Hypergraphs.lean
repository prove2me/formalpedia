-- Prove2me | Definitions.Def_SparseIncidenceHom_WidthComparison_Hypergraphs
-- name    : SparseIncidenceHom_WidthComparison_Hypergraphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:31.199384+00:00
-- url     : https://prove2.me/theorems/154e5c2b-f4e7-4f4c-a041-b5106e8a74b2
-- title:
--   Finite covered hypergraphs, projected subhypergraphs, and structural graph invariants
-- statement:
--   Let $V$ be a finite vertex set. A hypergraph $H=(V,E)$ has a set of nonempty subsets as edges, and every vertex belongs to an edge. The base object permits the empty hypergraph and disconnected hypergraphs. The input predicate separately requires a nonempty connected primal graph. For $W\subseteq V$, projection is
--   $$E(H[W])=\{e\cap W:e\in E,\ e\cap W\ne\varnothing\}.$$
--   Equal projected edges merge. The primal graph $P(H)$ joins distinct vertices that share an edge; the incidence graph $I(H)$ has disjoint vertex and edge parts with membership as adjacency. Their invariants are
--   $$\alpha(H)=\max\{|S|:S\subseteq V\text{ independent in }P(H)\},\qquad
--   \mu(H)=\max_{F\subseteq I(H),\ V(F)\ne\varnothing}\min_{v\in V(F)}\deg_F(v).$$
--   Both invariants are zero on the empty hypergraph. Components after deleting $S$ are the reachable classes of the primal graph induced on $V\setminus S$.
--
--   These objects provide the shared finite combinatorial substrate for all width and separator statements. Mathlib supplies the unrestricted hypergraph and simple-graph types; the additional fields impose exactly the source's conventions. No rank, degree or uniformity condition is imposed.
-- source:
--   Matthias Lanzinger, STOC 2027 submission #662 (October 2026), pp. 7–8, Section 2.1 and incidence degeneracy definition

import Mathlib

namespace SparseIncidenceHom.WidthComparison

/-- Section 2.1, p. 7. Finiteness is supplied by the carrier, without connectivity restrictions. -/
structure FiniteHypergraph (V : Type) where
  graph : Hypergraph V
  all_vertices : graph.vertexSet = Set.univ
  edge_nonempty : ∀ e ∈ graph.edgeSet, e.Nonempty
  covered : ∀ v : V, ∃ e ∈ graph.edgeSet, v ∈ e

abbrev Edge {V : Type} (H : FiniteHypergraph V) := {e : Set V // e ∈ H.graph.edgeSet}

noncomputable instance edgeFintype {V : Type} [Fintype V] (H : FiniteHypergraph V) :
    Fintype (Edge H) := Fintype.ofFinite _

/-- Projection, with equal intersections identified as elements of a set. -/
def induced {V : Type} (H : FiniteHypergraph V) (W : Set V) : FiniteHypergraph W where
  graph := {
    vertexSet := Set.univ
    edgeSet := {f | f.Nonempty ∧ ∃ e ∈ H.graph.edgeSet, f = {v : W | v.val ∈ e}}
    subset_vertexSet_of_mem_edgeSet' := fun _ _ => Set.subset_univ _ }
  all_vertices := rfl
  edge_nonempty := fun _ h => h.1
  covered := by
    intro v
    obtain ⟨e, he, hv⟩ := H.covered v.val
    exact ⟨{u : W | u.val ∈ e}, ⟨⟨v, hv⟩, e, he, rfl⟩, hv⟩

/-- Distinct endpoints are essential: Hypergraph.Adj itself is reflexive on covered vertices. -/
def primal {V : Type} (H : FiniteHypergraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ e ∈ H.graph.edgeSet, u ∈ e ∧ v ∈ e
  symm := ⟨by
    rintro u v ⟨hne, e, he, hu, hv⟩
    exact ⟨hne.symm, e, he, hv, hu⟩⟩
  loopless := ⟨by simp⟩

def InputHypergraph {V : Type} (H : FiniteHypergraph V) : Prop :=
  Nonempty V ∧ (primal H).Connected

/-- The actual bipartite incidence graph, including one vertex for each distinct hyperedge. -/
def incidence {V : Type} (H : FiniteHypergraph V) : SimpleGraph (V ⊕ Edge H) where
  Adj a b := match a, b with
    | Sum.inl v, Sum.inr e => v ∈ e.val
    | Sum.inr e, Sum.inl v => v ∈ e.val
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> simp⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

noncomputable def independenceNumber {V : Type} [Fintype V] (H : FiniteHypergraph V) : ℕ :=
  sSup {k | ∃ S : Set V, S.ncard = k ∧
    ∀ u ∈ S, ∀ v ∈ S, ¬ (primal H).Adj u v}

/-- Maximum minimum degree over every nonempty subgraph, not maximum vertex degree. -/
noncomputable def incidenceDegeneracy {V : Type} [Fintype V] (H : FiniteHypergraph V) : ℕ :=
  sSup {k | ∃ F : (incidence H).Subgraph, F.verts.Nonempty ∧
    k = sInf ((fun v => (F.neighborSet v).ncard) '' F.verts)}

/-- Vertex sets of components after deleting S, using original primal adjacency. -/
def IsComponentAfter {V : Type} (H : FiniteHypergraph V) (S C : Set V) : Prop :=
  ∃ v : {u : V // u ∉ S}, C = {u | ∃ hu : u ∉ S,
    ((primal H).induce {u | u ∉ S}).Reachable v ⟨u, hu⟩}

end SparseIncidenceHom.WidthComparison


