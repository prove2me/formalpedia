-- Prove2me | Definitions.Def_GapCliqueLB_Clique_Inputs
-- name    : GapCliqueLB_Clique_Inputs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:44:25.037207+00:00
-- url     : https://prove2.me/theorems/8ec1458f-7814-481d-96de-dee8e153a301
-- title:
--   Graphs, uniform hypergraphs, partite instances, and their encodings
-- statement:
--   A simple graph is supplied as a list of unordered edges, each with two distinct endpoints, with no repeated unordered edge. Its endpoint labels are arbitrary natural numbers; every ordering and orientation is permitted. With $M$ edges its word-list encoding is
--
--   $$[M,u_1,v_1,\ldots,u_M,v_M].$$
--
--   The $(h,s)$-Gap-Clique promise means that the graph contains $K_h$ or is $K_{s+1}$-free. A finite graph output additionally records its vertex count, retaining isolated vertices.
--
--   Uniform hypergraphs use the published general finite hypergraph object. Serialization records an ordered list of distinct hyperedges, each written as $r$ distinct vertices. An unrestricted instance has vertices $\{0,\ldots,n-1\}$ and encoding $[n,m,\text{edge endpoints}]$. A $k$-partite instance has actual part sizes $n_a$ and vertices $(a,x)$ with $x<n_a$; every hyperedge meets each part at most once. Its encoding records a declared bound $n$, $k$, $r$, the actual sizes, $m$, and all class/local-index pairs. Boundedness means $n_a\le n$ for every part, including empty parts.
--
--   A hyperclique is a vertex subset all of whose $r$-subsets are hyperedges. A multicolored hyperclique selects one vertex from every part. Sizes below $r$ are allowed and have no hyperedge obligations. These definitions provide the shared input interface for the hypothesis and both graph reductions.
-- source:
--   Reina Itakura, Karthik C.S., Mayank Motwani, Gary Peng, STOC 2027 submission #232 (October 2026), §1.1, PDF p. 3 (printed p. 2); §3, PDF p. 14 (printed p. 13); Theorem 4.4, PDF p. 15 (printed p. 14), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/232.pdf

import Mathlib
import Definitions.Def_TenChallenges_Hypergraph

namespace GapCliqueLB.Clique

/-- An ordered, arbitrarily oriented list of the edges of a simple graph. -/
structure GraphListing (V : Type) [DecidableEq V] where
  edges : List (V × V)
  loopless : ∀ e ∈ edges, e.1 ≠ e.2
  unique : (edges.map fun e => ({e.1, e.2} : Finset V)).Nodup

def GraphListing.graph {V : Type} [DecidableEq V] (L : GraphListing V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ({u, v} : Finset V) ∈ L.edges.map (fun e => {e.1, e.2})
  symm := ⟨by intros u v h; simpa [ne_comm, Finset.pair_comm] using h⟩
  loopless := ⟨by intros u h; exact h.1 rfl⟩

abbrev GraphInput := GraphListing ℕ

/-- M followed by all endpoint pairs; labels, orientations and order are unrestricted. -/
def encGraph (G : GraphInput) : List ℕ :=
  G.edges.length :: G.edges.flatMap (fun e => [e.1, e.2])

def HasClique {V : Type} (G : SimpleGraph V) (h : ℕ) : Prop :=
  ∃ S, G.IsNClique h S

/-- Requirements on the solver apply exactly to these promise inputs. -/
def GapClique (h s : ℕ) (G : GraphInput) : Prop :=
  HasClique G.graph h ∨ G.graph.CliqueFree (s + 1)

/-- An explicit finite output graph; the vertex count retains isolated vertices. -/
structure GraphOutput where
  vertices : ℕ
  listing : GraphListing (Fin vertices)

def GraphOutput.encode (G : GraphOutput) : List ℕ :=
  [G.vertices, G.listing.edges.length] ++
    G.listing.edges.flatMap (fun e => [e.1.val, e.2.val])

/-- Serialization data, not a new hypergraph model. Every unordered edge appears once. -/
structure EdgeInput (V : Type) [DecidableEq V] (r : ℕ) where
  edges : List (List V)
  arity : ∀ e ∈ edges, e.length = r
  distinct : ∀ e ∈ edges, e.Nodup
  unique : (edges.map List.toFinset).Nodup

/-- Interpret serialization data using the published general finite hypergraph. -/
def EdgeInput.graph {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}
    (H : EdgeInput V r) : FinHypergraph V where
  vertices := Finset.univ
  edges := {e | e ∈ H.edges.map List.toFinset}
  edges_subset_vertices := by intros; exact Finset.subset_univ _

/-- Including sizes smaller than r: the edge condition is then vacuous. -/
def IsHyperclique {V : Type} [DecidableEq V] (H : FinHypergraph V)
    (r : ℕ) (S : Finset V) : Prop :=
  S ⊆ H.vertices ∧ ∀ e ⊆ S, e.card = r → e ∈ H.edges

structure HyperInput (r : ℕ) where
  n : ℕ
  data : EdgeInput (Fin n) r

def HyperInput.contains {r : ℕ} (H : HyperInput r) (k : ℕ) : Prop :=
  ∃ S : Finset (Fin H.n), S.card = k ∧ IsHyperclique H.data.graph r S

/-- n, m, then all r vertex indices per edge, in their supplied order. -/
def encHyper {r : ℕ} (H : HyperInput r) : List ℕ :=
  [H.n, H.data.edges.length] ++ H.data.edges.flatMap (fun e => e.map Fin.val)

/-- k parts, variable actual sizes, and crossing r-edges. Empty parts are allowed. -/
structure PartiteInput (k r : ℕ) where
  sizes : Fin k → ℕ
  data : EdgeInput (Σ a : Fin k, Fin (sizes a)) r
  crossing : ∀ e ∈ data.edges, (e.map Sigma.fst).Nodup

abbrev PartiteInput.Vertex {k r : ℕ} (H : PartiteInput k r) :=
  Σ a : Fin k, Fin (H.sizes a)

def PartiteInput.Bounded {k r : ℕ} (H : PartiteInput k r) (n : ℕ) : Prop :=
  ∀ a, H.sizes a ≤ n

def PartiteInput.multicolored {k r : ℕ} (H : PartiteInput k r) : Prop :=
  ∃ c : (a : Fin k) → Fin (H.sizes a),
    IsHyperclique H.data.graph r
      (Finset.univ.image fun a => (⟨a, c a⟩ : H.Vertex))

/-- n is a declared upper bound; record actual sizes, then class/index endpoint pairs. -/
def encPartite {k r : ℕ} (n : ℕ) (H : PartiteInput k r) : List ℕ :=
  [n, k, r] ++ List.ofFn H.sizes ++ [H.data.edges.length] ++
    H.data.edges.flatMap (fun e => e.flatMap fun v => [v.1.val, v.2.val])

end GapCliqueLB.Clique


