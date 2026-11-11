-- Prove2me | Definitions.Def_DirectedTreeCovers_Strong_Trees
-- name    : DirectedTreeCovers_Strong_Trees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:24:35.172227+00:00
-- url     : https://prove2.me/theorems/c3bff01e-ee9d-4fad-a42b-114c0df463a6
-- title:
--   Weighted directed tree-pairs, searches, stretch and overlap
-- statement:
--   A weighted rooted tree consists of bare rooted-tree data and an original parent-edge identity for each nonroot vertex. Validity requires a present root, parent closure, termination of every parent chain at the root, correctly directed edges, and shortest root paths in a stored induced subgraph. An incoming tree and an outgoing tree with a common root form a tree-pair; their supports may differ. For their actual union $T$, let $d_T$ be its directed walk distance. Strong stretch means
--
--   $$\forall u,v\in V,\quad\exists T\in\mathcal T:\ d_T(u,v)\le k\,d_G(u,v)+(k-1)d_G(v,u).$$
--
--   Overlap counts each tree-pair whose union support contains the vertex, once for that pair. The file computes shortest-path searches using tight edges that decrease the minimum shortest-walk hop count, with a fixed finite-set selector for remaining ties. It does not assume search correctness, stretch or overlap. Searches missing their root return an empty slot, rather than an invalid rooted object.
--
--   **Formalization Note** Distances use the original edges and weights, with infinity off support and $0\cdot\infty=0$. Parent termination excludes zero-weight parent cycles. Lists count repeated pair occurrences separately. Search tie-breaking is a fixed function of the graph and search region, independent of the random hierarchy.
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/840.pdf, §2, printed pp.6–7 (PDF pp.7–8); §5.1 and Algorithm 3, printed pp.16–17 (PDF pp.17–18)

import Mathlib
import Definitions.Def_DirectedTreeCovers_Strong_Distances
import Definitions.Def_PredAdvice_RootedTree

noncomputable section

namespace DirectedTreeCovers.Strong

open scoped Classical
open EulerSparsify
variable {V E : Type} [Fintype V] [Fintype E]

/-- Bare rooted-tree data plus the original edge chosen at each nonroot vertex. -/
structure WeightedTree (V E : Type) where
  rooted : PredAdvice.RootedTree V
  parentEdge : V → Option E

/-- Exactly the parent edges; values outside the support and at the root are ignored. -/
def treeEdges (T : WeightedTree V E) : Finset E :=
  Finset.univ.filter fun e => ∃ x ∈ T.rooted.verts,
    x ≠ T.rooted.root ∧ T.parentEdge x = some e

def treeDist (G : DiGraph V E) (T : WeightedTree V E) (u v : V) : ENNReal :=
  subdist G T.rooted.verts (treeEdges T) u v

/-- away = true for an out-tree, false for an in-tree. Parent termination is explicit:
tight distances alone would permit zero-weight parent cycles. Shortest paths are in X,
the induced construction subgraph, rather than necessarily in all of G (§§2,5.1). -/
def IsShortestTree (G : DiGraph V E) (X : Finset V) (away : Bool)
    (T : WeightedTree V E) : Prop :=
  T.rooted.root ∈ X ∧ T.rooted.root ∈ T.rooted.verts ∧
  T.rooted.verts ⊆ X ∧
  (∀ x ∈ T.rooted.verts, ∃ m : ℕ, (T.rooted.parent^[m]) x = T.rooted.root) ∧
  (∀ x ∈ T.rooted.verts, x ≠ T.rooted.root →
    T.rooted.parent x ∈ T.rooted.verts ∧ ∃ e, T.parentEdge x = some e ∧
      (if away then G.head e = T.rooted.parent x ∧ G.tail e = x
       else G.head e = x ∧ G.tail e = T.rooted.parent x)) ∧
  (∀ x ∈ T.rooted.verts,
    (if away then treeDist G T T.rooted.root x else treeDist G T x T.rooted.root) =
      (if away then inducedDist G X T.rooted.root x else inducedDist G X x T.rooted.root))

/-- A pair stores the induced search region and allows different in/out supports. -/
structure TreePair (V E : Type) where
  region : Finset V
  incoming : WeightedTree V E
  outgoing : WeightedTree V E

def IsTreePair (G : DiGraph V E) (T : TreePair V E) : Prop :=
  T.incoming.rooted.root = T.outgoing.rooted.root ∧
  IsShortestTree G T.region false T.incoming ∧ IsShortestTree G T.region true T.outgoing

def pairSupport (T : TreePair V E) : Finset V := T.incoming.rooted.verts ∪ T.outgoing.rooted.verts

/-- Shortest distance in the actual union, with infinity off its support. -/
def pairDist (G : DiGraph V E) (T : TreePair V E) (u v : V) : ENNReal :=
  subdist G (pairSupport T) (treeEdges T.incoming ∪ treeEdges T.outgoing) u v

def pairRoundtrip (G : DiGraph V E) (T : TreePair V E) (u v : V) : ENNReal :=
  pairDist G T u v + pairDist G T v u

/-- Fixed deterministic selection from a finite set; no random level is an argument. -/
def firstEdge (F : Finset E) : Option E := F.toList.head?

/-- Tight edges that also decrease minimum shortest-walk hop count. Selecting one gives
an acyclic shortest-path search even when there are zero-weight cycles. -/
def searchEdges (G : DiGraph V E) (X : Finset V) (w : V) (away : Bool) (x : V) : Finset E :=
  Finset.univ.filter fun e => x ≠ w ∧ G.head e ∈ X ∧ G.tail e ∈ X ∧
    if away then
      G.tail e = x ∧ inducedDist G X w (G.head e) ≠ ⊤ ∧
      inducedDist G X w (G.head e) + ENNReal.ofReal (G.w e) = inducedDist G X w x ∧
      shortestHops G X w (G.head e) + 1 = shortestHops G X w x
    else
      G.head e = x ∧ inducedDist G X (G.tail e) w ≠ ⊤ ∧
      ENNReal.ofReal (G.w e) + inducedDist G X (G.tail e) w = inducedDist G X x w ∧
      shortestHops G X (G.tail e) w + 1 = shortestHops G X x w

/-- Actual search data, computed from distances and hops, without a correctness hypothesis.
The default parent is used only if no tight decreasing-hop edge exists. -/
def searchTree (G : DiGraph V E) (X : Finset V) (w : V) (away : Bool) : WeightedTree V E where
  rooted := {
    root := w
    verts := Finset.univ.filter fun x => w ∈ X ∧ x ∈ X ∧
      (if away then inducedDist G X w x else inducedDist G X x w) ≠ ⊤
    parent := fun x => match firstEdge (searchEdges G X w away x) with
      | none => x
      | some e => if away then G.head e else G.tail e }
  parentEdge := fun x => firstEdge (searchEdges G X w away x)

/-- Searches on a region missing the root return no pair, rather than inventing a root
inside an empty cluster. This also covers genuinely empty expanded clusters. -/
def searchPair (G : DiGraph V E) (X : Finset V) (w : V) : Option (TreePair V E) :=
  if w ∈ X then some ⟨X, searchTree G X w false, searchTree G X w true⟩ else none

def optionRoundtrip (G : DiGraph V E) (T : Option (TreePair V E)) (u v : V) : ENNReal :=
  match T with
  | none => ⊤
  | some t => pairRoundtrip G t u v

/-- Exact strong stretch, in the source's second equivalent form (§2, printed p.7).
ENNReal uses 0 * infinity = 0, including at k = 1. -/
def StrongCover (G : DiGraph V E) (k : ℕ) (ts : List (TreePair V E)) : Prop :=
  (∀ T ∈ ts, IsTreePair G T) ∧ ∀ u v : V, ∃ T ∈ ts,
    pairDist G T u v ≤ (k : ENNReal) * dist G u v + ((k - 1 : ℕ) : ENNReal) * dist G v u

/-- Occurrences of the union support, counted once per pair. -/
def overlap (ts : List (TreePair V E)) (v : V) : ℕ :=
  (ts.filter fun T => v ∈ pairSupport T).length

end DirectedTreeCovers.Strong


