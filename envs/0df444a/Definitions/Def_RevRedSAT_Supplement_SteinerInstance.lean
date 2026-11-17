-- Prove2me | Definitions.Def_RevRedSAT_Supplement_SteinerInstance
-- name    : RevRedSAT_Supplement_SteinerInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:56:34.612208+00:00
-- url     : https://prove2.me/theorems/28ef5dab-29e8-4f5f-9d30-941934b56799
-- title:
--   Steiner Tree instances and Max Leaf Spanning Tree solutions
-- statement:
--   An instance of **Steiner Tree** (App. C.3) is a finite simple graph $G$ on $n$ vertices, a terminal set $R\subseteq V(G)$ and a budget $b$. Its code lists $n$, the edges, the terminals, and then $b$.
--
--   A set $T$ of edges is a **feasible Steiner solution** if $T\subseteq E(G)$, $|T|\le b$, and the graph with vertex set $R\cup V(T)$ and edge set $T$ is a tree, or $R=T=\emptyset$. A single terminal with no edge is a one-vertex tree.
--
--   For **Max Leaf Spanning Tree** (App. C.4) the instance is $G$ with a leaf target $k$. A set $T$ of edges is feasible if $T\subseteq E(G)$, the graph $(V(G),T)$ is a tree, and at least $k$ vertices lie on exactly one edge of $T$ (the leaves). A one-vertex tree has no leaves and a two-vertex tree has two.
--
--   **Formalization Note** A tree subgraph is identified with its edge set. Mathlib's trees are nonempty, so the graph with no vertices has no spanning tree.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C.3, p.94 (Steiner Tree); App. C.4, p.94 (Max Leaf Spanning Tree)

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RevRedSAT_SearchWithin
import Definitions.Def_RevRedSAT_VCInstance
import Definitions.Def_RevRedSAT_Supplement_IsEdgeListing

set_option autoImplicit false

namespace RevRedSAT.Supplement

open RSListDecodingCapacity.AllRates

/-- **An instance of (unweighted) Steiner Tree.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C.3, p.94: "Steiner Tree. Given G, a terminal set R ⊆ V(G), and a budget b, find a tree
subgraph of G that contains every terminal and has at most b edges. The tree may also contain
vertices outside R and need not be induced. If R is empty, the empty solution is admitted; a single
terminal needs no edge."

**Formalization Note** Vertices are `Fin n`; the budget is a nonnegative integer (App. C, p.92). -/
structure SteinerInstance where
  /-- the number of vertices -/
  n : ℕ
  /-- the graph -/
  G : SimpleGraph (Fin n)
  /-- the terminal set -/
  R : Finset (Fin n)
  /-- the budget on the number of edges -/
  b : ℕ

/-- The codes of a Steiner Tree instance: `n`, a listing of the edges (`IsEdgeListing`), a
duplicate-free list of the terminals in any order, then the budget `b` last, every number in
self-delimiting binary. -/
def IsSteinerCode (I : SteinerInstance) (w : List Bool) : Prop :=
  ∃ E : List (Fin I.n × Fin I.n), IsEdgeListing I.G E ∧
    ∃ Rl : List (Fin I.n), Rl.Nodup ∧ Rl.toFinset = I.R ∧
      w = encNat I.n ++ encList encEdge E ++ encSet Rl ++ encNat I.b

/-- The vertex set `R ∪ V(T)` spanned by a candidate solution `T`: the terminals and the endpoints
of the edges of `T`. -/
def steinerVertices {n : ℕ} (R : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : Set (Fin n) :=
  (R : Set (Fin n)) ∪ {v | ∃ e ∈ T, v ∈ e}

/-- **Feasible solutions of Steiner Tree**, as edge sets: `T` is a set of at most `b` edges of `G`
such that the graph with vertex set `R ∪ V(T)` and edge set `T` is a tree, or this vertex set is
empty (the empty solution for `R = ∅`). A single terminal with no edge is a one-vertex tree. -/
def SteinerValid (I : SteinerInstance) (T : Finset (Sym2 (Fin I.n))) : Prop :=
  (∀ e ∈ T, e ∈ I.G.edgeSet) ∧ T.card ≤ I.b ∧
    (steinerVertices I.R T = ∅ ∨
      ((SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin I.n)))).induce
        (steinerVertices I.R T)).IsTree)

/-- **Feasible solutions of Max Leaf Spanning Tree**, as edge sets (App. C.4, p.94: "Given G and a
target k, find a spanning tree with at least k leaves, where a leaf has degree one in the tree. … A
one-vertex tree has zero leaves and a two-vertex tree has two. A disconnected nonempty graph has no
spanning tree"). On `(n, G, k)` (the published `RevRedSAT.VCInstance`, `k` the leaf target), `T` is
a set of edges of `G` forming a tree on all `n` vertices, in which at least `k` vertices lie on
exactly one edge of `T`.

**Formalization Note** Mathlib's trees are nonempty, so the graph with no vertices has no spanning
tree. -/
def MaxLeafValid (I : VCInstance) (T : Finset (Sym2 (Fin I.n))) : Prop :=
  (∀ e ∈ T, e ∈ I.G.edgeSet) ∧ (SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin I.n)))).IsTree ∧
    I.k ≤ (Finset.univ.filter fun v => (T.filter fun e => v ∈ e).card = 1).card

end RevRedSAT.Supplement


