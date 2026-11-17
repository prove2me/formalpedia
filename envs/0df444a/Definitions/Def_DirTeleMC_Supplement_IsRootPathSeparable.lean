-- Prove2me | Definitions.Def_DirTeleMC_Supplement_IsRootPathSeparable
-- name    : DirTeleMC_Supplement_IsRootPathSeparable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:39:21.87151+00:00
-- url     : https://prove2.me/theorems/a8a9d304-641d-4323-91fc-69f1deb2bb1a
-- title:
--   Underlying graphs, minor-closed classes and $p$-root-path separable graphs
-- statement:
--   The **underlying graph** of a digraph has the same vertices, two distinct vertices being adjacent if an arc joins them in either direction. A **class of graphs** is given by its graphs on the vertex sets $\{0,\dots,N-1\}$. It is **minor-closed** if it contains every graph isomorphic to one of its graphs, to one of its graphs with a vertex deleted, with an edge deleted, or with an edge contracted (and hence every graph isomorphic to a minor of one of its graphs).
--
--   For a tree $A$ on the vertices of a graph, a vertex $r$ and a set $Z$, the **root paths** $A[r,Z]$ are the union of the vertex sets of the paths of $A$ from $r$ to the vertices of $Z$. Let $p\ge1$. A connected graph $H$ is **$p$-root-path separable** if for every vertex $r$, every spanning tree $A$ of $H$ and all vertex weights $\mu\ge0$ there is a nonempty set $Z$ of at most $p$ vertices such that every component of $H-A[r,Z]$ has weight at most
--   $$\frac{\mu(V(H))}{2}.$$
--
--   These notions define the graph classes of Theorem 5.2.
--
--   **Formalization Note** Contraction of an edge $uv$ merges $v$ into $u$; deleting and contracting one edge or vertex at a time generates all minors, so closure under these four operations (with isomorphisms) is closure under minors.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), §5.1 and Definition 5.1, p.14 (PDF p.15); App. C, "Graph classes", p.36 (PDF p.37); Definition 5.1 restated, p.37 (PDF p.38)

import Mathlib

namespace DirTeleMC.Supplement

/-- **The underlying graph of a digraph** (§5.1, p.14; App. C, p.36: "The underlying graph of a digraph has the same
vertices, and two distinct vertices are adjacent in it if an arc joins them, in either direction").
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…). Loops and parallel arcs disappear. -/
def underlying {n : ℕ} (adj : Fin n → Fin n → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => adj u v = true

/-- A class of finite graphs, given by the graphs on the vertex sets `Fin N` that belong to it (App. C, p.36: "Graphs
in this appendix are undirected and have no loops or parallel edges").

**Formalization Note.** Every finite graph is isomorphic to one on some `Fin N`; closure under isomorphism is part
of `MinorClosed`. -/
abbrev GraphClass : Type := (N : ℕ) → SimpleGraph (Fin N) → Prop

/-- Contraction of the edge `uv` of `G` (App. C, p.36: "contracting the two ends of edges"): the vertex `v` is merged
into `u`; the result lives on the vertices other than `v`, and `u` is adjacent to every vertex adjacent to `u` or `v`.
-/
def contractEdge {N : ℕ} (G : SimpleGraph (Fin N)) (u v : Fin N) :
    SimpleGraph {x : Fin N // x ≠ v} :=
  SimpleGraph.fromRel fun a b => G.Adj a.1 b.1 ∨ (a.1 = u ∧ G.Adj v b.1)

/-- **A minor-closed class** (§5.1, p.14; App. C, p.36: "A class of graphs is minor-closed if it contains every graph
isomorphic to a minor of one of its graphs, that is, to a graph obtained from one of them by deleting vertices and
edges and contracting edges"). The class contains every graph isomorphic to one of its graphs, to one of its graphs
with a vertex deleted, with an edge deleted, or with an edge contracted; hence every graph isomorphic to a minor.

**Formalization Note.** The four one-step operations generate all minors; closure under each, with isomorphisms,
is closure under taking minors. -/
def MinorClosed (C : GraphClass) : Prop :=
  (∀ N (G : SimpleGraph (Fin N)) M (H : SimpleGraph (Fin M)), C N G → Nonempty (H ≃g G) → C M H) ∧
  (∀ N (G : SimpleGraph (Fin N)) (v : Fin N) M (H : SimpleGraph (Fin M)), C N G →
    Nonempty (H ≃g G.induce {x | x ≠ v}) → C M H) ∧
  (∀ N (G : SimpleGraph (Fin N)) (u v : Fin N), C N G → C N (G.deleteEdges {s(u, v)})) ∧
  (∀ N (G : SimpleGraph (Fin N)) (u v : Fin N) M (H : SimpleGraph (Fin M)), C N G → G.Adj u v →
    Nonempty (H ≃g contractEdge G u v) → C M H)

/-- **The root path set `A[r, Z]`** (§5.1, p.14: "the root path A[r, v] is the vertex set of the path in A from r to v,
and A[r, Z] is the union of the root paths to the vertices of a set Z"), for a tree `A`. -/
def rootPaths {N : ℕ} (A : SimpleGraph (Fin N)) (r : Fin N) (Z : Finset (Fin N)) : Set (Fin N) :=
  {x | ∃ z ∈ Z, ∃ w : A.Walk r z, w.IsPath ∧ x ∈ w.support}

/-- **A balanced set** for the weights `μ`: every connected component of `H − S` has weight at most `μ(V(H))/2`
(Definition 5.1, p.14). The component of `x ∉ S` is the set of `y ∉ S` reachable from `x` in `H − S`. -/
noncomputable def IsBalanced {N : ℕ} (H : SimpleGraph (Fin N)) (S : Set (Fin N)) (μ : Fin N → ℝ) : Prop := by
  classical
  exact ∀ x : Fin N, x ∉ S →
    (∑ y ∈ Finset.univ.filter fun y => ∃ hx : x ∈ Sᶜ, ∃ hy : y ∈ Sᶜ,
        (H.induce Sᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩, μ y) ≤ (∑ y, μ y) / 2

/-- **A `p`-root-path separable graph** (Definition 5.1, p.14, restated p.37).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…): "Let p ≥ 1 be an integer. A connected graph H is p-root-path separable if for every
vertex r of H, every spanning tree A of H rooted at r and all vertex weights μ on H, there is a nonempty set Z of at
most p vertices of H such that every component of H − A[r, Z] has weight at most μ(V(H))/2."

A spanning tree of `H` is a tree `A ≤ H` on the vertex set of `H`; vertex weights are nonnegative reals. -/
def IsRootPathSeparable (p : ℕ) {N : ℕ} (H : SimpleGraph (Fin N)) : Prop :=
  ∀ (r : Fin N) (A : SimpleGraph (Fin N)) (μ : Fin N → ℝ), A ≤ H → A.IsTree → (∀ v, 0 ≤ μ v) →
    ∃ Z : Finset (Fin N), Z.Nonempty ∧ Z.card ≤ p ∧ IsBalanced H (rootPaths A r Z) μ

end DirTeleMC.Supplement


