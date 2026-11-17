-- Prove2me | Definitions.Def_RevRedSAT_Supplement_CVCValid
-- name    : RevRedSAT_Supplement_CVCValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:54:53.327206+00:00
-- url     : https://prove2.me/theorems/2f91f829-3d1b-4b8d-8d18-4c434083bd7a
-- title:
--   Feasible solutions of Connected Vertex Cover, Connected Dominating Set, Feedback Vertex Set, and Clique
-- statement:
--   All four problems take a finite simple graph $G$ on $n$ vertices and a number $k$ (the published `RevRedSAT.VCInstance`).
--
--   1. **Connected Vertex Cover** (App. C.3): $S$ is feasible if it is a vertex cover with $|S|\le k$ and, when $S\neq\emptyset$, the induced graph $G[S]$ is connected. The empty cover is admitted exactly for an edgeless graph.
--   2. **Connected Dominating Set** (App. C.3): $D$ is feasible if every vertex is in $D$ or adjacent to it, $|D|\le k$, and $G[D]$ is connected when $D\neq\emptyset$. The empty set dominates only the graph with no vertices.
--   3. **Feedback Vertex Set** (App. C.4): $S$ is feasible if $|S|\le k$ and $G-S$ (the subgraph induced on $V(G)\setminus S$) is acyclic.
--   4. **Clique** (App. C.6): the instance is a YES-instance if some $k$ vertices are pairwise adjacent.
--
--   **Formalization Note** Mathlib's connectedness requires a nonempty vertex set, which is why the empty set is handled by the implication "nonempty implies connected".
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C.3, p.93–94; App. C.4, p.94; App. C.6, p.95

import Mathlib
import Definitions.Def_RevRedSAT_VCInstance

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **Feasible solutions of Connected Vertex Cover.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C.3, p.94: "Connected Vertex Cover. Find a vertex cover S with |S| ≤ b such that G[S] is
connected when S is nonempty. We admit the empty cover for an edgeless graph."

On a graph-plus-number instance `(n, G, k)` (the published `RevRedSAT.VCInstance`, whose number
`k` is the budget `b`), `S` is feasible if it is a vertex cover of size at most `k` and, when
nonempty, induces a connected subgraph.

**Formalization Note** Mathlib's `Connected` requires a nonempty vertex type, so the empty cover is
admitted by the implication `S.Nonempty → …`; it is a cover exactly when `G` has no edges. -/
def CVCValid (I : VCInstance) (S : Finset (Fin I.n)) : Prop :=
  IsVertexCover I.G S ∧ S.card ≤ I.k ∧
    (S.Nonempty → (I.G.induce (S : Set (Fin I.n))).Connected)

/-- `D` dominates `G`: every vertex belongs to `D` or has a neighbour in `D` (App. C.3, p.93). -/
def IsDominating {n : ℕ} (G : SimpleGraph (Fin n)) (D : Finset (Fin n)) : Prop :=
  ∀ v, v ∈ D ∨ ∃ u ∈ D, G.Adj v u

/-- **Feasible solutions of Connected Dominating Set** (App. C.3, p.93: "Find a dominating set D with
|D| ≤ b such that the induced graph G[D] is connected. The empty set is admitted only when G is
empty"): a dominating set of size at most `k` that, when nonempty, induces a connected subgraph.
The empty set dominates exactly the graph with no vertices. -/
def CDSValid (I : VCInstance) (D : Finset (Fin I.n)) : Prop :=
  IsDominating I.G D ∧ D.card ≤ I.k ∧
    (D.Nonempty → (I.G.induce (D : Set (Fin I.n))).Connected)

/-- **Feasible solutions of Feedback Vertex Set** (App. C.4, p.94: "Given an undirected graph G and a
budget k, find S ⊆ V(G) with |S| ≤ k such that G − S is a forest, that is, contains no cycle"): at
most `k` vertices whose deletion leaves an acyclic induced subgraph. -/
def FVSValid (I : VCInstance) (S : Finset (Fin I.n)) : Prop :=
  S.card ≤ I.k ∧
    (I.G.induce ((Finset.univ \ S : Finset (Fin I.n)) : Set (Fin I.n))).IsAcyclic

/-- **YES-instances of Clique** (App. C.6, p.95: "Given a graph G and an integer ℓ, ask whether G
contains ℓ pairwise adjacent vertices"): on `(n, G, k)`, with `k` the clique size `ℓ`, some `k`
vertices are pairwise adjacent. -/
def CliqueYes (I : VCInstance) : Prop :=
  ∃ s : Finset (Fin I.n), I.G.IsNClique I.k s

end RevRedSAT.Supplement


