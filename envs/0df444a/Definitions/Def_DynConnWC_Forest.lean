-- Prove2me | Definitions.Def_DynConnWC_Forest
-- name    : DynConnWC_Forest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:30:38.514121+00:00
-- url     : https://prove2.me/theorems/5feb4bca-e4f9-49f9-90b9-2f3a4bd1e5f5
-- title:
--   Forests as edge sets, trees, cutsets and the forest deficit $D(F)$
-- statement:
--   A **forest** on $V$ is an acyclic set of pairs of distinct vertices; it need not consist of graph edges. $F\subseteq G$ means that all its pairs are edges of $G$. The **trees** of $F$ are the vertex sets of the connected components of the graph it spans on all of $V$, isolated vertices included, and the **representative** of a tree is its minimum vertex. A spanning forest of $G$ is a forest of $G$ with the same connected components as $G$.
--
--   An edge **leaves** $S\subseteq V$ if it has exactly one endpoint in $S$, and the **cutset** of $S$ is
--   $$\delta_G(S)=\{\{u,v\}\in E: |\{u,v\}\cap S|=1\}.$$
--   With $\mathrm{cc}(H)$ the number of connected components of $H$, the **forest deficit** is
--   $$D(F)=\mathrm{cc}(F)-\mathrm{cc}(G).$$
--   The deficit measures progress in the paper: for $F\subseteq G$ it is the number of edges still missing from a spanning forest.
--
--   **Formalization Note** The deficit is an integer, and it can be negative when $F\not\subseteq G$. The identity $D(F)=(n-|E_F|)-\mathrm{cc}(G)$ of Definition 2 follows from acyclicity and is not part of the definition.
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), §2, p.3 (PDF 4), Definition 2; §3.2, p.7 (PDF 8); invariant I2, p.17 (PDF 18)

import Mathlib

set_option autoImplicit false

namespace DynConnWC

/-! # Forests, trees, cutsets and the forest deficit

King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027
submission, sha256 9d16c13e…), §2, p.3: "All maintained forests have vertex set V, including
isolated vertices. Forests are defined by their edge sets. For a graph H, let cc(H) denote its
number of connected components, including isolated vertices. … A forest F is a forest of G,
written F ⊆ G, if all its edges belong to the current graph G. A spanning forest of G is a forest
of G with the same connected components as G. … An edge between a pair of vertices leaves a vertex
set S ⊆ V if it has exactly one endpoint in S. The cutset of S consists of the graph edges leaving
S: δ_G(S) = {{u, v} ∈ E : |{u, v} ∩ S| = 1}." Definition 2 (Forest Deficit), p.3: "For a forest
F = (V, E_F), its forest deficit with respect to the current graph G is
D(F) = cc(F) − cc(G) = (n − |E_F|) − cc(G)." Invariant I2, p.17: each maintained forest "is an
acyclic set of pairs of distinct vertices".

**Formalization Note.** A forest is a finite set of unordered pairs of vertices of `Fin n`
(`Finset (Sym2 (Fin n))`); `IsForestSet F` says the pairs are of distinct vertices and the graph
they span is acyclic. A forest need not consist of graph edges (Definition 4, p.5; A.3, p.30);
`SubG F G` is the relation `F ⊆ G`. The trees of `F` are the vertex sets of the connected
components of the graph spanned by `F` on all of `Fin n` (isolated vertices are trees). `cc` is
`Nat.card` of the connected components. The deficit is the integer `cc(F) − cc(G)` (negative
values are possible when `F ⊄ G`). The representative of a tree is its minimum vertex (§3.2,
p.7). A union of trees is the union of any subfamily of the trees, the empty one included. -/

variable {n : ℕ}

/-- The graph on `Fin n` spanned by a set of pairs (diagonal pairs are ignored). -/
def forestGraph (F : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))

/-- `F` is a forest: an acyclic set of pairs of distinct vertices. -/
def IsForestSet (F : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ F, ¬ e.IsDiag) ∧ (forestGraph F).IsAcyclic

/-- `F ⊆ G`: every pair of `F` is an edge of `G`. -/
def SubG (F : Finset (Sym2 (Fin n))) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ e ∈ F, e ∈ G.edgeSet

open Classical in
/-- The vertex set of the tree of `F` containing `v`. -/
noncomputable def treeOf (F : Finset (Sym2 (Fin n))) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => (forestGraph F).Reachable v u)

theorem mem_treeOf_self (F : Finset (Sym2 (Fin n))) (v : Fin n) : v ∈ treeOf F v := by
  classical
  simp [treeOf]

open Classical in
/-- The trees of `F`, as vertex sets. -/
noncomputable def trees (F : Finset (Sym2 (Fin n))) : Finset (Finset (Fin n)) :=
  Finset.univ.image (treeOf F)

/-- The representative `z(P)` of the tree of `F` containing `v`: its minimum vertex. -/
noncomputable def rep (F : Finset (Sym2 (Fin n))) (v : Fin n) : Fin n :=
  (treeOf F v).min' ⟨v, mem_treeOf_self F v⟩

/-- `cc(H)`: the number of connected components of `H`, isolated vertices included. -/
noncomputable def cc (H : SimpleGraph (Fin n)) : ℕ := Nat.card H.ConnectedComponent

/-- **Definition 2.** The forest deficit `D(F) = cc(F) − cc(G)` of `F` with respect to `G`. -/
noncomputable def deficit (G : SimpleGraph (Fin n)) (F : Finset (Sym2 (Fin n))) : ℤ :=
  (cc (forestGraph F) : ℤ) - cc G

/-- The pair `e` leaves the vertex set `S`: exactly one of its endpoints lies in `S`. -/
def Leaves (S : Finset (Fin n)) (e : Sym2 (Fin n)) : Prop :=
  ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∉ S

open Classical in
/-- The cutset `δ_G(S)`: the edges of `G` with exactly one endpoint in `S`. -/
noncomputable def cutset (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter (fun e => e ∈ G.edgeSet ∧ Leaves S e)

open Classical in
/-- The unions of trees of `F` (of every subfamily of its trees, the empty one included). -/
noncomputable def unionsOfTrees (F : Finset (Sym2 (Fin n))) : Finset (Finset (Fin n)) :=
  (trees F).powerset.image (fun 𝒯 => 𝒯.biUnion id)

/-- `u` and `v` lie in the same tree of `F`. -/
def SameTree (F : Finset (Sym2 (Fin n))) (u v : Fin n) : Prop := (forestGraph F).Reachable u v

/-- `F` is a spanning forest of `G`: a forest of `G` with the same connected components. -/
def IsSpanningForestOf (F : Finset (Sym2 (Fin n))) (G : SimpleGraph (Fin n)) : Prop :=
  IsForestSet F ∧ SubG F G ∧ ∀ u v, SameTree F u v ↔ G.Reachable u v

end DynConnWC


