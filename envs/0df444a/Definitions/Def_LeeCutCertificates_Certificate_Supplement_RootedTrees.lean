-- Prove2me | Definitions.Def_LeeCutCertificates_Certificate_Supplement_RootedTrees
-- name    : LeeCutCertificates_Certificate_Supplement_RootedTrees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:00:46.27118+00:00
-- url     : https://prove2.me/theorems/e0151143-2353-49c3-8734-5dc4b6382a7f
-- title:
--   Finite-label tree APIs over the published rooted-tree model
-- statement:
--   The published general rooted-tree model is reused on $n$ labeled vertices: a tree $T$ has a root and a parent map. The root is its own parent, and every vertex reaches it by finitely many parent steps. Descendants and root paths include their endpoints. Every nonroot vertex indexes its parent edge once. For a shore $S$, write $\partial_T(S)$ for the parent edges with unequal endpoint labels. Then
--
--   $$S\text{ two-respects }T\quad\Longleftrightarrow\quad \varnothing\ne S\ne V,\quad |\partial_T(S)|\le2.$$
--
--   This representation includes one-edge cuts and does not relate tree edges to any graph's support. Rooting an undirected supplied tree is free public preprocessing.
--
--   **Formalization Note** `RootedTree n` and its ancestor relation are aliases of the published `HarelTarjan.Compressed.RootedTree (Fin n)` and `IsAncestor`. No new general tree structure is defined. Vertices are `Fin n`. The reach-root condition excludes every nonroot cycle; it imposes no bound on depth or vertex degree.
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), §8.2, printed pp.24–25 (PDF pp.25–26); §12, printed p.43 (PDF p.44)

import Definitions.Def_HarelTarjan_Compressed_RootedTree

set_option autoImplicit false
open Classical

namespace LeeCutCertificates.Certificate.Supplement

/-- The published general rooted-tree object, specialized to the finite vertex labels. -/
abbrev RootedTree (n : ℕ) := HarelTarjan.Compressed.RootedTree (Fin n)

/-- The published inclusive ancestor relation, with the local finite-label interface. -/
abbrev RootedTree.Ancestor {n : ℕ} (T : RootedTree n) (u v : Fin n) : Prop :=
  HarelTarjan.Compressed.IsAncestor T u v

noncomputable def RootedTree.subtree {n : ℕ} (T : RootedTree n) (v : Fin n) :
    Finset (Fin n) := Finset.univ.filter (T.Ancestor v)

/-- Each nonroot vertex indexes one unordered edge, counted once. -/
noncomputable def RootedTree.cross {n : ℕ} (T : RootedTree n) (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun v => v ≠ T.root ∧ ¬ (v ∈ S ↔ T.parent v ∈ S)).card

/-- Nontrivial shores crossing at most two edges; one-edge shores are included. -/
def RootedTree.TwoRespects {n : ℕ} (T : RootedTree n) (S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ S ≠ Finset.univ ∧ T.cross S ≤ 2

end LeeCutCertificates.Certificate.Supplement


