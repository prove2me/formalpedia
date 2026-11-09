-- Prove2me | Definitions.Def_PhyloCSP_Template
-- name    : PhyloCSP_Template
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:22:08.051822+00:00
-- url     : https://prove2.me/theorems/71a7648a-66ac-45ef-bf3d-0087d730d677
-- title:
--   Template trees and their locations $\mathrm{Loc}(B)=L(B)\sqcup E(B)$
-- statement:
--   A **template** is a finite rooted tree $B$ in which every internal node has one or two children. Its **locations** are its leaves and its edges,
--   $$
--   \mathrm{Loc}(B)=L(B)\sqcup E(B).
--   $$
--
--   A template is encoded with vertices $0,1,\dots,n-1$, root $0$, a parent map (no parent exactly at the root, parents have smaller index) and at most two children per vertex. The leaves are the vertices with no children; each non-root vertex $v$ names the edge from its parent into $v$. The ancestor relation "$v$ lies at or below $w$" is computed from the parent map.
--
--   **Formalization Note** Every finite rooted tree with unary or binary internal nodes has such an encoding. "A template with at most $2N$ vertices" means $n\le 2N$.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 3.3, p.8 (PDF p.10)

import Mathlib

set_option autoImplicit false

namespace PhyloCSP

/-- **Template trees and their locations (Definition 3.3).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 3.3, p.8 (PDF p.10): "Fix a finite rooted template
tree B, in which every internal node has one or two children. Let L(B) and E(B) denote its leaves
and edges, which we will refer to as locations: Loc(B) = L(B) ⊔ E(B)."

A template has `n` vertices `Fin n`, root `0`, a parent map with `parent v = none` exactly at the
root and parents of smaller index, and at most two children per vertex. Its leaves are the
vertices without children; its edges are the non-root vertices (the edge into `v` from its
parent); `Loc B = L(B) ⊔ E(B)`.

**Formalization Note.** Unordered finite rooted trees are encoded by indexed parent maps; every
finite rooted tree whose internal nodes have one or two children has such an encoding (number the
vertices in breadth-first order). "A template with at most `2N` vertices" (Theorem 12.1) is
`B.n ≤ 2 * N`. Unary internal nodes are allowed, as in the paper. -/
structure Template where
  /-- The number of vertices. -/
  n : ℕ
  /-- The parent of each vertex (`none` at the root). -/
  parent : Fin n → Option (Fin n)
  n_pos : 0 < n
  parent_eq_none_iff : ∀ v, parent v = none ↔ v.val = 0
  parent_lt : ∀ v u, parent v = some u → u < v
  card_children_le : ∀ u, (Finset.univ.filter (fun v => parent v = some u)).card ≤ 2

namespace Template

/-- The template leaves `L(B)`: vertices that are nobody's parent. -/
abbrev Leaf (B : Template) : Type := {v : Fin B.n // ∀ w, B.parent w ≠ some v}

/-- The template edges `E(B)`: the edge into each non-root vertex `v`. -/
abbrev Edge (B : Template) : Type := {v : Fin B.n // v.val ≠ 0}

/-- The locations `Loc(B) = L(B) ⊔ E(B)`. -/
abbrev Loc (B : Template) : Type := B.Leaf ⊕ B.Edge

/-- The `k`-th ancestor of a vertex (`none` above the root). -/
def anc (B : Template) : ℕ → Fin B.n → Option (Fin B.n)
  | 0, v => some v
  | k + 1, v => (B.anc k v).bind B.parent

/-- `v` lies at or below `w` in the template. -/
def AtOrBelow (B : Template) (w v : Fin B.n) : Prop := ∃ k : Fin B.n, B.anc k v = some w

instance (B : Template) (w v : Fin B.n) : Decidable (B.AtOrBelow w v) := by
  unfold AtOrBelow; infer_instance

end Template

end PhyloCSP


