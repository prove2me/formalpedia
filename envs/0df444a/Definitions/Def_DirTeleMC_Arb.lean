-- Prove2me | Definitions.Def_DirTeleMC_Arb
-- name    : DirTeleMC_Arb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:29:37.37628+00:00
-- url     : https://prove2.me/theorems/1df8d8a2-4055-4407-ac3b-b50a22277c01
-- title:
--   Out-arborescences, their height, leaves, out-degrees and child orders
-- statement:
--   An **out-arborescence** of $G$ rooted at $r$ is a rooted tree on a set of vertices of $G$ in which every non-root vertex $v$ is entered by the arc $(\mathrm{parent}(v), v)$ of $G$. The **depth** of a vertex is its number of arcs from the root, the **height** is the largest depth, a **leaf** is a vertex without children, and the **out-degree** of a vertex is its number of children. For a vertex $u$, its **subtree** consists of the vertices below it (including $u$), its leaf count is the number of leaves in it, and its size the number of its vertices.
--
--   A **child order** lists, for every vertex, its children, each once. A **directed path of the arborescence** from $u$ to $w$ is a vertex sequence starting at $u$ and ending at $w$ in which each entry is a child of the previous one (the empty path when $u = w$).
--
--   **Formalization Note** The arborescence is a root, a vertex set and a parent map whose iterates reach the root; the parent of the root is the root itself.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), §3, pp.8–9 (PDF pp.9–10); Lemma 4.2, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_DirTeleMC_IsJump

namespace DirTeleMC

/-- **Out-arborescences** given by a parent map.
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), §3, p.8: "an out-arborescence: a directed tree rooted at s, with all arcs
pointing away from s".

An `Arb n` is a root, a vertex set and a parent map; `Arb.IsTree` and `Arb.IsIn` below say when it is an
out-arborescence (of a digraph `adj`).

**Formalization Note.** The parent of the root is the root itself (a convention; it carries no arc). -/
structure Arb (n : ℕ) where
  root : Fin n
  verts : Finset (Fin n)
  parent : Fin n → Fin n

namespace Arb

variable {n : ℕ}

/-- `A` is a rooted tree: the root is a vertex, the parent of every other vertex is a vertex, and iterating
the parent map from every vertex reaches the root (so there is no cycle). -/
def IsTree (A : Arb n) : Prop :=
  A.root ∈ A.verts ∧ A.parent A.root = A.root ∧
    (∀ v ∈ A.verts, A.parent v ∈ A.verts) ∧ ∀ v ∈ A.verts, ∃ m, A.parent^[m] v = A.root

/-- `A` is an out-arborescence of the digraph `adj`: a rooted tree in which every vertex other than the root
is entered by the arc `(parent v, v)` of the digraph. -/
def IsIn (adj : Fin n → Fin n → Bool) (A : Arb n) : Prop :=
  A.IsTree ∧ ∀ v ∈ A.verts, v ≠ A.root → adj (A.parent v) v = true

/-- The children of `u`: the vertices other than the root whose parent is `u`. -/
def children (A : Arb n) (u : Fin n) : Finset (Fin n) :=
  A.verts.filter fun c => c ≠ A.root ∧ A.parent c = u

/-- The leaves: the vertices without children. -/
def leaves (A : Arb n) : Finset (Fin n) :=
  A.verts.filter fun u => A.children u = ∅

/-- The depth of `v`, the least `m` with `parent^[m] v = root` (`0` if there is none, which does not happen
for a vertex of a tree). -/
noncomputable def depth (A : Arb n) (v : Fin n) : ℕ := by
  classical
  exact if h : ∃ m, A.parent^[m] v = A.root then Nat.find h else 0

/-- The height: the largest depth of a vertex. -/
noncomputable def height (A : Arb n) : ℕ := A.verts.sup A.depth

/-- The vertex set of the subtree of `u`: the vertices having `u` as an ancestor (or equal to `u`). -/
noncomputable def subtree (A : Arb n) (u : Fin n) : Finset (Fin n) := by
  classical
  exact A.verts.filter fun v => ∃ m, A.parent^[m] v = u

/-- The number of leaves of the subtree of `u`. -/
noncomputable def leafCount (A : Arb n) (u : Fin n) : ℕ := (A.leaves ∩ A.subtree u).card

/-- The number of vertices of the subtree of `u`. -/
noncomputable def subtreeSize (A : Arb n) (u : Fin n) : ℕ := (A.subtree u).card

/-- The maximum out-degree bound: every vertex has at most `d` children. -/
def OutDegLE (A : Arb n) (d : ℕ) : Prop := ∀ u ∈ A.verts, (A.children u).card ≤ d

/-- A child order: for every vertex `u`, `ord u` lists the children of `u`, each exactly once. -/
def IsChildOrder (A : Arb n) (ord : Fin n → List (Fin n)) : Prop :=
  ∀ u ∈ A.verts, (ord u).Nodup ∧ ∀ c, c ∈ ord u ↔ c ∈ A.children u

/-- `P` is a (possibly empty) directed path of `A` from `u` to `w`: a vertex list starting at `u`, ending at
`w`, in which every entry after the first is a child of the entry before it. -/
def IsTreePath (A : Arb n) (u : Fin n) (P : List (Fin n)) (w : Fin n) : Prop :=
  P.head? = some u ∧ P.getLast? = some w ∧ u ∈ A.verts ∧ P.IsChain fun a b => b ∈ A.children a

end Arb

end DirTeleMC


