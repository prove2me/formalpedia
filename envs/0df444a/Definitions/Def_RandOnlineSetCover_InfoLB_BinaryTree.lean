-- Prove2me | Definitions.Def_RandOnlineSetCover_InfoLB_BinaryTree
-- name    : RandOnlineSetCover_InfoLB_BinaryTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:51.513558+00:00
-- url     : https://prove2.me/theorems/49861ab4-9a90-4ed1-b940-60486c933851
-- title:
--   Complete binary trees, rooted subtrees, boundary and colors
-- statement:
--   A complete binary tree with $h$ levels has vertices given by bit words of lengths $0,\ldots,h-1$. The empty word is the root. One vertex is an ancestor of another if its word is a prefix; a child extends that word by one bit. A subtree rooted at $v$ is a finite set of descendants that contains every intermediate ancestor between $v$ and each of its vertices. The empty subtree rooted at $v$ is also permitted.
--
--   For a rooted subtree $H$, its boundary is
--
--   $$
--   \partial H=\{u\notin H:\operatorname{parent}(u)\in H\}\cup(H\cap\operatorname{Leaves}(T)),\qquad
--   \partial\varnothing(v)=\{v\}.
--   $$
--
--   A coloring $\chi:V\to[m]$ gives the set $\chi(H)=\{\chi(u):u\in H\}$ of colors on $H$ itself. This is different from the color set of its boundary.
--
--   These definitions provide the common tree vocabulary for the inner-instance construction and the expansion property of the coloring.
--
--   **Formalization Note** Words are represented by a depth and a Boolean vector of that depth. A tree of height $2k$ in this paper has $2k$ levels, not $2k$ edges on its root-to-leaf paths. The general tree interface is independent of the set-cover model.
-- source:
--   Roie Levin, STOC 2027 submission #400 (October 2026), §3.1, pp. 3–4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/400.pdf

import Mathlib

namespace RandOnlineSetCover.InfoLB

/-- A complete binary tree with h levels: a vertex is its root-to-vertex bit word. -/
abbrev BinaryVertex (h : ℕ) := Σ d : Fin h, Fin d.val → Bool

/-- u is an ancestor of v, including equality. -/
def IsAncestor {h : ℕ} (u v : BinaryVertex h) : Prop :=
  ∃ hdepth : u.1.val ≤ v.1.val,
    ∀ i : Fin u.1.val, u.2 i = v.2 ⟨i.val, lt_of_lt_of_le i.isLt hdepth⟩

/-- Parent-child relation; root has no parent. -/
def IsChild {h : ℕ} (u v : BinaryVertex h) : Prop :=
  IsAncestor u v ∧ v.1.val = u.1.val + 1

def treeRoot (h : ℕ) (hh : 0 < h) : BinaryVertex h :=
  ⟨⟨0, hh⟩, fun i => Fin.elim0 i⟩

/-- The empty rooted subtree is allowed; nonempty ones contain their root and every
intermediate ancestor. This is exactly a connected vertex set inside its descendants. -/
def IsRootedSubtree {h : ℕ} (v : BinaryVertex h)
    (H : Finset (BinaryVertex h)) : Prop :=
  (∀ u ∈ H, IsAncestor v u) ∧
  ∀ u ∈ H, ∀ w, IsAncestor v w → IsAncestor w u → w ∈ H

/-- §3.1: outside children and included leaves; the empty subtree has boundary {v}. -/
noncomputable def boundary {h : ℕ} (v : BinaryVertex h)
    (H : Finset (BinaryVertex h)) : Finset (BinaryVertex h) := by
  classical
  exact if H = ∅ then {v} else
    Finset.univ.filter fun u =>
      (u ∉ H ∧ ∃ p ∈ H, IsChild p u) ∨ (u ∈ H ∧ u.1.val + 1 = h)

/-- Colors present on the vertices themselves (as opposed to the boundary). -/
noncomputable def subtreeColors {h m : ℕ} (χ : BinaryVertex h → Fin m)
    (H : Finset (BinaryVertex h)) : Finset (Fin m) := H.image χ

end RandOnlineSetCover.InfoLB


