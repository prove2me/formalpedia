-- Prove2me | Definitions.Def_TreeCorrMatch_ErrorFree_RootedTree
-- name    : TreeCorrMatch_ErrorFree_RootedTree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:24:03.57839+00:00
-- url     : https://prove2.me/theorems/8b3f657b-6d4e-4963-ba2a-eb281def4589
-- title:
--   Ordered rooted trees, unlabeled classes $[h]$, $\mathcal Z_k$, the count $r_m$ of rooted unlabeled trees and Otter's constant
-- statement:
--   A **rooted tree** is a finite tree with a distinguished root; the **depth** of a node is its distance to the root and the depth of the tree is the largest depth of a node. We work with **ordered rooted trees**: a root together with the ordered list of the subtrees rooted at its children (the labeled trees of §2.3, where children are labeled by their position among their siblings). For such a tree $h$ we use its number of nodes $|V(h)|$, its depth, the largest number of children of a node, and the subtree rooted at the vertex reached from the root by a given sequence of child positions.
--
--   Two ordered rooted trees are **isomorphic** when they agree after reordering the children of every node. The **unlabeled rooted tree** $[h]$ is the isomorphism class of $h$, and
--
--   $$\mathcal Z_k=\{[h] : h \text{ an ordered rooted tree of depth at most } k\}.$$
--
--   Let $r_m$ be the number of rooted unlabeled trees with $m$ nodes ($r_1,r_2,r_3,r_4,\dots=1,1,2,4,9,20,\dots$, OEIS A000081). **Otter's constant** is the radius of convergence of their generating function,
--
--   $$C_{\mathrm{Otter}}=\sup\Big\{x\ge 0:\ \sum_{m\ge 1} r_m x^m<\infty\Big\}\approx 0.3383 .$$
--
--   These are the tree objects on which the likelihood-ratio tests of the mission operate; the threshold $s>\sqrt{C_{\mathrm{Otter}}}\approx 0.5817$ of the correlation parameter is expressed through $C_{\mathrm{Otter}}$.
--
--   **Formalization Note** The unlabeled class is the quotient `Quot OTree.Iso` (`cls h`). Otter's constant is not defined in the paper (it cites Otter 1948); it is the reciprocal $1/\alpha$ of the growth rate $r_m\sim C\alpha^m m^{-3/2}$, $\alpha\approx 2.9558$. The set in the supremum contains $0$ and is bounded by $1$ (as $r_m\ge1$), so the real supremum is the radius of convergence.
-- source:
--   Cheng, Wang, Ying, Near-Quadratic Error-Free Graph Matching above Otter's Threshold via Approximate Local Tree Correlation Testing, arXiv:2611.02281 (held copy, sha256 0dfdbedd…), pp. 5–6, §2.1 and §2.3 (PDF pp. 7–8); C_Otter p. 1 (PDF p. 3)

import Mathlib

/-!
Ordered rooted trees, their unlabeled classes, the classes `Z_k` of depth at most `k`, the number
`r_m` of rooted unlabeled trees with `m` nodes, and Otter's constant `C_Otter`.

Cheng, Wang, Ying, *Near-Quadratic Error-Free Graph Matching above Otter's Threshold via
Approximate Local Tree Correlation Testing*, arXiv:2611.02281 (held copy, sha256 0dfdbedd…),
§2.1 and §2.3, pp. 5–6; Otter's constant p. 1 (cited from Otter 1948).
-/

namespace TreeCorrMatch.ErrorFree

/-- A finite **ordered rooted tree**: a root together with the ordered list of the subtrees rooted
at its children (the paper's labeled trees of §2.3, children labeled by their position). -/
inductive OTree : Type
  | node : List OTree → OTree

namespace OTree

/-- The single-node tree. -/
def leaf : OTree := node []

/-- The ordered list of subtrees rooted at the children of the root. -/
def children : OTree → List OTree
  | node cs => cs

/-- The number of nodes `|V(t)|`. -/
def size : OTree → ℕ
  | node cs => 1 + (cs.map size).sum

/-- The depth: the maximum distance from the root to a node (`0` for a single node). -/
def depth : OTree → ℕ
  | node cs => (cs.map fun c => depth c + 1).foldr max 0

/-- The maximum number of children of a node of the tree. -/
def maxChildren : OTree → ℕ
  | node cs => (cs.map maxChildren).foldr max cs.length

/-- The subtree rooted at the vertex with position `p` (the list of child indices, `0`-based, read
from the root), or `none` if there is no such vertex. -/
def subtreeAt : OTree → List ℕ → Option OTree
  | t, [] => some t
  | node cs, i :: p =>
    match cs[i]? with
    | some c => subtreeAt c p
    | none => none

/-- Root-preserving isomorphism of ordered rooted trees, forgetting the order of children:
`node cs ≅ node ds` when some reordering of `ds` is elementwise isomorphic to `cs`. -/
inductive Iso : OTree → OTree → Prop
  | mk {cs ds : List OTree} (es : List OTree) (hp : es.Perm ds) (hf : List.Forall₂ Iso cs es) :
      Iso (node cs) (node ds)

end OTree

/-- **Rooted unlabeled trees**: ordered rooted trees up to root-preserving isomorphism (the
paper's `[h]`, §2.3). -/
def UTree : Type := Quot OTree.Iso

/-- The unlabeled class `[h]` of an ordered rooted tree `h`. -/
def cls (h : OTree) : UTree := Quot.mk _ h

/-- `Z_k`: the rooted unlabeled trees of depth at most `k`. -/
def Zk (k : ℕ) : Set UTree := {x | ∃ h : OTree, cls h = x ∧ h.depth ≤ k}

/-- `r_m`: the number of rooted unlabeled trees with `m` nodes (OEIS A000081:
`1, 1, 2, 4, 9, 20, 48, 115, …` for `m = 1, 2, …`). -/
noncomputable def rootedTreeCount (m : ℕ) : ℕ :=
  Set.ncard {x : UTree | ∃ h : OTree, cls h = x ∧ h.size = m}

/-- **Otter's constant** `C_Otter ≈ 0.3383`: the radius of convergence of the generating function
`∑ₘ r_m x^m` of rooted unlabeled trees, i.e. the supremum of the `x ≥ 0` at which the series
converges. -/
noncomputable def otterConst : ℝ :=
  sSup {x : ℝ | 0 ≤ x ∧ Summable fun m : ℕ => (rootedTreeCount m : ℝ) * x ^ m}

end TreeCorrMatch.ErrorFree


