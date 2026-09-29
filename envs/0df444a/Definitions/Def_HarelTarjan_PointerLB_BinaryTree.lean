-- Prove2me | Definitions.Def_HarelTarjan_PointerLB_BinaryTree
-- name    : HarelTarjan_PointerLB_BinaryTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:37:58.871111+00:00
-- url     : https://prove2.me/theorems/c4780e30-3e4f-4b28-8a14-ef450732a11a
-- title:
--   The complete binary tree of height $h$, its leaves, ancestors and nearest common ancestors
-- statement:
--   The complete binary tree $T$ of height $h$, with $n = 2^h$ leaves, in which the lower bound of Harel and Tarjan's Theorem 1 is stated.
--
--   1. **Vertices.** A vertex is identified with the path from the root $r$ to it, written as a word $s \in \{0,1\}^{\le h}$ of left ($0$) and right ($1$) turns. The root is the empty word, the two children of $w$ are $w0$ and $w1$, and the depth of $w$ is its length $|w|$.
--   2. **Ancestors.** $w$ is an ancestor of $v$ (and $v$ a descendant of $w$) when $w$ is a prefix of $v$. As in the paper's Appendix, every vertex is an ancestor and a descendant of itself.
--   3. **Leaves.** A leaf is a vertex of depth $h$; the leaves form a finite set $L$ with $|L| = 2^h$. A vertex of depth $d$ has height $h - d$.
--   4. **Nearest common ancestor.** For vertices $x, y$,
--   $$\operatorname{nca}(x,y) = \text{the longest common prefix of } x \text{ and } y,$$
--   which is the vertex of greatest depth that is an ancestor of both $x$ and $y$ (Appendix, p. 355).
--
--   These objects fix the tree on which every nca query of the mission is asked.
--
--   **Formalization Note** `Vertex h` is the subtype of `List Bool` of length at most `h` (`false` = left). The longest common prefix `lcp` is defined by structural recursion, and `nca` packages it as a vertex using the structural lemma `lcp_length_le_left`. `leaves h` is the image of `List.Vector Bool h`. The identification of `nca` with the Appendix definition is the separate theorem `nca_isDeepestCommonAncestor`.
-- source:
--   Harel, Tarjan, Fast Algorithms for Finding Nearest Common Ancestors, SIAM J. Comput. 13 (1984), p. 340, §2 (Theorem 1, complete binary tree with n leaves); pp. 354–355, Appendix (tree terminology)

import Mathlib

namespace HarelTarjan.PointerLB

/-- The vertices of the complete binary tree of height `h` (Harel–Tarjan, §2 and Appendix,
pp. 340, 354–355). A vertex is the path from the root to it, written as a list of turns
(`false` = left child, `true` = right child), of length at most `h`. The root is `[]`, the
children of `w` are `w ++ [false]` and `w ++ [true]`, and the depth of `w` is its length. -/
abbrev Vertex (h : ℕ) : Type := {s : List Bool // s.length ≤ h}

/-- `w` is an ancestor of `v` (and `v` a descendant of `w`), in the Appendix's sense
`p^i(v) = w` for some `i ≥ 0`: the path to `w` is a prefix of the path to `v`. Every vertex is an
ancestor and a descendant of itself. -/
def IsAncestor {h : ℕ} (w v : Vertex h) : Prop := w.1 <+: v.1

/-- `v` is a leaf of the complete binary tree of height `h`: its depth is `h`. -/
def IsLeaf {h : ℕ} (v : Vertex h) : Prop := v.1.length = h

/-- The finite set of the `2 ^ h` leaves (the vertices of depth `h`). -/
def leaves (h : ℕ) : Finset (Vertex h) :=
  (Finset.univ : Finset (List.Vector Bool h)).map
    ⟨fun v : List.Vector Bool h => (⟨v.1, le_of_eq v.2⟩ : Vertex h),
      fun _ _ hab => Subtype.ext (congrArg (fun v : Vertex h => v.1) hab)⟩

/-- The longest common prefix of two lists of turns. -/
def lcp : List Bool → List Bool → List Bool
  | a :: x, b :: y => if a = b then a :: lcp x y else []
  | _, _ => []

/-- The longest common prefix is no longer than its first argument. -/
theorem lcp_length_le_left : ∀ x y : List Bool, (lcp x y).length ≤ x.length
  | a :: x, b :: y => by
      unfold lcp
      split_ifs
      · simpa using lcp_length_le_left x y
      · simp
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]

/-- The nearest common ancestor `nca(x, y)` of two vertices: the vertex whose path is the longest
common prefix of the paths to `x` and `y`, i.e. the vertex of greatest depth that is an ancestor
of both (Appendix, p. 355). -/
def nca {h : ℕ} (x y : Vertex h) : Vertex h :=
  ⟨lcp x.1 y.1, (lcp_length_le_left x.1 y.1).trans x.2⟩

end HarelTarjan.PointerLB


