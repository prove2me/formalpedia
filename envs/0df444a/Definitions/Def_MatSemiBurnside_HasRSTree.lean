-- Prove2me | Definitions.Def_MatSemiBurnside_HasRSTree
-- name    : MatSemiBurnside_HasRSTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:38:53.825232+00:00
-- url     : https://prove2.me/theorems/5f8ff8ff-625d-4a13-9d25-3d4baf422d70
-- title:
--   Rank-stable factorisation trees of bounded height
-- statement:
--   For a matrix product $a_1\cdots a_k$, a **factorisation tree** groups its factors recursively: the leaves are labelled with $a_1,\dots,a_k$ in order from left to right, and each internal node is labelled with the product of its children's labels. Its **height** is the length of the longest path from the root to a leaf. A factorisation tree is **rank-stable** if every node with at least three children is labelled with a rank-stable matrix.
--
--   The predicate "the product of the list $a_1,\dots,a_k$ has a rank-stable factorisation tree of height at most $h$" is defined recursively:
--
--   1. a single matrix $[a]$ has one, of height $0\le h$;
--   2. if $a_1\cdots a_k$ is cut into $s\ge2$ consecutive nonempty blocks, each of which has a rank-stable factorisation tree of height at most $h$, then $a_1\cdots a_k$ has one of height at most $h+1$ (a root with $s$ children), provided that the root's label $a_1\cdots a_k$ is rank-stable when $s\ge3$.
--
--   These trees are the tool from [11] (Ait El Manssour, Naraghi, Shirmohammadi, Worrell) on which the proof of Theorem 1 rests.
--
--   **Formalization Note** Internal nodes have at least two children; a node with a single child carries its child's label and only adds height, so excluding such nodes loses no tree of a given height bound.
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), §3, p.7 (factorisation trees); p.8 and p.29 (rank-stable condition)

import Mathlib
import Definitions.Def_MatSemiBurnside_IsStableSet
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Rank-stable factorisation tree of height at most h.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), §3, p.7: "Given such a matrix
product a1 · · · ak, a factorisation tree groups its factors recursively. The leaves of the tree are
labelled with the matrices a1 to ak in the exact order from left to right, whereas each internal
node of the tree is labelled by the product of its children's labels. The height of the tree is
the length of the longest path from the root to a leaf." p.8: "in its rank-stable forest
factorisation every node with more than two children is rank-stable"; p.29: "At every node with
at least three children, the matrix labelling the node is rank-stable."

`HasRSTree l h` says the product of the list `l = [a₁, …, a_k]` has a factorisation tree of height
at most `h` in which every node with at least three children is labelled by a rank-stable matrix:
* a single matrix is a leaf (height 0, hence at most any `h`);
* if `l` is the concatenation of `s ≥ 2` consecutive blocks, each of which has such a tree of
  height at most `h`, then `l` has one of height at most `h + 1` (a root with `s` children),
  provided the root's label `l.prod` is rank-stable when `s ≥ 3`.

**Formalization Note.** Internal nodes have at least two children. A node with one child has the
same label as its child and only adds height, so this loses no tree of a given height bound.
Every list with a tree is nonempty. -/
inductive HasRSTree {d : ℕ} : List (Matrix (Fin d) (Fin d) ℚ) → ℕ → Prop
  | leaf (a : Matrix (Fin d) (Fin d) ℚ) (h : ℕ) : HasRSTree [a] h
  | node (ls : List (List (Matrix (Fin d) (Fin d) ℚ))) (h : ℕ) :
      2 ≤ ls.length → (∀ l ∈ ls, HasRSTree l h) →
      (3 ≤ ls.length → IsRankStable ls.flatten.prod) → HasRSTree ls.flatten (h + 1)

end MatSemiBurnside


