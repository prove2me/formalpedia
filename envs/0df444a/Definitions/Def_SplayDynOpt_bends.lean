-- Prove2me | Definitions.Def_SplayDynOpt_bends
-- name    : SplayDynOpt_bends
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:56:42.180192+00:00
-- url     : https://prove2.me/theorems/876c48b7-45ee-4b42-a092-9058ba280879
-- title:
--   Heavy edges, bends and heavy-path junctions of the splay tree
-- statement:
--   Let $S$ be a tree on $[n]$ in the **ternary view**: each internal node, one per key, has a left child, a middle child holding its value, and a right child, where an empty left or right subtree is a null node. Let $\operatorname{rk}$ assign a rank to each external position. The subtree of a node covers a consecutive set of external positions.
--
--   An edge $uv$ is **heavy** if the minimum rank in the subtree of $v$ equals the minimum rank in the subtree of $u$, and **light** otherwise. Heavy paths are the connected components left after all light edges are removed.
--
--   A node is a **bend** if it is not the top-most node of its heavy path and either
--
--   1. it is the right child of its parent and the heavy path continues to its left child, or
--   2. it is the left child of its parent and the heavy path continues to its right child.
--
--   A left or right child may be a null node. Write $\operatorname{bends}(\operatorname{rk},S)$ for the set of keys of the bends.
--
--   A **heavy-path junction** between two rank functions $\operatorname{rk},\operatorname{rk}'$ is an internal node whose outgoing heavy edge changes; $\operatorname{junctions}(\operatorname{rk},\operatorname{rk}',S)$ is the set of their keys.
--
--   Bends count the zig-zags, and junctions measure how much a rotation of $T^*$ disturbs the heavy paths.
--
--   **Formalization Note** External positions of $S$ are numbered in symmetric order from $0$, so for a binary search tree on $[n]$ they agree with those of `extRank`. A node is not the top of its heavy path exactly when the edge from its parent is heavy. Heaviness is defined by equal minimum rank, not through a chosen minimizer, and `heavyDirs` records the three outgoing edges; that exactly one is heavy is the content of Lemma 4.
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), §5.2.1, pp.15–17 (heavy edges, bends); §5.2.4, p.22 (junctions); §5, p.14 (ternary view)

import Mathlib

set_option autoImplicit false

namespace SplayDynOpt

open BinaryTree

/-- In the **ternary view** of the splay tree `S`, the subtree rooted at a node of `S` whose
in-order block starts at external position `off` covers the external positions
`off, …, off + 2·numNodes`. `minRank rk off s` is the minimum rank `rk e` over these positions.
The left child of `node a l r` (at offset `off`) has offset `off`, the value node `a` is at
position `off + 2·numNodes l + 1`, and the right child has offset `off + 2·numNodes l + 2`; a nil
child is the single null node at its offset. -/
def minRank (rk : ℕ → ℕ) : ℕ → BinaryTree ℕ → ℕ
  | off, nil => rk off
  | off, node _ l r =>
      min (minRank rk off l) (min (rk (off + 2 * l.numNodes + 1))
        (minRank rk (off + 2 * l.numNodes + 2) r))

/-- Which outgoing edges of the internal node `node a l r` (at offset `off`) are **heavy**: the
edge to a child is heavy iff the minimum rank in the child's subtree equals the minimum rank in
the node's subtree. Components: (left child, middle value node, right child). -/
def heavyDirs (rk : ℕ → ℕ) (off : ℕ) : BinaryTree ℕ → Bool × Bool × Bool
  | nil => (false, false, false)
  | node a l r =>
      let m := minRank rk off (node a l r)
      (decide (minRank rk off l = m), decide (rk (off + 2 * l.numNodes + 1) = m),
        decide (minRank rk (off + 2 * l.numNodes + 2) r = m))

/-- Helper for `bends`: `pos = none` at the root of `S`; `pos = some (isLeft, pm)` at a node that
is the left (`isLeft = true`) or right child of a parent whose subtree has minimum rank `pm`. -/
def bendsAux (rk : ℕ → ℕ) : ℕ → Option (Bool × ℕ) → BinaryTree ℕ → Finset ℕ
  | _, _, nil => ∅
  | off, pos, node a l r =>
      let m := minRank rk off (node a l r)
      let here : Finset ℕ :=
        match pos with
        | none => ∅
        | some (isLeft, pm) =>
            if pm = m ∧
                (if isLeft then minRank rk (off + 2 * l.numNodes + 2) r = m
                 else minRank rk off l = m) then {a} else ∅
      here ∪ bendsAux rk off (some (true, m)) l ∪
        bendsAux rk (off + 2 * l.numNodes + 2) (some (false, m)) r

/-- The **bends** of the splay tree `S` with respect to the rank function `rk` (the ranks are
depths in the nearly optimal tree `T*`, see `extRank`), as the set of keys of the internal nodes
that are bends.

Chmel et al., *Splay trees are almost dynamically optimal*, arXiv:2607.18498 (version of
2026-11-02, sha256 6881e83c…), §5.2.1, p.15: "An edge uv is heavy if the minimum rank in the subtree
of v is the same as the minimum rank in the subtree of u; otherwise, it is light. We define heavy
paths as the connected components that remain after all light edges are removed."; p.17: "A node
is called a bend if it is not the top-most node of the heavy path on which it lies and either it
is the right child of its parent and the heavy path continues to its left child, or it is the left
child of its parent and the heavy path continues to its right child."

**Formalization Note.** External positions of `S` are numbered in symmetric order from `0`
(`minRank`); for a BST `S` on `[n]` they are the positions of `extRank`. A node is not the top of
its heavy path iff the edge from its parent is heavy. "The heavy path continues to its left child"
means the edge to the left child (a null node if the left subtree is empty) is heavy. -/
def bends (rk : ℕ → ℕ) (S : BinaryTree ℕ) : Finset ℕ :=
  bendsAux rk 0 none S

/-- Helper for `junctions`: keys of the nodes of `S` (subtree at offset `off`) whose set of heavy
outgoing edges differs between the rank functions `rk` and `rk'`. -/
def junctionsAux (rk rk' : ℕ → ℕ) : ℕ → BinaryTree ℕ → Finset ℕ
  | _, nil => ∅
  | off, node a l r =>
      (if heavyDirs rk off (node a l r) ≠ heavyDirs rk' off (node a l r) then {a} else ∅) ∪
        junctionsAux rk rk' off l ∪ junctionsAux rk rk' (off + 2 * l.numNodes + 2) r

/-- The **heavy-path junctions** of the splay tree `S` caused by changing the ranks from `rk` to
`rk'`: the internal nodes whose outgoing heavy edge changes.

Chmel et al., §5.2.4, p.22: "We call such an event a heavy path junction. Formally, a junction
occurs at an internal node z whose outgoing heavy edge changes, equivalently, when the minimum-rank
external node in the subtree of z changes from v′ to v". -/
def junctions (rk rk' : ℕ → ℕ) (S : BinaryTree ℕ) : Finset ℕ :=
  junctionsAux rk rk' 0 S

end SplayDynOpt


