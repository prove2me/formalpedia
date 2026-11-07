-- Prove2me | Definitions.Def_SplayDynOpt_kRibless
-- name    : SplayDynOpt_kRibless
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:56:29.593046+00:00
-- url     : https://prove2.me/theorems/292e6195-e71e-48b7-bb5d-8ea5ce064dd0
-- title:
--   $k$-ribless binary trees
-- statement:
--   A non-root node of a binary tree is a **left-rib node** if it is the left child of its parent, and a **right-rib node** if it is the right child of its parent. A **left rib** is a maximal path consisting only of left-rib nodes, and a **right rib** is defined in the same way. A **spine** is a rib that starts at a child of the root; all other ribs are **proper ribs**. For an integer $k$, a tree is **$k$-ribless** if all its proper ribs have at most $k$ nodes.
--
--   Riblessness says that keys close in symmetric order have similar depths. It is one of the three properties of the normal-form tree.
--
--   **Formalization Note** A maximal left rib starts at a left child whose parent is not a left child, and it is a spine exactly when that parent is the root. So the proper left ribs are the left chains starting at the left child of a non-root right child, and symmetrically for right ribs. `riblessAux` checks exactly these chains. The size of a rib is its number of key nodes; null leaves are not counted.
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), App. C.1, p.61 (ribs, k-ribless); §5.1, p.14 (ribless)

import Mathlib

set_option autoImplicit false

namespace SplayDynOpt

open BinaryTree

/-- The number of nodes on the path from the root of `t` that goes only to left children,
counting the root of `t` (`0` for the empty tree). -/
def leftChain : BinaryTree ℕ → ℕ
  | nil => 0
  | node _ l _ => 1 + leftChain l

/-- The number of nodes on the path from the root of `t` that goes only to right children,
counting the root of `t` (`0` for the empty tree). -/
def rightChain : BinaryTree ℕ → ℕ
  | nil => 0
  | node _ _ r => 1 + rightChain r

/-- Helper for `kRibless`: `pos = none` at the root of the whole tree, `pos = some true` at a
left child and `pos = some false` at a right child. A **proper left rib** starts at the left
child of a non-root right child, a **proper right rib** at the right child of a non-root left
child; each must have at most `k` nodes. -/
def riblessAux (k : ℕ) : Option Bool → BinaryTree ℕ → Prop
  | _, nil => True
  | pos, node _ l r =>
      (pos = some false → leftChain l ≤ k) ∧
      (pos = some true → rightChain r ≤ k) ∧
      riblessAux k (some true) l ∧ riblessAux k (some false) r

/-- A binary tree is **`k`-ribless** if all its proper ribs have at most `k` nodes.

Chmel et al., *Splay trees are almost dynamically optimal*, arXiv:2607.18498 (version of
2026-11-02, sha256 6881e83c…), App. C.1, p.61: "We say that a non-root node of a binary tree is a
left-rib node if it is the left child of its parent. Similarly for right-rib nodes. A left rib is
any maximal path in T consisting of only left-rib nodes. Similarly a right rib. A spine is a rib
that starts at a child of the root of the tree, all other ribs are proper ribs. […] For an integer
k, the tree is k-ribless if all its proper ribs are of size at most k."; §5.1, p.14 ("ribless").

**Formalization Note.** A maximal left rib starts at a left child `c` whose parent `v` is not a
left child; it is a spine iff `v` is the root. So the proper left ribs are exactly the left
chains starting at the left child of a non-root right child, and symmetrically for right ribs.
Size = number of nodes; the null leaves are not nodes. -/
def kRibless (k : ℕ) (t : BinaryTree ℕ) : Prop :=
  riblessAux k none t

end SplayDynOpt


