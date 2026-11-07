-- Prove2me | Definitions.Def_SplayDynOpt_rotateAt
-- name    : SplayDynOpt_rotateAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:57:28.013554+00:00
-- url     : https://prove2.me/theorems/c75dfc8f-8ab9-4361-b818-c1116a646044
-- title:
--   Rotation of a key with its parent
-- statement:
--   Let $t$ be a binary search tree and $x$ a key that is not the root, with parent $y$. The operation $\operatorname{rotate}(x)$ changes the tree locally around $x$. If $x$ is the left child of $y$, then $y$ becomes the right child of $x$, the former right child of $x$ becomes the new left child of $y$, and $x$ becomes a child of the former parent of $y$:
--   $$
--   y\bigl(x(a,b),\,c\bigr)\ \longmapsto\ x\bigl(a,\,y(b,c)\bigr).
--   $$
--   If $x$ is the right child of $y$, the operation is the mirror image:
--   $$
--   y\bigl(c,\,x(a,b)\bigr)\ \longmapsto\ x\bigl(y(c,a),\,b\bigr).
--   $$
--   A tree $t'$ is obtained from $t$ by **one rotation** if $t'=\operatorname{rotate}(x)(t)$ for some non-root key $x$ of $t$; the rotation has **depth at most $d$** if the depth of $x$ in $t$ is at most $d$.
--
--   Rotations are the only way a tree changes in the BST model, and every model cost in the mission counts them.
--
--   **Formalization Note** The function `rotateAt` returns the tree unchanged if $x$ is the root or absent. Those inputs are excluded by `IsRotationAt`, through which rotations enter every statement. The depth of a rotation is the depth of the rotated key before the rotation.
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), §2.1, p.3 (rotate); Theorem 2, p.15, item 2 (rotation depth)

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn

set_option autoImplicit false

namespace SplayDynOpt

open BinaryTree

/-- **Rotation of the node with key `x`** with its parent, located by binary search.

Chmel et al., *Splay trees are almost dynamically optimal*, arXiv:2607.18498 (version of
2026-11-02, sha256 6881e83c…), §2.1, p.3: "rotate(x). Change the tree locally around x. If x is the
left child of y, y now becomes the right child of x, the formerly right child of x becomes the new
left child of y, and x becomes a child of y's parent. The case where x is the right child is
analogous."

If `x` is the left child of `y` (subtree `y (x a b) c`), the result is `x a (y b c)`; if `x` is the
right child of `y` (subtree `y c (x a b)`), the result is `x (y c a) b`. The rest of the tree is
unchanged.

**Formalization Note.** If `x` is the root or not a key, the function returns the tree unchanged;
these inputs are excluded by `IsRotationAt`, which is how rotations enter every statement. -/
def rotateAt (x : ℕ) : BinaryTree ℕ → BinaryTree ℕ
  | nil => nil
  | node y l r =>
      if x < y then
        match l with
        | node z a b => if z = x then node x a (node y b r) else node y (rotateAt x (node z a b)) r
        | nil => node y nil r
      else if y < x then
        match r with
        | node z a b => if z = x then node x (node y l a) b else node y l (rotateAt x (node z a b))
        | nil => node y l nil
      else node y l r

/-- `t'` is obtained from `t` by **one rotation of the non-root key `x`** (`x ∈ keys t`,
`x` is not the root). The depth of this rotation is `depth x t`, the depth of `x` before it. -/
def IsRotationAt (x : ℕ) (t t' : BinaryTree ℕ) : Prop :=
  x ∈ keys t ∧ root t ≠ some x ∧ t' = rotateAt x t

/-- `t'` is obtained from `t` by a single rotation (at any depth). -/
def IsRotation (t t' : BinaryTree ℕ) : Prop :=
  ∃ x, IsRotationAt x t t'

/-- `t'` is obtained from `t` by a single rotation of a key of depth at most `d` in `t`
(Chmel et al., Theorem 2, p.15, item 2: "a single rotation at depth at most O(1)"). -/
def IsRotationWithin (d : ℕ) (t t' : BinaryTree ℕ) : Prop :=
  ∃ x, IsRotationAt x t t' ∧ depth x t ≤ d

end SplayDynOpt


