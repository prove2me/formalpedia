-- Prove2me | Definitions.Def_SplayDynOpt_IsBSTOn
-- name    : SplayDynOpt_IsBSTOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:56:32.70423+00:00
-- url     : https://prove2.me/theorems/558075d1-cc3e-445b-aaa4-1ff3f348abeb
-- title:
--   Binary search trees on $[n]$, root and depth
-- statement:
--   A **binary tree** is either empty or a node carrying a key, a left subtree and a right subtree. Write $\operatorname{keys}(t)$ for the set of keys of $t$. The tree $t$ has the **ordering property** if, at every node $u$, the key of $u$ is larger than all keys in the left subtree of $u$ and smaller than all keys in the right subtree of $u$; the strict inequalities force the keys to be distinct. A **binary search tree on $[n]$** is a binary tree with the ordering property and
--   $$
--   \operatorname{keys}(t)=\{1,\dots,n\}.
--   $$
--   The **root** of a non-empty tree is the key at its top node. The **depth** of a key $x$ is the number of edges from the root to the node with key $x$, so the root has depth $0$.
--
--   These are the configurations of every dynamic tree in the mission: the splay tree, the optimal tree and the normal-form tree.
--
--   **Formalization Note** Trees are Mathlib's `BinaryTree ℕ`. Taking the keys to be $\{1,\dots,n\}$ is the paper's own convention, without loss of generality because elements are only compared. `depth` searches by comparison, so it is meaningful only for a key of a binary search tree.
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), §2.1, p.3 (BST model)

import Mathlib

set_option autoImplicit false

namespace SplayDynOpt

open BinaryTree

/-- The set of keys stored in a binary tree.

Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký, Tarjan, *Splay trees are almost
dynamically optimal*, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), §2.1, p.3:
"an n-node binary tree where every node has a unique key from U = {1, . . . , n}".

**Formalization Note.** Trees are Mathlib's `BinaryTree ℕ` (`nil | node a l r`; the former name
`Tree` is deprecated in the pinned Mathlib). A key is the label of a `node`. -/
def keys : BinaryTree ℕ → Finset ℕ
  | nil => ∅
  | node a l r => insert a (keys l ∪ keys r)

/-- The **ordering property** at every node: every key of the left subtree is smaller than the
node's key, and every key of the right subtree is larger. Strict inequalities make keys distinct.

Chmel et al., §2.1, p.3: "for any node u, its key is larger than all keys in the left subtree of u
and smaller than all keys in the right subtree of u". -/
def IsBST : BinaryTree ℕ → Prop
  | nil => True
  | node a l r => (∀ b ∈ keys l, b < a) ∧ (∀ b ∈ keys r, a < b) ∧ IsBST l ∧ IsBST r

instance decidableIsBST : DecidablePred IsBST := by
  intro t
  induction t with
  | nil => exact isTrue trivial
  | node a l r hl hr => unfold IsBST; exact instDecidableAnd

/-- A **binary search tree on `[n] = {1, …, n}`**: the ordering property holds and the key set is
exactly `{1, …, n}`. Chmel et al., §2.1, p.3 (BST model), and Theorem 2, p.14 ("a binary search
tree on [n]").

**Formalization Note.** Keys are natural numbers and the key universe is `Finset.Icc 1 n`, which
the paper says is without loss of generality ("elements are only compared"). -/
def IsBSTOn (n : ℕ) (t : BinaryTree ℕ) : Prop :=
  IsBST t ∧ keys t = Finset.Icc 1 n

instance decidableIsBSTOn (n : ℕ) : DecidablePred (IsBSTOn n) := fun _ => instDecidableAnd

/-- The key at the root (`none` for the empty tree). -/
def root : BinaryTree ℕ → Option ℕ
  | nil => none
  | node a _ _ => some a

/-- The **depth** of key `x`: the number of edges on the path from the root to the node with key
`x`, found by binary search. The root has depth `0`.

**Formalization Note.** Only meaningful for `x ∈ keys t` of a BST `t`; for an absent key the value
is the length of the unsuccessful search path (never used). -/
def depth (x : ℕ) : BinaryTree ℕ → ℕ
  | nil => 0
  | node a l r => if x = a then 0 else if x < a then depth x l + 1 else depth x r + 1

end SplayDynOpt


