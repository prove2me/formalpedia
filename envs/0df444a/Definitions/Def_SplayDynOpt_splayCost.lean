-- Prove2me | Definitions.Def_SplayDynOpt_splayCost
-- name    : SplayDynOpt_splayCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:57:23.032664+00:00
-- url     : https://prove2.me/theorems/efc3d4df-5860-4868-8623-7b2423ca4358
-- title:
--   Bottom-up splaying and the splay cost of an access sequence
-- statement:
--   **Splaying** a key $x$ moves it to the root by steps that look at the parent $p$ and the grandparent $g$ of $x$, starting at the position of $x$ and working upward:
--
--   1. a **zig-zig**, if $x$ and $p$ are both left children or both right children: rotate $p$, then $x$, so that $g(p(x(a,b),c),d)\mapsto x(a,p(b,g(c,d)))$, or its mirror image;
--   2. a **zig-zag**, if one of them is a left child and the other a right child: rotate $x$ twice, so that $g(p(c,x(a,b)),d)\mapsto x(p(c,a),g(b,d))$, or its mirror image;
--   3. a **zig**, if $p$ is the root: rotate $x$ once.
--
--   The cost of one access is $1$ plus the number of rotations, that is
--   $$
--   1+\#\text{zig}+2\,\#\text{zig-zig}+2\,\#\text{zig-zag}.
--   $$
--   The **splay cost** $\operatorname{splayCost}(S_0,X)$ is the total cost of splaying $x_1,\dots,x_m$ in turn, starting from the tree $S_0$. The totals $\operatorname{zigzigCount}(S_0,X)$ and $\operatorname{zigzagCount}(S_0,X)$ count the zig-zigs and the zig-zags over the same run.
--
--   This is the algorithm whose competitive ratio the mission bounds.
--
--   **Formalization Note** The rotations are paired from $x$ upward, so a zig, if there is one, is the last step, at the root. Pairing from the root downward, as many functional presentations do, is a different algorithm, and the verification file separates the two on a four-node path. Splaying the root returns the tree unchanged with all counts $0$. If $x$ is not a key the tree is returned unchanged with all counts $0$; that case never occurs for $X$ over $[n]$.
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), §2.2, p.5 (splaying, Figure 3); §2.1, p.3 (cost of an access)

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn

set_option autoImplicit false

namespace SplayDynOpt

open BinaryTree

/-- One frame of the path from a node up to the root: the node above has key `key`, the current
subtree is its left child (`isLeft = true`) or right child (`isLeft = false`), and `other` is
the sibling subtree. -/
structure Frame where
  isLeft : Bool
  key : ℕ
  other : BinaryTree ℕ

/-- Rebuild a tree from a subtree and the frames above it (nearest frame first). -/
def plug : BinaryTree ℕ → List Frame → BinaryTree ℕ
  | t, [] => t
  | t, f :: fs => plug (if f.isLeft then node f.key t f.other else node f.key f.other t) fs

/-- Binary search for key `x`: returns the left and right subtrees of the node with key `x`
together with the frames from its parent up to the root (parent first), or `none` if `x` is
not found. `acc` holds the frames collected so far. -/
def focus (x : ℕ) : BinaryTree ℕ → List Frame → Option (BinaryTree ℕ × BinaryTree ℕ × List Frame)
  | nil, _ => none
  | node y l r, acc =>
      if x = y then some (l, r, acc)
      else if x < y then focus x l (⟨true, y, r⟩ :: acc)
      else focus x r (⟨false, y, l⟩ :: acc)

/-- The numbers of zigs, zig-zigs and zig-zags performed by one splay. -/
structure SplayCounts where
  zig : ℕ
  zigzig : ℕ
  zigzag : ℕ
deriving DecidableEq, Repr

instance : Add SplayCounts := ⟨fun a b => ⟨a.zig + b.zig, a.zigzig + b.zigzig, a.zigzag + b.zigzag⟩⟩

/-- **Bottom-up splaying.** The node with key `x` has subtrees `a`, `b`, and `fs` lists the frames
from its parent up to the root. Each step looks at `x`'s parent `p` and grandparent `g` (the first
two frames) and performs, **at x's position**:
* a **zig-zig** if `x` and `p` are both left children or both right children: rotate `p`, then `x`
  (`g (p (x a b) c) d ↦ x a (p b (g c d))` and its mirror image);
* a **zig-zag** if one is a left and the other a right child: rotate `x` twice
  (`g (p c (x a b)) d ↦ x (p c a) (g b d)` and its mirror image);
* a **zig** if `p` is the root: rotate `x` once.
It then continues from the new position of `x`, so the zig (if any) is the last step, at the root.

Chmel et al., *Splay trees are almost dynamically optimal*, arXiv:2607.18498 (version of
2026-11-02, sha256 6881e83c…), §2.2, p.5: "If x and its parent are either both left children or
both right children, then a zig-zig is performed by rotating first the parent of x and then x. […]
If x is a right child and its parent is a left child, or vice versa, a zig-zag is performed by
rotating x twice. […] Right below the root, x might not have a grandparent. In this case a zig is
performed by only rotating x."; Figure 3, p.5.

**Formalization Note.** This is the classical bottom-up splay of Sleator–Tarjan; the rotations
are paired from `x` upward, not from the root downward. -/
def splayUp (x : ℕ) : BinaryTree ℕ → BinaryTree ℕ → List Frame → BinaryTree ℕ × SplayCounts
  | a, b, [] => (node x a b, ⟨0, 0, 0⟩)
  | a, b, [p] =>
      if p.isLeft then (node x a (node p.key b p.other), ⟨1, 0, 0⟩)
      else (node x (node p.key p.other a) b, ⟨1, 0, 0⟩)
  | a, b, p :: g :: fs =>
      let (a', b', c) : BinaryTree ℕ × BinaryTree ℕ × SplayCounts :=
        match p.isLeft, g.isLeft with
        | true, true => (a, node p.key b (node g.key p.other g.other), ⟨0, 1, 0⟩)
        | false, false => (node p.key (node g.key g.other p.other) a, b, ⟨0, 1, 0⟩)
        | false, true => (node p.key p.other a, node g.key b g.other, ⟨0, 0, 1⟩)
        | true, false => (node g.key g.other a, node p.key b p.other, ⟨0, 0, 1⟩)
      let r := splayUp x a' b' fs
      (r.1, c + r.2)

/-- **Splay** key `x` to the root (bottom-up), returning the new tree and the step counts. If `x`
is not a key the tree is returned unchanged with zero counts. -/
def splay (x : ℕ) (t : BinaryTree ℕ) : BinaryTree ℕ × SplayCounts :=
  match focus x t [] with
  | none => (t, ⟨0, 0, 0⟩)
  | some (a, b, fs) => splayUp x a b fs

/-- The cost of one splay access in the BST model: `1` plus the number of rotations, i.e.
`1 + #zig + 2·#zig-zig + 2·#zig-zag` (Chmel et al., §2.1, p.3: "The cost of an access is 1 plus
the number of rotations performed"). -/
def accessCost (c : SplayCounts) : ℕ := 1 + c.zig + 2 * c.zigzig + 2 * c.zigzag

/-- **`cost(T, X)` of the splay tree**: the total cost of serving `X = x₁, …, x_m` by splaying each
`xⱼ` in turn, starting from the tree `S₀`. Chmel et al., Theorem 1, p.13. -/
def splayCost : BinaryTree ℕ → List ℕ → ℕ
  | _, [] => 0
  | S, x :: X => accessCost (splay x S).2 + splayCost (splay x S).1 X

/-- The total number of zig-zigs performed by the splay tree on `X` from `S₀` (Lemma 35, p.47). -/
def zigzigCount : BinaryTree ℕ → List ℕ → ℕ
  | _, [] => 0
  | S, x :: X => (splay x S).2.zigzig + zigzigCount (splay x S).1 X

/-- The total number of zig-zags performed by the splay tree on `X` from `S₀` (Lemma 36, p.48). -/
def zigzagCount : BinaryTree ℕ → List ℕ → ℕ
  | _, [] => 0
  | S, x :: X => (splay x S).2.zigzag + zigzagCount (splay x S).1 X

end SplayDynOpt


