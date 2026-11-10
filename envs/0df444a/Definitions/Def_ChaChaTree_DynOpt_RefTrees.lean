-- Prove2me | Definitions.Def_ChaChaTree_DynOpt_RefTrees
-- name    : ChaChaTree_DynOpt_RefTrees
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:21:12.258695+00:00
-- url     : https://prove2.me/theorems/1a6ec063-f3a4-402c-8b9a-aa4a6d173311
-- title:
--   Reference trees T₁ and T₂, fragments, DepthAlt_{T₁,T₂} (Defs. 16–17) and Wilber's Alt_{T₁}
-- statement:
--   **Primary reference tree.** $T_1$ is the perfect binary search tree of height $H$ with the keys $[N] = [2^H]$ at its leaves (leaf-oriented). Its vertices are pairs $(j, i)$, depth $j \in \{0,\dots,H\}$ and position $i < 2^j$; the depth-$j$ ancestor of key $x$ is $(j, \lfloor (x-1)/2^{H-j} \rfloor)$ (`ancIdx`), and `lcaDepth H x y` is the depth of $\mathrm{lca}(x,y)$.
--
--   **Secondary tree.** $T_2$ is a full binary tree (`FBT`, every internal node has two children) whose leaves, from left to right, are the depths $0,\dots,H-1$; an internal node whose leaves are $a,\dots,b-1$ is the interval $[a,b)$, with children $[a,c)$ and $[c,b)$ (`FBT.internals`).
--
--   **Definition 16–17.** A non-leaf fragment is $q = (v, [a,b))$ with $[a,b)$ an internal node of $T_2$ and $v$ a vertex of $T_1$ at depth $a$. Its active direction is initially UP. On the $t$-th access, if $x_t$ is not in the subtree of $v$ or is the first access to it, nothing changes; otherwise, with $x_{t'}$ the previous access into the subtree and $d = \mathrm{depth}(\mathrm{lca}(x_{t'}, x_t))$, the direction becomes UP if $d \in [a,c)$, DOWN if $d \in [c,b)$, and is unchanged if $d \ge b$. $\mathrm{DepthAlt}_q(X)$ counts the DOWN-to-UP changes and $\mathrm{DepthAlt}_{T_1,T_2}(X) = \sum_{\text{non-leaf } q} \mathrm{DepthAlt}_q(X)$ (`depthAlt H T₂ X`).
--
--   **Wilber's alternation bound.** For every internal vertex $v$ of $T_1$, restrict $X$ to the accesses in the subtree of $v$, label each L or R by the child subtree containing it, and let $a_v(X)$ be the number of changes between consecutive labels; $\mathrm{Alt}_{T_1}(X) = \sum_v a_v(X)$ (`altT1 H X`).
--
--   **General reference trees.** `altBST T X` implements §2.1 for any node-oriented BST: accesses to a vertex itself receive L. `altLeaf T 1 X` implements §2.2 for any full leaf-oriented ordered tree with leaves numbered 1 through its leaf count. Both sum consecutive label changes in each vertex’s subtree; no balance or perfectness condition is imposed. `altT1 H X` retains the perfect-tree encoding used by the depth-alternation and process items.
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), §4.4, pp. 19–20 (PDF 20–21), Definitions 16–17; §2.1, p. 4 (PDF 5); §2.2, p. 6 (PDF 7)

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-! # Reference trees `T₁`, `T₂`, fragments, `DepthAlt_{T₁,T₂}` (Defs. 16–17) and `Alt_{T₁}`

Čech et al., *Dynamic Optimality to within O(log log log n)*, STOC 2027 submission (manuscript,
sha256 9316fbfd…), §4.4, pp. 19–20 (PDF 20–21); §2.1–2.2, pp. 4, 6–7 (PDF 5, 7–8); §5.2, p. 22.

**Primary reference tree `T₁`.** The perfect leaf-oriented binary search tree of height `H` with
the keys `[N] = [2^H]` at its leaves. A vertex is a pair `(j, i)`: depth `j ∈ {0, …, H}` and
position `i ∈ {0, …, 2^j − 1}` from the left; the root is `(0, 0)`, the children of `(j, i)` are
`(j + 1, 2i)` (left) and `(j + 1, 2i + 1)` (right), and key `x` is the leaf `(H, x − 1)`. The
depth-`j` ancestor of key `x` is `(j, ⌊(x − 1)/2^{H − j}⌋)`.

**Secondary tree `T₂`.** A full binary tree (every internal node has two children), `FBT`, whose
leaves, read left to right, are the depths `0, 1, …, H − 1`; the node whose leaves are exactly
`a, …, b − 1` is the interval `[a, b)`. -/

/-- Position of the depth-`j` ancestor of key `x` in the perfect leaf-oriented tree of height `H`
on `[2^H]`: `anc_j(x) = (j, ancIdx H j x)`. -/
def ancIdx (H j x : ℕ) : ℕ := (x - 1) / 2 ^ (H - j)

/-- Depth of `lca(x, y)` in `T₁`: the largest `j ≤ H` at which `x` and `y` have the same
ancestor. -/
def lcaDepth (H x y : ℕ) : ℕ :=
  ((Finset.range (H + 1)).filter fun j => ancIdx H j x = ancIdx H j y).sup id

/-- A full binary tree (every internal node has degree 2); used for `T₂` and `B`. -/
inductive FBT
  | leaf
  | node (l r : FBT)
  deriving DecidableEq, Repr

/-- Number of leaves. -/
def FBT.numLeaves : FBT → ℕ
  | .leaf => 1
  | .node l r => l.numLeaves + r.numLeaves

/-- Height (number of edges on a longest root-to-leaf path; a leaf has height `0`). -/
def FBT.height : FBT → ℕ
  | .leaf => 0
  | .node l r => max l.height r.height + 1

/-- The internal nodes of a full binary tree whose leaves are numbered `a, a + 1, …` from the
left, each as `(a, c, b)`: the node is the interval `[a, b)` and its children are `[a, c)` and
`[c, b)`. -/
def FBT.internals : FBT → ℕ → List (ℕ × ℕ × ℕ)
  | .leaf, _ => []
  | .node l r, a =>
      (a, a + l.numLeaves, a + l.numLeaves + r.numLeaves) ::
        (l.internals a ++ r.internals (a + l.numLeaves))

/-- The direction update of a non-leaf fragment with interval `[a, b)` and children `[a, c)`,
`[c, b)` (Definition 17) for a given `d_lca`: UP (`false`) if `d_lca ∈ [a, c)`, DOWN (`true`) if
`d_lca ∈ [c, b)`, unchanged if `d_lca ≥ b`. (`d_lca ≥ a` always holds there.) -/
def fragmentDir (c b dlca : ℕ) (down : Bool) : Bool :=
  if dlca < c then false else if dlca < b then true else down

/-- The number of DOWN → UP changes of the active direction of a fragment `(v, [a, b))` with
child intervals `[a, c)`, `[c, b)`, along the accesses `Y` into the subtree of `v` (in order),
starting from direction `down`. Each access after the first updates the direction by
`d_lca = depth(lca(x_{t'}, x_t))` with the previous access `x_{t'}` into the subtree. -/
def downUpChanges (H c b : ℕ) : List ℕ → Bool → ℕ
  | x :: y :: rest, down =>
      let down' := fragmentDir c b (lcaDepth H x y) down
      (if down && !down' then 1 else 0) + downUpChanges H c b (y :: rest) down'
  | _, _ => 0

/-- **Definition 17**, one fragment: `DepthAlt_q(X)` for the non-leaf fragment
`q = (v, [a, b))`, `v = (a, i)`, whose interval has children `[a, c)`, `[c, b)` in `T₂`. The
active direction starts at UP. -/
def depthAltFragment (H a c b i : ℕ) (X : List ℕ) : ℕ :=
  downUpChanges H c b (X.filter fun x => ancIdx H a x = i) false

/-- **Definition 17.** The depth alternation bound
`DepthAlt_{T₁,T₂}(X) = Σ_{non-leaf fragments q} DepthAlt_q(X)`, for the perfect leaf-oriented
`T₁` on `[2^H]` and the secondary tree `T₂` (leaves `0, …, H − 1`). A non-leaf fragment is
`q = (v, [a, b))` with `[a, b)` an internal node of `T₂` and `v` any of the `2^a` vertices of
`T₁` at depth `a` (Definition 16). -/
def depthAlt (H : ℕ) (T₂ : FBT) (X : List ℕ) : ℕ :=
  ((T₂.internals 0).map fun f =>
    ∑ i ∈ Finset.range (2 ^ f.1), depthAltFragment H f.1 f.2.1 f.2.2 i X).sum

/-- The number of changes between consecutive labels of a sequence. -/
def labelChanges : List ℕ → ℕ
  | x :: y :: rest => (if x ≠ y then 1 else 0) + labelChanges (y :: rest)
  | _ => 0

/-- **Wilber's alternation bound** `Alt_{T₁}(X) = Σ_v a_v(X)` for the perfect leaf-oriented
reference tree `T₁` on `[2^H]` (§2.1, adapted in §2.2/§5 to keys at the leaves): for each
internal vertex `v = (j, i)` (`j < H`), restrict `X` to the accesses in the subtree of `v`, label
each `L` or `R` according to the child subtree of `v` containing it (`ancIdx H (j+1) x % 2`:
`0` = left, `1` = right), and count the changes between consecutive labels. -/
def altT1 (H : ℕ) (X : List ℕ) : ℕ :=
  ∑ j ∈ Finset.range H, ∑ i ∈ Finset.range (2 ^ j),
    labelChanges ((X.filter fun x => ancIdx H j x = i).map fun x => ancIdx H (j + 1) x % 2)

/-- Wilber's alternation count for an arbitrary node-oriented reference BST (§2.1,
PDF 5). At each vertex, restrict to its subtree and label an access to the vertex
itself or its left subtree L, and an access to its right subtree R. -/
def altBST : BinaryTree ℕ → List ℕ → ℕ
  | .nil, _ => 0
  | .node v l r, X =>
      labelChanges ((X.filter fun x => x ∈ SplayDynOpt.keys (.node v l r)).map
        fun x => if x ≤ v then 0 else 1) + altBST l X + altBST r X

/-- The leaf-oriented version for any full ordered reference tree (§2.2, PDF 7–9).
Leaves are the consecutive keys starting at `a`; the split is between the last
leaf of the left subtree and the first leaf of the right subtree. -/
def altLeaf : FBT → ℕ → List ℕ → ℕ
  | .leaf, _, _ => 0
  | .node l r, a, X =>
      labelChanges ((X.filter fun x => a ≤ x ∧ x < a + l.numLeaves + r.numLeaves).map
        fun x => if x < a + l.numLeaves then 0 else 1) +
        altLeaf l a X + altLeaf r (a + l.numLeaves) X

end ChaChaTree.DynOpt


