-- Prove2me | Definitions.Def_CannonFloydParry_Trees
-- name    : CannonFloydParry_Trees
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-09-16T21:06:17.655317+00:00
-- url     : https://prove2.me/theorems/ca385744-4cf7-43e8-a50d-8c3cce36f9e8
-- title:
--   Ordered rooted binary trees and their standard dyadic partitions
-- statement:
--   The tree combinatorics of section 2 of Cannon-Floyd-Parry, on its own. Nothing
--   here mentions Thompson's group $F$, and nothing is imported beyond Mathlib.
--
--   **Trees.** p. 218: “Define an *ordered rooted binary tree* to be a tree $S$ such that i) $S$ has
--   a root $v_0$, ii) if $S$ consists of more than $v_0$, then $v_0$ has valence 2, and iii) if $v$ is
--   a vertex in $S$ with valence greater than 1, then there are exactly two edges $e_{v,L}$, $e_{v,R}$
--   which contain $v$ and are not contained in the geodesic from $v_0$ to $v$.” Here an ordered rooted
--   binary tree is instead an inductive type: a leaf, or a root carrying a left and a right subtree.
--   The source's graph-theoretic conditions say exactly that every non-leaf vertex has two
--   distinguished children, so for finite ordered rooted binary trees the two descriptions pick out
--   the same objects. The source's definition also admits infinite ones, such as the tree
--   $\mathcal{T}$ below, which the source calls an ordered rooted binary tree (p. 219); the inductive
--   type does not. **The inductive type is a reformulation, not the source's definition.** The
--   source's trivial tree, named in its definition of leaves but given no defining sentence of its
--   own, is the leaf.
--
--   p. 219: “There is a *tree of standard dyadic intervals*, $\mathcal{T}$, which is defined as
--   follows. The vertices of $\mathcal{T}$ are the standard dyadic intervals in $[0,1]$. An edge of
--   $\mathcal{T}$ is a pair $(I,J)$ of standard dyadic intervals $I$ and $J$ such that either $I$ is
--   the left half of $J$, in which case $(I,J)$ is a left edge, or $I$ is the right half of $J$, in
--   which case $(I,J)$ is a right edge.” And p. 219: “Define a *$\mathcal{T}$-tree* to be a finite
--   ordered rooted binary subtree of $\mathcal{T}$ with root $[0,1]$.” The type also serves as the
--   source's $\mathcal{T}$-tree. Here the halving is not carried by the type: it is supplied by a
--   function sending a $\mathcal{T}$-tree to the list of breakpoints of the partition of $[0,1]$ its
--   leaves cut out, splitting each interval in half at each node. So $\mathcal{T}$ is never built as
--   a graph.
--
--   p. 220: “It is easy to see that the leaves of a $\mathcal{T}$-tree are the intervals of a standard
--   dyadic partition. Conversely, the intervals of a standard dyadic partition determine finitely
--   many vertices of $\mathcal{T}$, and it is easy to see that these vertices are the leaves of their
--   convex hull, which is a $\mathcal{T}$-tree. Thus there is a canonical bijection between standard
--   dyadic partitions and $\mathcal{T}$-trees.” Since $\mathcal{T}$ is never built as a graph, the
--   first of these sentences becomes something to prove rather than something given.
--
--   Also defined on the type:
--
--   - p. 218: “Vertices with valence 0 (in case of the trivial tree) or 1 in $S$ will be called
--     *leaves* of $S$.” Defined here: the number of leaves.
--   - p. 218: “The *right side* of $S$ is the maximal arc of right edges in $S$ which begins at the
--     root of $S$.” Defined here: the **length of the right side**, counted in edges.
--   - p. 219: “For every nonnegative integer $n$, let $\mathcal{T}_n$ be the $\mathcal{T}$-tree with
--     $n + 1$ leaves whose right side has length $n$.” Defined here: $\mathcal{T}_n$ itself.
--   - p. 220: “Define a *caret* to be an ordered rooted binary subtree of $\mathcal{T}$ with exactly
--     two edges.” Defined here: whether the last two leaves of a $\mathcal{T}$-tree lie in a common
--     caret.
--
--   **Exponents.** p. 222: “Define the *exponents* of a $\mathcal{T}$-tree $S$ as follows. Let
--   $I_0, \dots, I_n$ be the leaves of $S$ in order. For every integer $k$ with $0 \le k \le n$ let
--   $a_k$ be the length of the maximal arc of left edges in $S$ which begins at $I_k$ and which does
--   not reach the right side of $S$. Then $a_k$ is the $k^{\text{th}}$ *exponent* of $S$.” Read
--   structurally that counts the upward run of "is a left child" steps from the $k$th leaf $I_k$,
--   stopped before the first vertex lying on the right side, and it is given here by a recursion on
--   the $\mathcal{T}$-tree. The clause about the right side is not decoration: a leaf may be a left
--   child and still have exponent $0$, when the single left edge above it ends on the right side.
--   The recursion is checked against the source's worked Example 2.4, whose $\mathcal{T}$-tree has
--   exponents $2,1,0,0,1,2,0,0,0,0$; that check is part of this file.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 2 pp. 218-222 (trees, T-trees, carets, exponents)

import Mathlib

/-!
# Ordered rooted binary trees, and the partitions their leaves cut out

Cannon–Floyd–Parry, *Introductory notes on Richard Thompson's groups*,
L'Enseignement Mathématique (2) **42** (1996), 215–256, §2 (pages 218–222).

The tree combinatorics of that section, on its own: the tree type, the standard dyadic
partition its leaves cut out, and the exponents of a tree.  Nothing here mentions Thompson's
group `F`, and nothing here is imported from the rest of the development — this file needs only
Mathlib.  The objects that do involve `F` — tree diagrams, the generators `Xₙ`, the positive
elements — are in the companion file `Def_CannonFloydParry_TreeDiagrams`.

## Two reformulations of the source, stated plainly

**Trees are an inductive type here, where CFP use graphs.**  CFP define an *ordered rooted
binary tree* to be a graph-theoretic tree `S` with a root `v₀` such that `v₀` has valence 2
unless `S` is trivial, and such that every vertex of valence greater than 1 has exactly two
edges not on the geodesic from `v₀`, distinguished as a left and a right edge (p. 218).  Those
conditions say exactly that every non-leaf vertex has exactly two distinguished children, so
the notion is equivalent to the inductive type below, with CFP's trivial tree as `leaf`.
Formalizing the graph version and proving the equivalence would be a large development for no
mathematical gain, so the inductive type is used directly.  **This is a reformulation, not
CFP's definition.**

**A `𝒯`-tree is an element of that type.**  CFP's `𝒯` is the infinite tree whose vertices are
the standard dyadic intervals in `[0,1]` and whose edges join an interval to its two halves; a
*`𝒯`-tree* is a finite ordered rooted binary subtree of `𝒯` with root `[0,1]` (p. 219).  Under
the reformulation above the halving is not part of the tree but is recovered by `marks`, which
sends a tree to the partition of `[0,1]` its leaves cut out.  So `𝒯` is never formalized as a
graph, and the content CFP get for free from the ambient `𝒯` — that the leaves of a `𝒯`-tree
are the intervals of a standard dyadic partition — becomes a theorem of the mission instead.

The type is named `TTree` after CFP's `𝒯`-trees, and to stay clear of Mathlib's own `Tree`.
-/

namespace CannonFloydParry

/-! ### Ordered rooted binary trees -/

/-- An **ordered rooted binary tree**, in CFP's sense (p. 218), as an inductive type: a `leaf`,
or a root carrying a left and a right subtree.  `leaf` is CFP's trivial tree.

Used as their **`𝒯`-tree** (p. 219): the halving structure of the ambient tree `𝒯` of standard
dyadic intervals is supplied by `marks` rather than carried by the type. -/
inductive TTree where
  | leaf : TTree
  | node : TTree → TTree → TTree
  deriving DecidableEq, Repr

namespace TTree

/-- The number of leaves. -/
def leafCount : TTree → ℕ
  | leaf => 1
  | node l r => l.leafCount + r.leafCount

/-- The length of the **right side** — the maximal arc of right edges beginning at the root
(p. 218).  Length is an edge count, so the trivial tree has right side of length `0`. -/
def rightSideLen : TTree → ℕ
  | leaf => 0
  | node _ r => r.rightSideLen + 1

/-- CFP's **`𝒯ₙ`** (p. 219): the tree with `n + 1` leaves whose right side has length `n`. -/
def comb : ℕ → TTree
  | 0 => leaf
  | n + 1 => node leaf (comb n)

/-! ### The standard dyadic partition cut out by the leaves -/

/-- The interior breakpoints of the partition of `[a,b]` cut out by the leaves, in order.

No order between `a` and `b` is assumed, and none is needed to define the list: the recursion
just takes arithmetic means.  It describes a partition only when `a < b`; for `a = b` every
entry equals `a`, and for `a > b` the list decreases.  Only `a = 0`, `b = 1` is ever used. -/
noncomputable def marksAux : TTree → ℝ → ℝ → List ℝ
  | leaf, _, _ => []
  | node l r, a, b =>
      l.marksAux a ((a + b) / 2) ++ ((a + b) / 2) :: r.marksAux ((a + b) / 2) b

/-- The partition of `[0,1]` cut out by the leaves of `t`, as the increasing list of its
breakpoints `x₀ = 0, x₁, …, xₙ = 1`.  The intervals of this partition are the leaves of `t`
in CFP's reading (p. 220). -/
noncomputable def marks (t : TTree) : List ℝ := (0 : ℝ) :: (t.marksAux 0 1 ++ [1])

/-! ### Exponents

CFP define the exponents of a `𝒯`-tree `S` by (p. 222): letting `I₀, …, Iₙ` be the leaves of
`S` in order, the `k`th exponent `aₖ` is *the length of the maximal arc of left edges in `S`
which begins at `Iₖ` and which does not reach the right side of `S`*.

Read structurally, that counts the upward run of "is a left child" steps from the `k`th leaf,
stopped **before** the first vertex lying on the right side of `S`.  The clause about the right
side is not decoration: the leaf before last in `Example 2.4` is a left child, but the single
left edge above it ends on the right side, so its exponent is `0` and not `1`.

Two recursions give this.  `leftRuns` counts the upward run with no such restriction, which is
what applies inside the *left* subtree of a node, since the right side of `node l r` misses `l`
entirely; `exponents` then blocks the step onto the root for leaves of `l` and recurses into `r`,
whose right side is the rest of the right side of `node l r`.  A run reaches the root of a tree
exactly when it starts at the leftmost leaf, which is why only the head is incremented.

`exponents_exampleTree` below checks the result against CFP's worked `Example 2.4`. -/

/-- Increment the first entry of a list, if any. -/
def incrHead : List ℕ → List ℕ
  | [] => []
  | a :: as => (a + 1) :: as

/-- For each leaf in order, the length of the upward run of left edges from it, **not**
restricted by the right side — the count that applies within a left subtree. -/
def leftRuns : TTree → List ℕ
  | leaf => [0]
  | node l r => incrHead l.leftRuns ++ r.leftRuns

/-- The **exponents** of the tree, for each leaf in order (CFP p. 222). -/
def exponents : TTree → List ℕ
  | leaf => [0]
  | node l r => l.leftRuns ++ r.exponents

/-- CFP's `Example 2.4` (pp. 222–223): the tree of their Figure 9, read at 400 dpi. -/
def exampleTree : TTree :=
  node
    (node (node leaf (node leaf leaf)) leaf)
    (node (node leaf (node (node leaf leaf) leaf)) (node leaf leaf))

/-- CFP's `Example 2.4`: the exponents of the tree of their Figure 9 are
`2, 1, 0, 0, 1, 2, 0, 0, 0, 0`.  This pins the reading of the exponent definition, and in
particular of the clause "does not reach the right side". -/
theorem exponents_exampleTree : exampleTree.exponents = [2, 1, 0, 0, 1, 2, 0, 0, 0, 0] := by rfl

/-- CFP's `Example 2.1`/Figure 9 aside: the example tree has ten leaves. -/
theorem leafCount_exampleTree : exampleTree.leafCount = 10 := by rfl

end TTree

/-- Whether the last two leaves of a tree lie in a common caret — that is, whether the tree
ends in a caret both of whose children are leaves.  This is the shape CFP's reduction step
looks for (p. 221). -/
def TTree.endsInCaret : TTree → Bool
  | TTree.leaf => false
  | TTree.node TTree.leaf TTree.leaf => true
  | TTree.node _ TTree.leaf => false
  | TTree.node _ (TTree.node a b) => TTree.endsInCaret (TTree.node a b)
/-- Whether the `k`th and `(k + 1)`th leaves of the tree, counted from `0` in left-to-right
order, are the two children of a common vertex — CFP's "the `n`th and `(n+1)`th leaves are the
vertices of a caret" (p. 221), indexed from `0` rather than from `1`.

Three cases: the pair lies inside the left subtree, or inside the right subtree, or it straddles
the two.  In the straddling case the two leaves are the rightmost leaf of the left subtree and
the leftmost leaf of the right subtree, and they are siblings exactly when both subtrees are
single leaves.  `TTree.endsInCaret` is the special case `k + 2 = leafCount`. -/
def TTree.caretAt : TTree → ℕ → Bool
  | TTree.leaf, _ => false
  | TTree.node l r, k =>
      if k + 1 < l.leafCount then l.caretAt k
      else if l.leafCount ≤ k then r.caretAt (k - l.leafCount)
      else
        match l, r with
        | TTree.leaf, TTree.leaf => true
        | _, _ => false

end CannonFloydParry


