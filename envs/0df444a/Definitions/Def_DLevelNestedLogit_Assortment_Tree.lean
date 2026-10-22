-- Prove2me | Definitions.Def_DLevelNestedLogit_Assortment_Tree
-- name    : DLevelNestedLogit_Assortment_Tree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T04:22:21.095785+00:00
-- url     : https://prove2.me/theorems/862a4224-5da1-40a4-9f19-f094de69b4f8
-- title:
--   d-level product tree: leaves are the products 1..n (at depth d) and the no-purchase option 0 (at level one); Children(j) and N_j
-- statement:
--   The **product taxonomy** of the $d$-level nested logit model. There are $n$ products $1,\dots,n$ and a no-purchase option, product $0$. They are the leaves of a finite rooted tree $T=(V,E)$: every node $j\neq\mathrm{root}$ has a parent $\mathrm{Parent}(j)$ and lies one level below it, and $\mathrm{root}$ is at level $0$. The tree has $d$ levels: every node has level at most $d$, the product leaves $1,\dots,n$ are at level exactly $d$, and the no-purchase leaf $0$ is a child of $\mathrm{root}$ (level one). The leaves of the tree, the nodes without children, are exactly the $n+1$ product nodes.
--
--   For a node $j$, $\mathrm{Children}(j)$ is the set of nodes whose parent is $j$, and $N_j\subseteq\{0,1,\dots,n\}$ is the set of products in the subtree rooted at $j$:
--   $$N_j=\{j\}\ \text{if $j$ is a leaf},\qquad N_j=\bigcup_{k\in\mathrm{Children}(j)}N_k\ \text{otherwise}.$$
--
--   **Formalization Note.** `ProductTree n` bundles a `Fintype` node type `Node`, `root`, `parent` (with `parent root = root`, never used as a real parent), a level function `depth` with `depth j = depth (parent j) + 1` for `j ≠ root`, the number of levels `d`, and an injective map `leaf : Fin (n + 1) → Node` (`leaf 0` is the no-purchase option). `children j` excludes `root`. `IsLeaf j` means `j = leaf i` for some `i`, and `leafIndex` recovers `i`. `N j : Finset (Fin (n + 1))` is defined by the recursion above, which terminates because children are one level deeper and levels are at most `d`; the two small lemmas in the file are the termination measures.
-- source:
--   Li, Rusmevichientong, Topaloglu, The d-Level Nested Logit Model: Assortment and Price Optimization Problems, Oper. Res. 63(2), 2015, pp. 327–328, §3

import Mathlib

namespace DLevelNestedLogit.Assortment

/-- The product taxonomy of the d-level nested logit model (Li, Rusmevichientong, Topaloglu,
Oper. Res. 63(2), 2015, §3, pp. 327–328).

There are `n` products `1, …, n` and the no-purchase option `0`; they are the leaves
`leaf 0, leaf 1, …, leaf n` of a finite rooted tree with node type `Node`. Every node other
than `root` has the parent `parent j` and sits one level below it; `root` is at depth `0`.
The tree has `d` levels: every node has depth at most `d`, the product leaves `1, …, n` are at
depth exactly `d`, and the no-purchase leaf `0` is a child of `root` (level one). The leaves
of the tree (the nodes without children) are exactly the nodes `leaf i`. -/
structure ProductTree (n : ℕ) where
  /-- The vertex set `V`. -/
  Node : Type
  [instFintype : Fintype Node]
  [instDecEq : DecidableEq Node]
  /-- The root of the tree. -/
  root : Node
  /-- `Parent(j)`; its value at `root` is `root` itself and is never used as a real parent. -/
  parent : Node → Node
  /-- The level of a node: `root` is at level `0`. -/
  depth : Node → ℕ
  /-- The number of levels `d`. -/
  d : ℕ
  /-- `leaf i` is the leaf node of product `i`; `leaf 0` is the no-purchase option. -/
  leaf : Fin (n + 1) → Node
  parent_root : parent root = root
  depth_root : depth root = 0
  depth_parent : ∀ j, j ≠ root → depth j = depth (parent j) + 1
  depth_le : ∀ j, depth j ≤ d
  leaf_injective : Function.Injective leaf
  leaf_ne_root : ∀ i, leaf i ≠ root
  /-- A leaf has no children. -/
  leaf_no_child : ∀ i k, k ≠ root → parent k ≠ leaf i
  /-- A node that is not a leaf has at least one child. -/
  nonleaf_has_child : ∀ j, (∀ i, leaf i ≠ j) → ∃ k, k ≠ root ∧ parent k = j
  /-- The products `1, …, n` are the leaves at depth `d`. -/
  depth_product : ∀ i : Fin (n + 1), i ≠ 0 → depth (leaf i) = d
  /-- The no-purchase option, node `0`, is in level one, directly connected to `root`. -/
  parent_leaf_zero : parent (leaf 0) = root

attribute [instance] ProductTree.instFintype ProductTree.instDecEq

namespace ProductTree

variable {n : ℕ} (T : ProductTree n)

/-- `Children(j)`: the nodes other than `root` whose parent is `j`. -/
def children (j : T.Node) : Finset T.Node :=
  Finset.univ.filter (fun k => k ≠ T.root ∧ T.parent k = j)

/-- `j` is a leaf node, i.e. `j = leaf i` for some `i ∈ {0, 1, …, n}`. -/
def IsLeaf (j : T.Node) : Prop := ∃ i, T.leaf i = j

instance (j : T.Node) : Decidable (T.IsLeaf j) := by
  unfold IsLeaf; infer_instance

/-- The product index `i` of a leaf node `j = leaf i`. -/
noncomputable def leafIndex (j : T.Node) (h : T.IsLeaf j) : Fin (n + 1) := Classical.choose h

theorem depth_lt_of_mem_children {j k : T.Node} (hk : k ∈ T.children j) :
    T.d - T.depth k < T.d - T.depth j := by
  simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  have h1 := T.depth_parent k hk.1
  have h2 := T.depth_le k
  rw [hk.2] at h1
  omega

theorem depth_parent_lt {j : T.Node} (hj : j ≠ T.root) : T.depth (T.parent j) < T.depth j := by
  have := T.depth_parent j hj
  omega

/-- `N_j`: the set of products (leaf nodes, including `0` when it lies below `j`) in the
subtree rooted at `j` — `{i}` at a leaf `leaf i`, and the union of the children's sets at a
nonleaf node (p. 328). -/
noncomputable def N (j : T.Node) : Finset (Fin (n + 1)) :=
  if h : T.IsLeaf j then {T.leafIndex j h}
  else (T.children j).attach.biUnion (fun k => N k.1)
termination_by T.d - T.depth j
decreasing_by exact T.depth_lt_of_mem_children k.2

end ProductTree

end DLevelNestedLogit.Assortment


