-- Prove2me | Definitions.Def_DLevelNestedLogit_Pricing_Model
-- name    : DLevelNestedLogit_Pricing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T05:16:52.003176+00:00
-- url     : https://prove2.me/theorems/d2684b3b-3ffb-485e-8586-481e984d7e32
-- title:
--   d-level product tree and parameters of the nested logit price model (leaves: products 1..n at depth d and the no-purchase option 0 under root)
-- statement:
--   The **$d$-level product tree** of the nested logit price model is a finite rooted tree $T=(V,E)$. Its leaves are the $n$ products $l=1,\dots,n$, all at depth $d$, and the **no-purchase option**, node $0$, which is a child of $\mathrm{root}$ (level one). Every other node $j$ is a **nonleaf node**; it has a nonempty set $\mathrm{Children}(j)$ of child nodes, and every node $c\neq\mathrm{root}$ has a parent $\mathrm{Parent}(c)$, which is a nonleaf node one level above $c$. The set $N_j$ of products in the subtree rooted at $j$ is $\{j\}$ for a leaf and the disjoint union of the $N_k$, $k\in\mathrm{Children}(j)$, for a nonleaf node.
--
--   The model's parameters are:
--
--   1. a number $\eta_j$ for each nonleaf node $j$;
--   2. a number $\alpha_0$ for the no-purchase option;
--   3. numbers $\alpha_l$ and $\beta_l$ for each product $l$.
--
--   The **standing assumptions** are
--   $$
--   \beta_l>0\ \ (l=1,\dots,n),\qquad \eta_j\in(0,1]\ \ (j\ \text{nonleaf},\ j\neq\mathrm{root}),\qquad \eta_{\mathrm{root}}=0 .
--   $$
--
--   This is the model on which the preference weights, expected revenues, the stationarity characterization and the push-up-then-push-down pricing algorithm of the mission are defined.
--
--   **Formalization Note** The node type is `Option (Fin n) ⊕ Inner`: `Sum.inl (some l)` is product $l$, indexed by `l : Fin n` (the paper's product $l$ is Lean's `l - 1`), `Sum.inl none` is node $0$, and `Inner` is a finite type of nonleaf nodes containing `root`. The map `parent` is defined on every node and takes values in `Inner`, so leaves have no children; its value at `root` is never used. A level function `level : Inner → ℕ` with `level root = 0`, `level j = level (Parent j) + 1` for `j ≠ root`, `level j < d`, and `level (Parent l) + 1 = d` for every product encodes the $d$ levels and makes the bottom-up and top-down recursions well founded. `exists_child` says every nonleaf node has a child, so the leaves are exactly the $n+1$ nodes `Sum.inl _`. The standing assumptions are the predicate `Params.Standing`; `rank_lt_of_mem_children` is a structural lemma used only for termination.
-- source:
--   Li, Rusmevichientong, Topaloglu, The d-Level Nested Logit Model: Assortment and Price Optimization Problems, Oper. Res. 63(2), 2015, p. 334, §7 (tree, prices); p. 328, §3, (1) (η_j ∈ (0,1], η_root = 0); p. 335 (α_j, β_j > 0)

import Mathlib

namespace DLevelNestedLogit.Pricing

/-- The `d`-level product tree of the price optimization problem (Li, Rusmevichientong,
Topaloglu, Oper. Res. 63(2), 2015, §7, p. 334, reusing §3, pp. 327–328).

The nodes are `Node T = Option (Fin n) ⊕ Inner`:
* `Sum.inl (some l)` is the leaf of product `l` (the paper's products `1, …, n` are
  `l = 0, …, n-1 : Fin n`);
* `Sum.inl none` is the leaf of the no-purchase option (the paper's node `0`);
* `Sum.inr j` for `j : Inner` are the nonleaf nodes, `root` among them.

Every node other than `root` has the parent `parent c`, always a nonleaf node, so leaves have
no children. Levels: `root` is at level `0`, a nonleaf child is one level below its parent,
every nonleaf node is at level `< d`, every product leaf is at depth exactly `d` (its parent is
at level `d - 1`), and the no-purchase leaf is a child of `root` (level one). Every nonleaf node
has at least one child, so the leaves of the tree are exactly the `n + 1` nodes `Sum.inl _`. -/
structure DLevelTree (n d : ℕ) where
  /-- The nonleaf nodes (including `root`). -/
  Inner : Type
  [instFintype : Fintype Inner]
  [instDecEq : DecidableEq Inner]
  /-- The root of the tree. -/
  root : Inner
  /-- `Parent(c)` for every node `c ≠ root`; its value at `Sum.inr root` is never used. -/
  parent : Option (Fin n) ⊕ Inner → Inner
  /-- The level of a nonleaf node. -/
  level : Inner → ℕ
  level_root : level root = 0
  level_parent : ∀ j : Inner, j ≠ root → level j = level (parent (Sum.inr j)) + 1
  level_lt : ∀ j : Inner, level j < d
  /-- Every product leaf is at depth `d`. -/
  level_parent_product : ∀ l : Fin n, level (parent (Sum.inl (some l))) + 1 = d
  /-- The no-purchase option (node `0`) is directly connected to `root`. -/
  parent_noPurchase : parent (Sum.inl none) = root
  /-- Every nonleaf node has a child. -/
  exists_child : ∀ j : Inner, ∃ c : Option (Fin n) ⊕ Inner, c ≠ Sum.inr root ∧ parent c = j

attribute [instance] DLevelTree.instFintype DLevelTree.instDecEq

namespace DLevelTree

variable {n d : ℕ} (T : DLevelTree n d)

/-- The node set `V` of the tree. -/
abbrev Node : Type := Option (Fin n) ⊕ T.Inner

/-- `Children(j)`: the nodes other than `root` whose parent is `j`. -/
def children (j : T.Inner) : Finset T.Node :=
  Finset.univ.filter (fun c => c ≠ Sum.inr T.root ∧ T.parent c = j)

/-- The node of product `l`. -/
abbrev productNode (l : Fin n) : T.Node := Sum.inl (some l)

/-- `Parent(l)` of the product `l`, a nonleaf node. -/
abbrev parentOf (l : Fin n) : T.Inner := T.parent (T.productNode l)

/-- A termination measure: `0` on leaves, `d - level j` on a nonleaf node `j`. -/
def rank : T.Node → ℕ
  | Sum.inl _ => 0
  | Sum.inr j => d - T.level j

/-- A child of a nonleaf node has smaller `rank` (used for the bottom-up recursions). -/
theorem rank_lt_of_mem_children {j : T.Inner} {c : T.Node} (hc : c ∈ T.children j) :
    T.rank c < T.rank (Sum.inr j) := by
  simp only [children, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  obtain ⟨hne, hpar⟩ := hc
  have hj := T.level_lt j
  cases c with
  | inl o => simp only [rank]; omega
  | inr k =>
    have hk : k ≠ T.root := fun h => hne (by rw [h])
    have h1 := T.level_parent k hk
    have h2 := T.level_lt k
    rw [hpar] at h1
    simp only [rank]
    omega

end DLevelTree

/-- The parameters of the `d`-level nested logit price model (p. 335): `η j` for each nonleaf
node `j`, `α₀` for the no-purchase option, and `α l`, `β l` for each product `l`. -/
structure Params {n d : ℕ} (T : DLevelTree n d) where
  η : T.Inner → ℝ
  α₀ : ℝ
  α : Fin n → ℝ
  β : Fin n → ℝ

/-- The standing assumptions of the model: `β l > 0` for every product (p. 335),
`η j ∈ (0, 1]` for every nonleaf node other than `root` (p. 328, (1)), and `η root = 0`
(p. 328). -/
def Params.Standing {n d : ℕ} {T : DLevelTree n d} (P : Params T) : Prop :=
  (∀ l : Fin n, 0 < P.β l) ∧ P.η T.root = 0 ∧
    ∀ j : T.Inner, j ≠ T.root → 0 < P.η j ∧ P.η j ≤ 1

end DLevelNestedLogit.Pricing


