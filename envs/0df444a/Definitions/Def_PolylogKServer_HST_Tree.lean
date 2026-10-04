-- Prove2me | Definitions.Def_PolylogKServer_HST_Tree
-- name    : PolylogKServer_HST_Tree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:28:21.014454+00:00
-- url     : https://prove2.me/theorems/32ee9f34-d4af-49b9-9ebf-12d9e8fc2e55
-- title:
--   Rooted weighted trees, tree distance on leaves, σ-HSTs and weighted σ-HSTs
-- statement:
--   A **rooted weighted tree** $T$ on a finite set $V$ of nodes consists of a root $r$, a parent map $v\mapsto \mathrm{parent}(v)$ and a depth function with $\mathrm{depth}(r)=0$ and $\mathrm{depth}(\mathrm{parent}(v))+1=\mathrm{depth}(v)$ for every $v\neq r$, together with a length $W(v)>0$ for every non-root node $v$: $W(v)$ is the length of the edge from $v$ to its parent. A node $a$ is an **ancestor** of $v$ (and $v$ lies in the subtree $T(a)$) if $v$ reaches $a$ by repeatedly taking parents; every node is its own ancestor. A **leaf** is a node with no children. The depth of the tree is the largest depth of a leaf.
--
--   The **tree distance** between two nodes $u,v$ is the total length of the edges on the path between them:
--   $$
--   d_T(u,v)=\sum_{x\neq r,\ x \text{ an ancestor of exactly one of } u,v} W(x).
--   $$
--
--   1. $T$ is a **σ-HST** if the edge lengths along every root-to-leaf path form a geometric sequence with ratio $1/\sigma$: there is $L>0$ such that $W(v)=L/\sigma^{\mathrm{depth}(v)-1}$ for every non-root $v$. In particular all edges from a node to its children have the same length, which is $1/\sigma$ times the length of the edge from the node to its parent. Leaves may sit at different depths.
--   2. $T$ is a **weighted σ-HST** if for every node $p$ that is neither the root nor a leaf, the distance from $p$ to its parent is at least $\sigma$ times the distance from $p$ to any of its children: $\sigma\,W(v)\le W(\mathrm{parent}(v))$ whenever $v\neq r$ and $\mathrm{parent}(v)\neq r$.
--   3. A finite metric space $M$ is the **leaf metric** of $T$ through a bijection $e$ between $M$ and the leaves of $T$ if $\mathrm{dist}(x,y)=d_T(e(x),e(y))$ for all $x,y\in M$.
--
--   These are the trees on which the paper runs its k-server algorithms: the input metric is embedded into σ-HSTs, σ-HSTs are flattened into weighted σ-HSTs of logarithmic depth, and the points of the k-server problem are the leaves.
--
--   **Formalization Note** The parent map is total with the convention $\mathrm{parent}(r)=r$; that pseudo-edge is never used, and $W(r)$ is never used. The depth function makes the parent map acyclic. Every σ-HST in this sense is a weighted σ-HST. The k-server metric is not built as a Lean `MetricSpace` instance on the leaves; theorems take an abstract finite metric space with the hypothesis that its distance is the tree distance.
-- source:
--   Bansal, Buchbinder, Mądry, Naor, A Polylogarithmic-Competitive Algorithm for the k-Server Problem, arXiv:1110.1580v1, p. 4 (σ-HSTs, §1.2), p. 6 (weighted σ-HSTs, W(j)), p. 35 (depth, proof of Theorem 8), p. 37 (W(p), w(p) = W(p)/σ)

import Mathlib

/-!
# Rooted weighted trees, σ-HSTs and weighted σ-HSTs

Bansal, Buchbinder, Mądry, Naor, *A Polylogarithmic-Competitive Algorithm for the k-Server
Problem*, arXiv:1110.1580v1, §1.2, p. 4 (σ-HSTs), p. 6 (weighted σ-HSTs, `W(j)`), p. 35
(depth), p. 37 (`W(p)` is the length of the edge from `p` to its parent, `w(p) = W(p)/σ` the
length of the edges from `p` to its children).

A rooted tree on a finite node type `V` is given by a root, a parent map (with the convention
`parent root = root`, an edge that is never used) and a depth function with
`depth root = 0` and `depth (parent v) + 1 = depth v` for `v ≠ root`, which makes the parent
map acyclic: iterating it from `v` reaches the root after `depth v` steps. Every non-root node
`v` carries the length `W v > 0` of the edge from `v` to its parent; the root carries none.
-/

namespace PolylogKServer.HST

/-- A finite rooted tree with positive edge lengths. `W v` is the length of the edge from the
non-root node `v` to its parent (the paper's `W(v)`); the value `W root` is never used. -/
structure WTree (V : Type) [Fintype V] [DecidableEq V] where
  /-- The root. -/
  root : V
  /-- The parent map; `parent root = root` is a convention, not an edge. -/
  parent : V → V
  /-- The depth of a node: the number of edges on its path to the root. -/
  depth : V → ℕ
  parent_root : parent root = root
  depth_root : depth root = 0
  depth_parent : ∀ v, v ≠ root → depth (parent v) + 1 = depth v
  /-- `W v`: the length of the edge from `v` to its parent. -/
  W : V → ℝ
  W_pos : ∀ v, v ≠ root → 0 < W v

variable {V : Type} [Fintype V] [DecidableEq V]

namespace WTree

/-- `T.IsAnc a v`: `a` is an ancestor of `v` (every node is its own ancestor), i.e. `v` lies in
the subtree `T(a)` rooted at `a`. -/
def IsAnc (T : WTree V) (a v : V) : Prop := ∃ i : ℕ, T.parent^[i] v = a

/-- A leaf is a node with no children. (A one-node tree has its root as its only leaf.) -/
def IsLeaf (T : WTree V) (v : V) : Prop := ∀ u, u ≠ T.root → T.parent u ≠ v

noncomputable instance (T : WTree V) : DecidablePred T.IsLeaf := Classical.decPred _

/-- The leaves of `T`, as a subtype of the nodes. These are the points of the k-server metric. -/
abbrev Leaf (T : WTree V) : Type := {v : V // T.IsLeaf v}

/-- The tree distance between two nodes: the total length of the edges on the path between
them. An edge `(v, parent v)` lies on that path exactly when `v` is an ancestor of one of the
two nodes but not of the other. -/
noncomputable def treeDist (T : WTree V) (u v : V) : ℝ := by
  classical
  exact ∑ x ∈ Finset.univ.filter (fun x => x ≠ T.root),
    if (T.IsAnc x u ↔ T.IsAnc x v) then 0 else T.W x

/-- The depth of the tree: the maximal depth of a leaf, i.e. the maximal number of edges on a
root-to-leaf path. -/
noncomputable def height (T : WTree V) : ℕ :=
  (Finset.univ.filter T.IsLeaf).sup T.depth

/-- `T` is a **σ-HST** (p. 4): the edge lengths along every root-to-leaf path form a geometric
sequence with ratio `1/σ`: there is `L > 0` such that every edge from a node at depth `m` to its
children has length `L / σ ^ m`, i.e. `W v = L / σ ^ (depth v - 1)` for every non-root `v`
(`depth v ≥ 1` there). In particular all edges from a node to its children have one common
length, `1/σ` times the length of the edge from the node to its parent. -/
def IsHST (T : WTree V) (σ : ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ ∀ v, v ≠ T.root → T.W v = L / σ ^ (T.depth v - 1)

/-- `T` is a **weighted σ-HST** (p. 6): for every node `p` that is neither the root nor a leaf,
the distance from `p` to its parent is at least `σ` times the distance from `p` to any of its
children. Written over the child `v` of `p = parent v`. -/
def IsWeightedHST (T : WTree V) (σ : ℝ) : Prop :=
  ∀ v, v ≠ T.root → T.parent v ≠ T.root → σ * T.W v ≤ T.W (T.parent v)

/-- The metric space `M` is the leaf metric of `T` through the bijection `e`: the distance of
two points is the tree distance of the corresponding leaves. -/
def IsLeafMetric (T : WTree V) (M : Type) [MetricSpace M] (e : M ≃ T.Leaf) : Prop :=
  ∀ x y : M, dist x y = T.treeDist (e x) (e y)

end WTree

end PolylogKServer.HST


