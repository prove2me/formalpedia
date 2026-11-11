-- Prove2me | Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Forestwidth
-- name    : SymmetricDepthHierarchy_ConstantDepth_Forestwidth
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:00.255564+00:00
-- url     : https://prove2.me/theorems/532a6c88-5be4-4826-a626-d1f2a5132347
-- title:
--   Rooted tree decompositions and the $\Delta$-forestwidth $\mathrm{fw}_\Delta$
-- statement:
--   A **tree decomposition** of a graph $F$ is a tree $T$ with bags $\beta(t)\subseteq V(F)$ covering $V(F)$ such that each edge has both endpoints in some bag and the bags containing any fixed vertex induce a connected subtree. The depth of a rooted tree counts edges.
--
--   For $\Delta\ge1$, the **$\Delta$-forestwidth** $\mathrm{fw}_\Delta(F)$ is the least $k\ge0$ such that $F$ admits a tree decomposition $(T,\beta)$ with root $r$ such that
--   $$\operatorname{depth}(T)\le\Delta,\qquad \beta(r)=\emptyset,\qquad |\beta(t)|\le k+1\ \text{ for all } t\in V(T).$$
--   Edge multiplicities are ignored.
--
--   It is the width measure matching support size and support depth (Theorem 3.5); the empty root bag distinguishes it from the $\Delta$-treewidth of [Bha+25].
--
--   **Formalization Note.** A rooted tree is given by a root, a parent map and levels with $\mathrm{level}(r)=0$ and $\mathrm{level}(t)=\mathrm{level}(\mathrm{parent}(t))+1$ for $t\ne r$; its edges join each non-root node to its parent, and depth $\le\Delta$ means all levels are $\le\Delta$. $\mathrm{fw}_\Delta$ takes values in $\mathbb N\cup\{\infty\}$, with value $\infty$ only if no decomposition exists (for a finite graph: only when $\Delta=0$ and the graph has a vertex).
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), §2.4, p. 9 (PDF p. 12); Definition 3.3, p. 10 (PDF p. 13)

import Mathlib

open scoped Classical

noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth

/-!
# Rooted tree decompositions and the `Δ`-forestwidth

STOC 2027 submission #1521, §2.4 (tree decompositions, printed p. 9, PDF p. 12) and
Definition 3.3 (printed p. 10, PDF p. 13).

A rooted tree on a finite node type `T` is given by its root, a parent map and a level function
with `level root = 0` and `level t = level (parent t) + 1` for `t ≠ root`; its edges join every
non-root node to its parent, and `level t` is the distance of `t` from the root. The depth of the
tree counts edges, so `depth ≤ Δ` means `level t ≤ Δ` for every node.
-/

/-- A rooted tree on the node type `T`. -/
structure RootedTree (T : Type) where
  root : T
  parent : T → T
  level : T → ℕ
  level_root : level root = 0
  level_parent : ∀ t, t ≠ root → level t = level (parent t) + 1

/-- The tree as a simple graph: each non-root node is adjacent to its parent. -/
def RootedTree.graph {T : Type} (R : RootedTree T) : SimpleGraph T :=
  SimpleGraph.fromRel fun s t => s ≠ R.root ∧ R.parent s = t

/-- A rooted tree decomposition of the graph `G` on `W`: bags `β(t) ⊆ W` covering all vertices,
each edge with both endpoints in some bag, and the nodes whose bag contains any fixed vertex
inducing a connected subtree. -/
structure TreeDecomp {W : Type} (G : SimpleGraph W) (T : Type) extends RootedTree T where
  bag : T → Finset W
  cover_vertex : ∀ v, ∃ t, v ∈ bag t
  cover_edge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t
  connected : ∀ v, (toRootedTree.graph.induce {t | v ∈ bag t}).Connected

/-- `fw_Δ(G) ≤ k`: `G` has a tree decomposition `(T, β)` with root `r` such that `T` has depth
`≤ Δ`, `β(r) = ∅`, and `|β(t)| ≤ k + 1` for all nodes `t`. -/
def FWLe {W : Type} (G : SimpleGraph W) (Δ k : ℕ) : Prop :=
  ∃ (T : Type) (_ : Fintype T) (D : TreeDecomp G T),
    (∀ t, D.level t ≤ Δ) ∧ D.bag D.root = ∅ ∧ ∀ t, (D.bag t).card ≤ k + 1

/-- Definition 3.3: the `Δ`-forestwidth `fw_Δ(G)`, the least `k ≥ 0` with `fw_Δ(G) ≤ k`, as an
extended natural number (`⊤` if there is no such `k`, which for finite `G` happens only when
`Δ = 0` and `G` has a vertex). -/
def forestwidth {W : Type} (Δ : ℕ) (G : SimpleGraph W) : ℕ∞ :=
  sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | FWLe G Δ k})

end SymmetricDepthHierarchy.ConstantDepth


