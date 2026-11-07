-- Prove2me | Definitions.Def_TreeCoverLB_WeightedTree
-- name    : TreeCoverLB_WeightedTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:12.871545+00:00
-- url     : https://prove2.me/theorems/1f4d549f-de80-4d5d-852a-9469034a46d2
-- title:
--   Edge-weighted tree on the vertex set $X$ and its tree distance $d_T$
-- statement:
--   An **edge-weighted tree on the vertex set $X$** is a tree $T$ (a connected acyclic simple graph) whose vertex set is exactly $X$ (no Steiner vertices), together with edge weights $w_T(e)\ge 0$ for every edge $e$ of $T$.
--
--   The **tree distance** $d_T(x,y)$ is the length of the unique $x$–$y$ path $P=(v_0,\dots,v_t)$ in $T$:
--   $$
--   d_T(x,y)=\operatorname{len}(P)=\sum_{i=1}^{t} w_T(\{v_{i-1},v_i\}).
--   $$
--
--   **Formalization Note** The weight function is total on unordered pairs; only its values on edges of the tree are used, and weight $0$ is allowed as in the paper's $w_G : E(G)\to\mathbb R_{\ge 0}$. The path sum is the published `KServer.walkWeight`.
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), §1, p.1 (PDF p.3) (trees on vertex set X); §3, p.8 (PDF p.10) (w_G : E(G) → ℝ_{≥0} and len(P))

import Mathlib
import Definitions.Def_KServer_tree_metric

namespace TreeCoverLB

/-- An **edge-weighted tree on the vertex set `X`** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §1, p.1 (PDF p.3): "k edge-weighted
trees T_1, …, T_k on vertex set X"; §3, p.8 (PDF p.10): "w_G : E(G) → ℝ_{≥0}").

A tree is a simple graph `G` on `X` itself (no Steiner vertices) that is a tree (connected and
acyclic), together with edge weights `w`, nonnegative on the edges of `G`.

**Formalization Note** The weight function is total on `Sym2 X`; only its values on the edges of
`G` are ever used (`WeightedTree.dist`). Weight `0` is allowed, as in the paper's
`w_G : E(G) → ℝ_{≥0}`. -/
structure WeightedTree (X : Type*) where
  /-- the underlying simple graph on `X` -/
  G : SimpleGraph X
  /-- `G` is a tree -/
  isTree : G.IsTree
  /-- the edge weights -/
  w : Sym2 X → ℝ
  /-- every edge has nonnegative weight -/
  w_nonneg : ∀ e ∈ G.edgeSet, 0 ≤ w e

namespace WeightedTree

variable {X : Type*}

/-- The unique path from `x` to `y` in the tree. -/
noncomputable def path (T : WeightedTree X) (x y : X) : T.G.Walk x y :=
  (T.isTree.existsUnique_path x y).exists.choose

/-- The **tree distance** `d_T(x, y)`: the length `len(P) = Σ w({v_{i−1}, v_i})` of the unique
`x`–`y` path `P` in the tree (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §3, p.8 (PDF p.10), the definition of `len(P)`).
The sum over the darts of the path is `KServer.walkWeight`. -/
noncomputable def dist (T : WeightedTree X) (x y : X) : ℝ :=
  KServer.walkWeight (fun u v => T.w s(u, v)) (T.path x y)

end WeightedTree

end TreeCoverLB


