-- Prove2me | Definitions.Def_TreeCoverLB_IsTreeCover
-- name    : TreeCoverLB_IsTreeCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:23:22.443535+00:00
-- url     : https://prove2.me/theorems/91c5329b-8891-4329-9cc7-8f003dd5a9e1
-- title:
--   $(\alpha,k)$-tree cover of a metric
-- statement:
--   Let $(X,d)$ be a finite metric space and $T_1,\dots,T_k$ edge-weighted trees on the vertex set $X$. They form an **$(\alpha,k)$-tree cover** if for every $x,y\in X$:
--
--   1. every tree dominates: $d_{T_i}(x,y)\ge d(x,y)$ for every $i\in[k]$;
--   2. some tree approximates the pair: $d_{T_i}(x,y)\le \alpha\, d(x,y)$ for some $i\in[k]$.
--
--   The parameters $k$ and $\alpha$ are the **size** and **distortion** of the cover.
--
--   **Formalization Note** The trees are indexed by $\{0,\dots,k-1\}$ (repetitions allowed, so "at most $k$" trees is the same notion). "Every size-$k$ tree cover has distortion at least $B$" is written in the theorems as: whenever $(T,\alpha)$ is a tree cover, $B\le\alpha$.
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), §1, p.1 (PDF p.3), the definition of an (α, k)-tree cover

import Mathlib
import Definitions.Def_TreeCoverLB_WeightedTree

namespace TreeCoverLB

/-- **`(α, k)`-tree cover** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §1, p.1 (PDF p.3)): the `k` edge-weighted trees
`T 0, …, T (k−1)` on the vertex set `X` form an `(α, k)`-tree cover of the metric `d` if, for every
`x, y ∈ X`,
* every tree dominates: `d_{T_i}(x, y) ≥ d(x, y)` for every `i`; and
* some tree `α`-approximates the pair: `d_{T_i}(x, y) ≤ α · d(x, y)` for some `i`.

`k` is the size and `α` the distortion of the cover.

**Formalization Note** "Every size-`k` tree cover has distortion at least `B`" is expressed in the
theorems as `∀ T α, IsTreeCover d T α → B ≤ α`, with no infimum. -/
def IsTreeCover {X : Type*} {k : ℕ} (d : X → X → ℝ) (T : Fin k → WeightedTree X) (α : ℝ) :
    Prop :=
  (∀ i x y, d x y ≤ (T i).dist x y) ∧ (∀ x y, ∃ i, (T i).dist x y ≤ α * d x y)

end TreeCoverLB


