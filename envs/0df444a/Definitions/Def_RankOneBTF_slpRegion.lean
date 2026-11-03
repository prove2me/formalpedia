-- Prove2me | Definitions.Def_RankOneBTF_slpRegion
-- name    : RankOneBTF_slpRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:51.996257+00:00
-- url     : https://prove2.me/theorems/985bc84a-0fc7-43f6-a2f9-1409afeb6c7a
-- title:
--   The feasible region of the standard LP (sLP)
-- statement:
--   For an input tensor $\mathcal G$ with $S_0=\{g_{ijk}=0\}$ and $S_1=\{g_{ijk}=1\}$, the **standard LP** is
--   $$
--   \begin{aligned}
--   \min\ & \sum_{(i,j,k)\in S_0} w_{ijk}+\sum_{(i,j,k)\in S_1}(1-w_{ijk})\\
--   \text{s.t. } & w_{ijk}\le x_i,\ w_{ijk}\le y_j,\ w_{ijk}\le z_k && \forall (i,j,k)\in S_1 \quad(6)\\
--   & w_{ijk}\ge 0,\ w_{ijk}\ge x_i+y_j+z_k-2 && \forall (i,j,k)\in S_0 \quad(7)\\
--   & (x,y,z)\in[0,1]^{n+m+l}. && (8)
--   \end{aligned}
--   $$
--   It is obtained from the McCormick (convex hull) relaxation of $w_{ijk}=x_iy_jz_k$ by dropping the constraints that are never active at an optimum, given the signs of the objective coefficients.
--
--   **Formalization Note** The set of points $(x,y,z,\mathcal W)$ satisfying (6)–(8). As on the page, $\mathcal W$ has no box constraint.
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §3, p.6, Problem (sLP), constraints (6)–(8)

import Mathlib
import Definitions.Def_RankOneBTF_lpObjective

namespace RankOneBTF

/-- The feasible region of the **standard LP** (sLP) for the input tensor `G`
(arXiv:2202.07053v3, §3, p.6):
```
w_ijk ≤ x_i, w_ijk ≤ y_j, w_ijk ≤ z_k,   ∀(i,j,k) ∈ S₁        (6)
w_ijk ≥ 0, w_ijk ≥ x_i + y_j + z_k − 2,  ∀(i,j,k) ∈ S₀        (7)
(x, y, z) ∈ [0,1]^{n+m+l}                                     (8)
```
with `S₀ = {g_ijk = 0}`, `S₁ = {g_ijk = 1}`. The LP minimizes `lpObjective G` over this set.

**Formalization Note** As on the page, `W` carries no box constraint: entries in `S₁` are
bounded only above and entries in `S₀` only below. `G i j k = true` means `(i,j,k) ∈ S₁`. -/
def slpRegion {n m l : ℕ} (G : BTensor n m l) : Set (LPPoint n m l) :=
  {pt | (∀ i j k, G i j k = true →
          pt.2.2.2 i j k ≤ pt.1 i ∧ pt.2.2.2 i j k ≤ pt.2.1 j ∧ pt.2.2.2 i j k ≤ pt.2.2.1 k) ∧
        (∀ i j k, G i j k = false →
          0 ≤ pt.2.2.2 i j k ∧ pt.1 i + pt.2.1 j + pt.2.2.1 k - 2 ≤ pt.2.2.2 i j k) ∧
        (∀ i, 0 ≤ pt.1 i ∧ pt.1 i ≤ 1) ∧ (∀ j, 0 ≤ pt.2.1 j ∧ pt.2.1 j ≤ 1) ∧
        (∀ k, 0 ≤ pt.2.2.1 k ∧ pt.2.2.1 k ≤ 1)}

end RankOneBTF


