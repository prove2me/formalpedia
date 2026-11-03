-- Prove2me | Definitions.Def_RankOneBTF_flpRegion
-- name    : RankOneBTF_flpRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:56.754682+00:00
-- url     : https://prove2.me/theorems/9744e6c0-2e92-47c5-b9db-4446be7aca40
-- title:
--   The flower LP (fLP) and its recovery of the ground truth
-- statement:
--   For an input tensor $\mathcal G$ with $S_0=\{g_{ijk}=0\}$ and $S_1=\{g_{ijk}=1\}$, the **flower LP** is
--   $$
--   \begin{aligned}
--   \min\ & \sum_{(i,j,k)\in S_0} w_{ijk}+\sum_{(i,j,k)\in S_1}(1-w_{ijk})\\
--   \text{s.t. } & w_{ijk}\le x_i,\ w_{ijk}\le y_j,\ w_{ijk}\le z_k && \forall (i,j,k)\in S_1 \quad(13)\\
--   & w_{ijk}\ge 0,\ w_{ijk}\ge x_i+y_j+z_k-2 && \forall (i,j,k)\in S_0 \quad(14)\\
--   & w_{i'jk}-w_{ijk}\le 1-x_i && \forall (i,j,k)\in S_0,\ (i',j,k)\in S_1 \quad(15)\\
--   & w_{ij'k}-w_{ijk}\le 1-y_j && \forall (i,j,k)\in S_0,\ (i,j',k)\in S_1 \quad(16)\\
--   & w_{ijk'}-w_{ijk}\le 1-z_k && \forall (i,j,k)\in S_0,\ (i,j,k')\in S_1 \quad(17)\\
--   & (x,y,z)\in[0,1]^{n+m+l}.
--   \end{aligned}
--   $$
--   The flower inequalities (15)–(17) strengthen the standard LP. **(fLP) recovers the ground truth** for $\mathcal G$ when $(\bar x,\bar y,\bar z,\bar{\mathcal W})$ is its unique optimal solution.
--
--   This is the LP of the mission's goal theorem.
--
--   **Formalization Note** `flpRegion G` is the set of points satisfying (13)–(17) and the box on $(x,y,z)$; as on the page, $\mathcal W$ has no box constraint. `FLPRecovers G x̄ ȳ z̄` states that the ground truth point is the unique optimal solution of (fLP) for $\mathcal G$.
-- source:
--   Del Pia, Khajavirad, Rank-one Boolean tensor factorization and the multilinear polytope, arXiv:2202.07053v3, §3, p.8, Problem (fLP), constraints (13)–(17); p.3 (recovery)

import Mathlib
import Definitions.Def_RankOneBTF_lpObjective

namespace RankOneBTF

/-- The feasible region of the **flower LP** (fLP) for the input tensor `G`
(arXiv:2202.07053v3, §3, p.8):
```
w_ijk ≤ x_i, w_ijk ≤ y_j, w_ijk ≤ z_k,   ∀(i,j,k) ∈ S₁                    (13)
w_ijk ≥ 0, w_ijk ≥ x_i + y_j + z_k − 2,  ∀(i,j,k) ∈ S₀                    (14)
w_i'jk − w_ijk ≤ 1 − x_i,  ∀(i,j,k) ∈ S₀, (i',j,k) ∈ S₁                   (15)
w_ij'k − w_ijk ≤ 1 − y_j,  ∀(i,j,k) ∈ S₀, (i,j',k) ∈ S₁                   (16)
w_ijk' − w_ijk ≤ 1 − z_k,  ∀(i,j,k) ∈ S₀, (i,j,k') ∈ S₁                   (17)
(x, y, z) ∈ [0,1]^{n+m+l}
```
with `S₀ = {g_ijk = 0}`, `S₁ = {g_ijk = 1}`. The LP minimizes `lpObjective G` over this set.

**Formalization Note** As on the page, `W` carries no box constraint. `G i j k = true` means
`(i,j,k) ∈ S₁`. -/
def flpRegion {n m l : ℕ} (G : BTensor n m l) : Set (LPPoint n m l) :=
  {pt | (∀ i j k, G i j k = true →
          pt.2.2.2 i j k ≤ pt.1 i ∧ pt.2.2.2 i j k ≤ pt.2.1 j ∧ pt.2.2.2 i j k ≤ pt.2.2.1 k) ∧
        (∀ i j k, G i j k = false →
          0 ≤ pt.2.2.2 i j k ∧ pt.1 i + pt.2.1 j + pt.2.2.1 k - 2 ≤ pt.2.2.2 i j k) ∧
        (∀ i i' j k, G i j k = false → G i' j k = true →
          pt.2.2.2 i' j k - pt.2.2.2 i j k ≤ 1 - pt.1 i) ∧
        (∀ i j j' k, G i j k = false → G i j' k = true →
          pt.2.2.2 i j' k - pt.2.2.2 i j k ≤ 1 - pt.2.1 j) ∧
        (∀ i j k k', G i j k = false → G i j k' = true →
          pt.2.2.2 i j k' - pt.2.2.2 i j k ≤ 1 - pt.2.2.1 k) ∧
        (∀ i, 0 ≤ pt.1 i ∧ pt.1 i ≤ 1) ∧ (∀ j, 0 ≤ pt.2.1 j ∧ pt.2.1 j ≤ 1) ∧
        (∀ k, 0 ≤ pt.2.2.1 k ∧ pt.2.2.1 k ≤ 1)}

/-- **Problem (fLP) recovers the ground truth** for the input tensor `G`
(arXiv:2202.07053v3, §1, p.3: "the optimization problem has a unique optimal solution and it
corresponds to the ground truth rank-one tensor"): the ground truth point `(x̄, ȳ, z̄, W̄)` is
the unique optimal solution of (fLP) built from `G`. -/
def FLPRecovers {n m l : ℕ} (G : BTensor n m l) (xb : Fin n → Bool) (yb : Fin m → Bool)
    (zb : Fin l → Bool) : Prop :=
  IsUniqueOptimalOn (flpRegion G) (lpObjective G) (groundPoint xb yb zb)

end RankOneBTF


