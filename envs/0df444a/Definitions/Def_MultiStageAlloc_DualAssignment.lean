-- Prove2me | Definitions.Def_MultiStageAlloc_DualAssignment
-- name    : MultiStageAlloc_DualAssignment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:33:00.769206+00:00
-- url     : https://prove2.me/theorems/1f3a1431-1af2-4b25-8d1b-f8e5839cf09d
-- title:
--   The dual assignment in the proof of Theorem 1: $\alpha_i$, $\Delta\beta_{s,j}$, $\beta_j$ and the last-stage dual
-- statement:
--   This is the dual assignment constructed stage by stage in the proof of Theorem 1, for a run $(x,y)$.
--
--   1. **Last stage.** The dual of the last-stage LP has variables $\hat\alpha_i\ge 0$ on $U_K$ and $\hat\beta_j\ge 0$ on $V$ with $\hat\alpha_i+\hat\beta_j\ge w_j$ on $E_K$ and objective $\sum_{i\in U_K}\hat\alpha_i+\sum_j n_j(1-y_j)\hat\beta_j$. A pair is optimal if it minimizes this objective among feasible pairs.
--   2. **Online duals.** $\alpha_i=c^{(l)}_k$ for $i\in U^{(l)}_k$, $k<K$, and $\alpha_i=\hat\alpha_i$ for $i\in U_K$.
--   3. **Offline increments.** For $s<K$ and $j\in V^{(l)}_s$,
--   $$
--   \Delta\beta_{s,j}=\Bigl(\sum_i \frac{x_{s,ij}}{n_j}\Bigr)\bigl(w_j-c^{(l)}_s\bigr),
--   $$
--   and $\Delta\beta_{K,j}=(1-y^{(K-1)}_j)\hat\beta_j$.
--   4. **Offline duals.** $\beta_j=\sum_{s=1}^K\Delta\beta_{s,j}$.
--
--   **Formalization Note** At $n\equiv 1$ this is the printed assignment, whose $y^*_{k,j}$ is $y^{(k-1)}_j$ here.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, proof of Theorem 1, pp.21–22

import Mathlib
import Definitions.Def_MultiStageAlloc_Decomposition

namespace MultiStageAlloc

variable {U V : Type*} [Fintype U] [Fintype V] {K : ℕ}

/-- **Feasibility in the dual of the last-stage LP.** At stage `K`, `F_K = 0` and Algorithm 1 solves
the maximum weight matching LP of `(U_K, V, E_K)` with capacities `n_j (1 - y_j)`,
arXiv:2211.16581v1, pp.21–22. Its dual variables are `α̂ ≥ 0` on `U_K` and `β̂ ≥ 0` on `V`, with
`α̂_i + β̂_j ≥ w_j` on `E_K`. -/
def LastStageDualFeasible (I : Instance U V K) (a : U → ℝ) (b : V → ℝ) : Prop :=
  (∀ i, I.batch i = K → 0 ≤ a i) ∧ (∀ j, 0 ≤ b j) ∧
    ∀ i j, I.edge i j → I.batch i = K → I.w j ≤ a i + b j

/-- **The objective of that dual**: `∑_{i ∈ U_K} α̂_i + ∑_j n_j (1 - y_j) β̂_j`. -/
noncomputable def lastStageDualObj (I : Instance U V K) (y : V → ℝ) (a : U → ℝ) (b : V → ℝ) : ℝ :=
  ∑ i with I.batch i = K, a i + ∑ j, I.cap j * ((1 - y j) * b j)

/-- **`(α̂_K, β̂_K)` is an optimal dual solution of the last-stage LP**, arXiv:2211.16581v1, p.22,
with `y = y*_K = y^(K-1)`. -/
def IsLastStageOptimalDual (I : Instance U V K) (y : V → ℝ) (a : U → ℝ) (b : V → ℝ) : Prop :=
  LastStageDualFeasible I a b ∧
    ∀ a' b', LastStageDualFeasible I a' b' → lastStageDualObj I y a b ≤ lastStageDualObj I y a' b'

/-- **The dual variable `α_i`**, proof of Theorem 1, arXiv:2211.16581v1, pp.21–22: `c^(l)_k` for
`i ∈ U^(l)_k` with `k = batch i < K`, and `α̂_K,i` for `i ∈ U_K`. Only the stage of `i` writes
`α_i`, so the page's stage-by-stage assignment is this single value. -/
noncomputable def dualAlpha (I : Instance U V K) (x : ℕ → U → V → ℝ) (y : ℕ → V → ℝ)
    (a : U → ℝ) (i : U) : ℝ :=
  if I.batch i < K then
    pairPrice I (I.batch i) (y (I.batch i - 1)) (x (I.batch i))
      (onlinePair I (I.batch i) (y (I.batch i - 1)) (x (I.batch i)) i)
  else a i

/-- **The increment `Δβ_s,j`**, proof of Theorem 1, arXiv:2211.16581v1, pp.21–22. For `s < K` and
`j ∈ V^(l)_s` it is `(∑_i x*_s,ij / n_j) (w_j - c^(l)_s)`, and at `s = K` it is
`(1 - y*_K,j) β̂_K,j`, where the page's `y*_{k,j}` is `y^(k-1)_j` here.

**Formalization Note.** At `n_j = 1` this is printed `Δβ`; for general `n_j` the increment is in units
of level, and the dual objective carries the coefficient `n_j`. -/
noncomputable def deltaBeta (I : Instance U V K) (x : ℕ → U → V → ℝ) (y : ℕ → V → ℝ)
    (b : V → ℝ) (s : ℕ) (j : V) : ℝ :=
  if s < K then
    (∑ i, x s i j / I.cap j) *
      (I.w j - pairPrice I s (y (s - 1)) (x s) (offlinePair I s (y (s - 1)) (x s) j))
  else (1 - y (K - 1) j) * b j

/-- **The dual variable `β_j = ∑_{s ∈ [K]} Δβ_s,j`**, proof of Theorem 1, arXiv:2211.16581v1,
pp.21–22. -/
noncomputable def dualBeta (I : Instance U V K) (x : ℕ → U → V → ℝ) (y : ℕ → V → ℝ)
    (b : V → ℝ) (j : V) : ℝ :=
  ∑ s ∈ Finset.Icc 1 K, deltaBeta I x y b s j

end MultiStageAlloc


