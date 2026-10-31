-- Prove2me | Definitions.Def_MWMSLagrange_Instance_CostBound
-- name    : MWMSLagrange_Instance_CostBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:45.180256+00:00
-- url     : https://prove2.me/theorems/ae7730f5-42a2-4e90-91d9-1410f71609df
-- title:
--   Cost primitives bounded by $B$
-- statement:
--   An MWMS instance has **costs bounded by** $B$ when
--
--   $$h_i\le B,\qquad b_i\le B,\qquad c_{i,j}\le B\ (j\in\mathcal M_i),\qquad |w_j|\le B .$$
--
--   Theorem 2's $O(\cdot)$ holds the cost primitives fixed while $M$, $N$ and $T$ grow; this condition is the quantitative form of "fixed". The constant of the bound may depend on $B$ and on the demand bound $\bar D$.
--
--   **Formalization Note** The paper's own constant depends on $\bar b=\max_i b_i$ and $\bar D$ only; that is false (see the goal theorem), which is why $B$ also bounds $c$ and $|w|$.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), Theorem 2, p.13; constant of the proof, p.25

import Mathlib
import Definitions.Def_MWMSLagrange_Instance

namespace MWMSLagrange

/-- Miao, Jasin, Chao, SSRN 3552995 (manuscript, sha256 1146a7f8…), Theorem 2, p.13: the cost
primitives that the `O(·)` of Theorem 2 treats as fixed are bounded by `B`:
`h_i ≤ B`, `b_i ≤ B`, `c_{i,j} ≤ B` for `j ∈ 𝓜_i`, and `|w_j| ≤ B`.

**Formalization Note.** The page's `O(√(min{M,N} T N log(TN)))` is read as a bound
`K · √(…)` whose constant `K` may depend on the demand bound `D̄` and on `B`, but not on
`M, N, T`, the network, the inventories or the demand laws. The paper's own proof (p.25) has a
constant in `b̄ = max_i b_i` and `D̄` only; that is false (see the goal `theorem_2`), which is
why the bound also covers `c` and `w`. -/
def Instance.CostBound {M N : ℕ} (I : Instance M N) (B : ℝ) : Prop :=
  (∀ i, I.h i ≤ B) ∧ (∀ i, I.b i ≤ B) ∧ (∀ i j, I.adj i j = true → I.c i j ≤ B) ∧
    (∀ j, |I.w j| ≤ B)

end MWMSLagrange


