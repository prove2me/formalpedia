-- Prove2me | Definitions.Def_SampleRemoval_Supplement_minPlus
-- name    : SampleRemoval_Supplement_minPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:14:45.397929+00:00
-- url     : https://prove2.me/theorems/f6374dd8-326a-452d-bf0a-005883ec8390
-- title:
--   Min-plus convolution $\Lambda(K)$ of group deletion curves
-- statement:
--   For a total deletion count $K$, the **min-plus convolution** is
--
--   $$\Lambda(K)=\min\left\{\sum_g f_g(k_g):\sum_gk_g=K,\ 0\le k_g\le n_g\right\}.$$
--
--   Thus $\Lambda(K)$ is the least total within-group cross-scatter obtainable with exactly $K$ deletions distributed across the groups.
--
--   **Formalization Note** The infimum is used for $K\le n$, when the finite allocation family is nonempty.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Section 4, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_SampleRemoval_Supplement_totalObs
import Definitions.Def_SampleRemoval_Supplement_deletionCurve

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- The min-plus convolution `Λ(K)` of the group deletion curves: the minimum total cross-scatter
over allocations of exactly `K` deletions (Xu, Gao, Hu, STOC 2027 submission, §4, p.7
(PDF p.9)). Statements use `K≤n`, for which the allocation family is finite and nonempty. -/
noncomputable def minPlus {Γ : ℕ} (M : FixedEffectsModel Γ) (K : ℕ) : ℝ :=
  sInf {z : ℝ | ∃ k : Fin Γ → ℕ, (∀ g, k g ≤ M.nobs g) ∧
    ∑ g, k g = K ∧ z = ∑ g, deletionCurve M g (k g)}

end SampleRemoval.Supplement


