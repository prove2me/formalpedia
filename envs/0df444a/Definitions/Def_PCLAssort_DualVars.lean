-- Prove2me | Definitions.Def_PCLAssort_DualVars
-- name    : PCLAssort_DualVars
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:33.483994+00:00
-- url     : https://prove2.me/theorems/6209d647-6b24-416f-b28d-a26ecad959ef
-- title:
--   Variables of the LP (D)
-- statement:
--   The LP (D) has variables $\alpha_{ij},\beta_{ij}$ for the edges $(i,j)\in E$ (dual to $y_{ij}\le x_i$ and $y_{ij}\le 1-x_j$), $\gamma_i$ for $i\in[n]$ (dual to $x_i\le1$), $\delta$ (dual to the knapsack constraint), and the free variable $z$.
--
--   **Formalization Note** The field for $\gamma_i$ is named `γd`, to avoid a clash with the dissimilarity parameters $\gamma_{ij}$.
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), §4.2, (D), p.793 (PDF p.9)

import Mathlib

namespace PCLAssort

/-- The variables of the LP (D) (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, §4.2, p.793): `α_ij`, `β_ij` for the edges `(i, j) ∈ E`,
`γ_i` for `i ∈ [n]`, `δ`, and the free variable `z`.

**Formalization Note.** The dual variable the page calls `γ_i` is the field `γd`, to avoid a clash
with the dissimilarity parameters `γ_ij`. `α` and `β` are indexed by all ordered pairs of vertices
of `G_z`; only their values on `E` enter (D). -/
structure DualVars (n : ℕ) where
  /-- `α_ij`, dual to `y_ij ≤ x_i` -/
  α : Option (Fin n) × Option (Fin n) → ℝ
  /-- `β_ij`, dual to `y_ij ≤ 1 − x_j` -/
  β : Option (Fin n) × Option (Fin n) → ℝ
  /-- `γ_i`, dual to `x_i ≤ 1` -/
  γd : Fin n → ℝ
  /-- `δ`, dual to `∑_i s_i x_i ≤ c` -/
  δ : ℝ
  /-- the free variable `z` -/
  z : ℝ

end PCLAssort


