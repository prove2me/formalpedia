-- Prove2me | Definitions.Def_ShapleyNV_dualVal
-- name    : ShapleyNV_dualVal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:45.863723+00:00
-- url     : https://prove2.me/theorems/820f0ddc-b636-43cb-a6bf-968c6240d8f4
-- title:
--   Dual value $\inf_{\lambda\ge0}$ of the dual objective
-- statement:
--   The dual value is the infimum of the dual objective over multipliers $\lambda \ge 0$:
--
--   $$
--   \inf_{\lambda \ge 0} \Big( \lambda\rho + \mathbb E_{\hat\xi \sim \widehat{\mathbb P}}\Big[ \sup_{\xi} \big\{ \ell(\xi) - \lambda\, c(\xi, \hat\xi) \big\} \Big] \Big).
--   $$
-- source:
--   Zhang, Yang, Gao, Optimal Robust Policy for Feature-Based Newsvendor (author manuscript, 2022-10-17), Lemma EC.1, v_D^f, p.ec1 (PDF 22)

import Mathlib
import Definitions.Def_ShapleyNV_dualObj

open MeasureTheory NNReal ENNReal

namespace ShapleyNV

/-- **Dual value** `inf_{λ ≥ 0} ( λρ + E_{P̂}[ sup_ξ { ℓ(ξ) − λ c(ξ, ξ̂) } ] )`.
Zhang, Yang, Gao, *Optimal Robust Policy for Feature-Based Newsvendor* (author manuscript, 2022-10-17), Lemma EC.1, `v_D^f`, p.ec1 (PDF 22).

**Formalization Note.** The multiplier `λ` (written `lam`, since `λ` is reserved in Lean) ranges
over the real numbers `λ ≥ 0`. -/
noncomputable def dualVal {α : Type*} [MeasurableSpace α] (c : α → α → ℝ) (Phat : Measure α) (ρ : ℝ)
    (ℓ : α → ℝ) : ℝ≥0∞ :=
  ⨅ lam : ℝ, ⨅ (_ : 0 ≤ lam), dualObj c Phat ρ ℓ lam

end ShapleyNV


