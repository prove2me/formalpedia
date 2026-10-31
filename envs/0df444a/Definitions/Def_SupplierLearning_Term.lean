-- Prove2me | Definitions.Def_SupplierLearning_Term
-- name    : SupplierLearning_Term
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:42:41.266402+00:00
-- url     : https://prove2.me/theorems/966e7ccb-e69e-4a5c-a27d-39468b596e76
-- title:
--   One term of the menu: payments and quantities for a reported type
-- statement:
--   The term of the contract designed for one reported type $\theta$: the first-period pair $(p_1^\theta,q_1^\theta)$ and, for each reported learning outcome $\Lambda$, the second-period pair $(p_2^{\theta\Lambda},q_2^{\theta\Lambda})$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.7

import Mathlib

namespace SupplierLearning

/-- **One term of the menu: payments and quantities for a reported type.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.7 (PDF p.7).

**Formalization Note.** For a reported type `θ`, `p₁, q₁` are `p₁^θ, q₁^θ`, and `p₂ Λ, q₂ Λ` are `p₂^{θΛ}, q₂^{θΛ}`, where `Λ` is the reported outcome (`true` for 1). Quantities are real here; nonnegativity is part of `Params.Feasible`. -/
structure Term where
  p₁ : ℝ
  q₁ : ℝ
  p₂ : Bool → ℝ
  q₂ : Bool → ℝ

end SupplierLearning


