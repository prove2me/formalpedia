-- Prove2me | Definitions.Def_SupplierLearning_Params_expectType
-- name    : SupplierLearning_Params_expectType
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:00.486069+00:00
-- url     : https://prove2.me/theorems/924236ca-9a48-4f03-a3c4-25dfcd221981
-- title:
--   Expectation $\mathbb E_\theta$ over the type
-- statement:
--   The expectation over the type under the prior: $\mathbb E_\theta[g(\theta)]=\nu\,g(\ell)+(1-\nu)\,g(h)$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.6, Table 1

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params

namespace SupplierLearning

/-- **Expectation \mathbb E_θ over the type.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.6, Table 1 (PDF p.6).

**Formalization Note.** `E_θ[g(θ)] = ν g(ℓ) + (1 − ν) g(h)`. -/
noncomputable def Params.expectType (P : Params) (g : SupplierType → ℝ) : ℝ :=
  P.ν * g .l + (1 - P.ν) * g .h

end SupplierLearning


