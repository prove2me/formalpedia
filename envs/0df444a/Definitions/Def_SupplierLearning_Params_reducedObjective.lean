-- Prove2me | Definitions.Def_SupplierLearning_Params_reducedObjective
-- name    : SupplierLearning_Params_reducedObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:20.417132+00:00
-- url     : https://prove2.me/theorems/607d37a3-7b68-4455-ba84-5e542e8cef1b
-- title:
--   The type-$h$ objective $H(q,y,z)$
-- statement:
--   The type-$h$ objective $H(q,y,z)=W_h(q,y,z)-\kappa\,\Gamma^+(q,y,z)$, which is the bracket in the definition of $F$ on App. p.7.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 3, App. p.7

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_kappa
import Definitions.Def_SupplierLearning_Params_typeSurplus
import Definitions.Def_SupplierLearning_Params_rentBound

namespace SupplierLearning

/-- **The type-h objective H(q,y,z).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 3, App. p.7 (PDF p.39).

**Formalization Note.** The function maximized in the definition of `F` on App. p.7: `R₁(q) − c^h q + δ E_{Λ|h}W₂ − (ν/(1 − ν)) U^ℓ`, with `U^ℓ` written as `Γ⁺`. -/
noncomputable def Params.reducedObjective (P : Params) (q y z : ℝ) : ℝ :=
  P.typeSurplus .h q y z - P.kappa * P.rentBound q y z

end SupplierLearning


