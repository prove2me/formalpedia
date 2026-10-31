-- Prove2me | Definitions.Def_SupplierLearning_Params_typeSurplus
-- name    : SupplierLearning_Params_typeSurplus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:53.697969+00:00
-- url     : https://prove2.me/theorems/aaa62a91-e77b-4742-824d-cdb57c2490f6
-- title:
--   Channel surplus $W_\theta(q,y,z)$ of a type
-- statement:
--   The expected channel surplus of type $\theta$ at the quantities $(q,y,z)$, with $y$ produced if $\Lambda=1$ and $z$ if $\Lambda=0$:
--   $$
--   W_\theta(q,y,z)=(a_1-q)q-c^\theta q+\delta\rho\big[(a_2-y)y-(c^\theta-r^\theta q)y\big]+\delta(1-\rho)\big[(a_2-z)z-c^\theta z\big].
--   $$
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.7, W(φ)

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_cost
import Definitions.Def_SupplierLearning_Params_rate

namespace SupplierLearning

/-- **Channel surplus W_θ(q,y,z) of a type.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.7, W(φ) (PDF p.7).

**Formalization Note.** `y` and `z` are the second-period quantities for `Λ = 1` and `Λ = 0`. This is the bracket of `W(φ)` for one type, as a function of quantities only. -/
noncomputable def Params.typeSurplus (P : Params) (θ : SupplierType) (q y z : ℝ) : ℝ :=
  (P.a₁ - q) * q - P.cost θ * q +
    P.δ * P.ρ * ((P.a₂ - y) * y - (P.cost θ - P.rate θ * q) * y) +
    P.δ * (1 - P.ρ) * ((P.a₂ - z) * z - P.cost θ * z)

end SupplierLearning


