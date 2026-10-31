-- Prove2me | Definitions.Def_SupplierLearning_Params_rentFloor
-- name    : SupplierLearning_Params_rentFloor
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:50.167349+00:00
-- url     : https://prove2.me/theorems/87478995-8a99-44d5-b48f-74af75b56ce2
-- title:
--   The rent gap $\Gamma(q,y,z)=W_\ell-W_h$
-- statement:
--   The surplus difference between the types at given quantities:
--   $$
--   \Gamma(q,y,z)=\Delta c_1q+\delta\rho(\Delta c_1+\Delta r\,q)y+\delta(1-\rho)\Delta c_1z,
--   $$
--   which equals $W_\ell(q,y,z)-W_h(q,y,z)$ and is the first line of (4).
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 2, App. p.6

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_deltaC
import Definitions.Def_SupplierLearning_Params_deltaR

namespace SupplierLearning

/-- **The rent gap Γ(q,y,z)=W_ℓ-W_h.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 2, App. p.6 (PDF p.38).

**Formalization Note.** `Γ = W_ℓ − W_h` as a function of quantities. Not named in the paper; it is the first line of (4). -/
noncomputable def Params.rentFloor (P : Params) (q y z : ℝ) : ℝ :=
  P.deltaC * q + P.δ * P.ρ * (P.deltaC + P.deltaR * q) * y + P.δ * (1 - P.ρ) * P.deltaC * z

end SupplierLearning


