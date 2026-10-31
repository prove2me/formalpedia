-- Prove2me | Definitions.Def_SupplierLearning_Params_PrintedRentCondition
-- name    : SupplierLearning_Params_PrintedRentCondition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:12.179976+00:00
-- url     : https://prove2.me/theorems/22a1bb32-5908-42dc-86c3-16314453fa67
-- title:
--   Condition (PR): the printed contract is implementable
-- statement:
--   Condition (PR):
--   $$
--   U^\ell(q,y,z)\le\Delta c_1q^\ell+\delta\Delta c_1z^\ell+\delta\rho q^\ell z^\ell\Delta r,
--   $$
--   where $(q^\ell,z^\ell)$ are type $\ell$'s first-best quantities. It is the case in which the printed contract satisfies (IC$^h$).
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, correction C1 of Proposition 1(a), p.13

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_deltaC
import Definitions.Def_SupplierLearning_Params_deltaR
import Definitions.Def_SupplierLearning_Params_firstBestOne
import Definitions.Def_SupplierLearning_Params_firstBestTwo
import Definitions.Def_SupplierLearning_Params_rent

namespace SupplierLearning

/-- **Condition (PR): the printed contract is implementable.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, correction C1 of Proposition 1(a), p.13 (PDF p.13).

**Formalization Note.** Not in the paper. (PR) is exactly (IC^h) at the printed contract. -/
def Params.PrintedRentCondition (P : Params) (q y z : ℝ) : Prop :=
  P.rent q y z ≤
    P.deltaC * P.firstBestOne .l + P.δ * P.deltaC * P.firstBestTwo .l false +
      P.δ * P.ρ * P.firstBestOne .l * P.firstBestTwo .l false * P.deltaR

end SupplierLearning


