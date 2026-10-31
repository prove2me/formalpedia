-- Prove2me | Definitions.Def_SupplierLearning_Params_U
-- name    : SupplierLearning_Params_U
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:45.075133+00:00
-- url     : https://prove2.me/theorems/f63a2187-7e79-430c-aa2b-ed1647220f4a
-- title:
--   Equilibrium payoff $U(\theta)$
-- statement:
--   The payoff of a supplier who picks the term designed for him: $U(\theta)\equiv\tilde U(\theta;\theta)$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.8

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_supplierPayoff

namespace SupplierLearning

/-- **Equilibrium payoff U(θ).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.8 (PDF p.8). -/
noncomputable def Params.U (P : Params) (φ : Contract) (θ : SupplierType) : ℝ :=
  P.supplierPayoff φ θ θ

end SupplierLearning


