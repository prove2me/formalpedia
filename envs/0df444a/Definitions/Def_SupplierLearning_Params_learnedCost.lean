-- Prove2me | Definitions.Def_SupplierLearning_Params_learnedCost
-- name    : SupplierLearning_Params_learnedCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:12.993996+00:00
-- url     : https://prove2.me/theorems/8deaf640-55e7-4996-af8a-b36aa74cb1cb
-- title:
--   The learning curve $L(\theta,\Lambda;q_1)$
-- statement:
--   The learning curve of a supplier of type $\theta$ who produced $q_1$ in period 1 and has learning outcome $\Lambda$:
--   $$
--   c_2^\theta=L(\theta,\Lambda;q_1)\equiv c^\theta-r^\theta q_1\cdot\Lambda.
--   $$
--   The second-period unit cost falls by $r^\theta q_1$ with probability $\rho$ and stays at $c^\theta$ otherwise.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, eq. (1), p.6

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_cost
import Definitions.Def_SupplierLearning_Params_rate
import Definitions.Def_SupplierLearning_outcomeValue

namespace SupplierLearning

/-- **The learning curve L(θ,Λ;q_1).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, eq. (1), p.6 (PDF p.6). -/
noncomputable def Params.learnedCost (P : Params) (θ : SupplierType) (Λ : Bool) (q : ℝ) : ℝ :=
  P.cost θ - P.rate θ * q * outcomeValue Λ

end SupplierLearning


