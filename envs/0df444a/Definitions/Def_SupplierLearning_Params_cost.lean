-- Prove2me | Definitions.Def_SupplierLearning_Params_cost
-- name    : SupplierLearning_Params_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:43.145272+00:00
-- url     : https://prove2.me/theorems/abd7aea3-959c-4d86-80eb-5e50874b109d
-- title:
--   Unit cost $c^\theta$ of a type
-- statement:
--   The unit cost $c^\theta$ of type $\theta$: $c^\ell$ for type $\ell$ and $c^h$ for type $h$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.5

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params

namespace SupplierLearning

/-- **Unit cost c^θ of a type.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.5 (PDF p.5). -/
def Params.cost (P : Params) : SupplierType → ℝ
  | .l => P.cl
  | .h => P.ch

end SupplierLearning


