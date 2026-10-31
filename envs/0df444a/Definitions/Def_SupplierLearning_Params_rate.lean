-- Prove2me | Definitions.Def_SupplierLearning_Params_rate
-- name    : SupplierLearning_Params_rate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:41.573994+00:00
-- url     : https://prove2.me/theorems/c12ce2d7-8a32-40ed-ab9a-cb8b2727754b
-- title:
--   Learning rate $r^\theta$ of a type
-- statement:
--   The learning rate $r^\theta$ of type $\theta$: $r^\ell$ for type $\ell$ and $r^h$ for type $h$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.6, Table 1

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params

namespace SupplierLearning

/-- **Learning rate r^θ of a type.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.6, Table 1 (PDF p.6). -/
def Params.rate (P : Params) : SupplierType → ℝ
  | .l => P.rl
  | .h => P.rh

end SupplierLearning


