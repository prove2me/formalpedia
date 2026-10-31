-- Prove2me | Definitions.Def_SupplierLearning_Params_kinkPoint
-- name    : SupplierLearning_Params_kinkPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:06.36899+00:00
-- url     : https://prove2.me/theorems/8ad8ed12-165b-4024-bc41-8614232e03a0
-- title:
--   The kink $\Delta c_1/r^h$
-- statement:
--   The point $q=\Delta c_1/r^h$, where $c^h-r^hq=c^\ell$: the boundary between single and double deviation.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 3, App. pp.7–8

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_deltaC

namespace SupplierLearning

/-- **The kink Δc_1/r^h.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 3, App. pp.7–8 (PDF p.39, 40). -/
noncomputable def Params.kinkPoint (P : Params) : ℝ := P.deltaC / P.rh

end SupplierLearning


