-- Prove2me | Definitions.Def_SupplierLearning_Params_deltaC
-- name    : SupplierLearning_Params_deltaC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:38.145532+00:00
-- url     : https://prove2.me/theorems/dd85ace5-0e6a-4bd9-bfd5-0378688f285e
-- title:
--   Cost gap $\Delta c_1=c^h-c^\ell$
-- statement:
--   The first-period cost gap $\Delta c_1\equiv c^h-c^\ell$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.6

import Definitions.Def_SupplierLearning_Params

namespace SupplierLearning

/-- **Cost gap Δc_1=c^h-c^ℓ.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.6 (PDF p.6). -/
noncomputable def Params.deltaC (P : Params) : ℝ := P.ch - P.cl

end SupplierLearning


