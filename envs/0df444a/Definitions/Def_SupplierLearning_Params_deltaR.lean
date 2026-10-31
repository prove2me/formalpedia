-- Prove2me | Definitions.Def_SupplierLearning_Params_deltaR
-- name    : SupplierLearning_Params_deltaR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:33.062998+00:00
-- url     : https://prove2.me/theorems/72188e85-a7d5-403c-a73b-c158cb085b1e
-- title:
--   Learning rate gap $\Delta r=r^\ell-r^h$
-- statement:
--   The learning rate gap $\Delta r\equiv r^\ell-r^h$. When $\Delta r\ge0$ learning expands the cost gap, when $\Delta r<0$ it compresses it.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.6

import Definitions.Def_SupplierLearning_Params

namespace SupplierLearning

/-- **Learning rate gap Δr=r^ℓ-r^h.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, p.6 (PDF p.6). -/
noncomputable def Params.deltaR (P : Params) : ℝ := P.rl - P.rh

end SupplierLearning


