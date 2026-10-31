-- Prove2me | Definitions.Def_SupplierLearning_Params_poolingThreshold
-- name    : SupplierLearning_Params_poolingThreshold
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:04.589908+00:00
-- url     : https://prove2.me/theorems/4db0282a-8f20-46f8-8775-5372d9996db4
-- title:
--   The pooling threshold $q_p$
-- statement:
--   The point $q_p=\kappa\Delta c_1/\big(\rho(B'+\kappa r^h)\big)$. When $r^h>\nu r^\ell$, the selected quantities pool for $q\le q_p$ and separate for $q>q_p$, and $q_p<\Delta c_1/r^h$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 2, App. p.7

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_deltaC
import Definitions.Def_SupplierLearning_Params_kappa
import Definitions.Def_SupplierLearning_Params_Bprime

namespace SupplierLearning

/-- **The pooling threshold q_p.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 2, App. p.7 (PDF p.39).

**Formalization Note.** Not named in the paper. When `r^h > ν r^ℓ` this is the point of the double-deviation region at which `q̄₂^{h1} = q̄₂^{h0}`. -/
noncomputable def Params.poolingThreshold (P : Params) : ℝ :=
  P.kappa * P.deltaC / (P.ρ * (P.Bprime + P.kappa * P.rh))

end SupplierLearning


