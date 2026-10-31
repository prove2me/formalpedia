-- Prove2me | Definitions.Def_SupplierLearning_Params_poolingQuantity
-- name    : SupplierLearning_Params_poolingQuantity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:52.893113+00:00
-- url     : https://prove2.me/theorems/a8caca15-9ca3-4b69-b26a-b20b45ba854b
-- title:
--   Pooling quantity $\hat q_2^{h}$ as a function of $q$
-- statement:
--   The pooling quantity $\hat y(q)=\hat q_2^{h}$ for a given $q=q_1^h$:
--   $$
--   \hat y(q)=\frac{a_2-c^h+\rho r^hq}{2}-\frac12\kappa\Delta c_1-\frac12\kappa\rho q\Delta r.
--   $$
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, note 9, p.26; App. pp.6–7

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_deltaC
import Definitions.Def_SupplierLearning_Params_deltaR
import Definitions.Def_SupplierLearning_Params_kappa

namespace SupplierLearning

/-- **Pooling quantity q̂q_2^{h} as a function of q.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, note 9, p.26; App. pp.6–7 (PDF p.26, 38, 39).

**Formalization Note.** The same formula in both regimes (App. p.7). -/
noncomputable def Params.poolingQuantity (P : Params) (q : ℝ) : ℝ :=
  (P.a₂ - P.ch + P.ρ * P.rh * q) / 2 - 1 / 2 * P.kappa * P.deltaC -
    1 / 2 * P.kappa * (P.ρ * q) * P.deltaR

end SupplierLearning


