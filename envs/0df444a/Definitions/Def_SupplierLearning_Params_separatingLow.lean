-- Prove2me | Definitions.Def_SupplierLearning_Params_separatingLow
-- name    : SupplierLearning_Params_separatingLow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:40.004483+00:00
-- url     : https://prove2.me/theorems/d907d716-6f9a-4da8-b453-ca33c18255af
-- title:
--   Separating quantity $\bar q_2^{h0}$ as a function of $q$
-- statement:
--   The separating quantity $\bar z(q)=\bar q_2^{h0}$ for a given $q=q_1^h$:
--   $$
--   \bar z(q)=\begin{cases}\dfrac{a_2-c^h}{2}-\dfrac12\kappa\Delta c_1,& c^h-r^hq\le c^\ell,\\[2mm]\dfrac{a_2-c^h}{2}-\dfrac12\kappa r^hq,& c^h-r^hq>c^\ell.\end{cases}
--   $$
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, note 9, p.26; proof of Proposition 1, Step 2, App. pp.6–7

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_deltaC
import Definitions.Def_SupplierLearning_Params_kappa

namespace SupplierLearning

/-- **Separating quantity q̄q_2^{h0} as a function of q.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, note 9, p.26; proof of Proposition 1, Step 2, App. pp.6–7 (PDF p.26, 38, 39).

**Formalization Note.** As for `Params.separatingHigh`: note 9 under single deviation, App. p.7 under double deviation (correction C4). -/
noncomputable def Params.separatingLow (P : Params) (q : ℝ) : ℝ :=
  if P.ch - P.rh * q ≤ P.cl then
    (P.a₂ - P.ch) / 2 - 1 / 2 * P.kappa * P.deltaC
  else
    (P.a₂ - P.ch) / 2 - 1 / 2 * P.kappa * P.rh * q

end SupplierLearning


