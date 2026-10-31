-- Prove2me | Definitions.Def_SupplierLearning_Params_periodTwoLow
-- name    : SupplierLearning_Params_periodTwoLow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:37.034364+00:00
-- url     : https://prove2.me/theorems/b3db2b4e-a162-48b5-85ba-4398b36df5a3
-- title:
--   Selected $q_2^{h0}$ as a function of $q$
-- statement:
--   The period-2 quantity for $\Lambda=0$ selected by Proposition 1(b): $\bar z(q)$ on the separating condition $\bar y(q)>\bar z(q)$, and $\hat y(q)$ otherwise.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Proposition 1(b), p.13

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_separatingHigh
import Definitions.Def_SupplierLearning_Params_separatingLow
import Definitions.Def_SupplierLearning_Params_poolingQuantity

namespace SupplierLearning

/-- **Selected q_2^{h0} as a function of q.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Proposition 1(b), p.13 (PDF p.13).

**Formalization Note.** `q̄₂^{h0} · 1_S + q̂₂^h · 1_{S^c}` with `S = {q̄₂^{h1} > q̄₂^{h0}}`. -/
noncomputable def Params.periodTwoLow (P : Params) (q : ℝ) : ℝ :=
  if P.separatingLow q < P.separatingHigh q then P.separatingLow q else P.poolingQuantity q

end SupplierLearning


