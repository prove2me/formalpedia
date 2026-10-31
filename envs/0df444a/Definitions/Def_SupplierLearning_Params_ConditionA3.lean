-- Prove2me | Definitions.Def_SupplierLearning_Params_ConditionA3
-- name    : SupplierLearning_Params_ConditionA3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:20.105013+00:00
-- url     : https://prove2.me/theorems/9fe9326e-f7d7-4ea1-b691-05e7c38e8751
-- title:
--   Condition (A3)
-- statement:
--   Condition (A3):
--   $$
--   \frac{\delta\rho}{2(1-\nu)^2}\Big(r^h-\nu r^\ell+\frac{1-\rho}{\rho}\nu r^h\Big)^2+\frac{\nu^2\delta(1-\rho)(r^h)^2}{2(1-\nu)^2}<2.
--   $$
--   It says that the reduced objective is strictly concave on the double-deviation separating region.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Condition (A3), App. p.7

import Definitions.Def_SupplierLearning_Params

namespace SupplierLearning

/-- **Condition (A3).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Condition (A3), App. p.7 (PDF p.39).

**Formalization Note.** Written in the printed form. -/
def Params.ConditionA3 (P : Params) : Prop :=
  P.δ * P.ρ / (2 * (1 - P.ν) ^ 2) * (P.rh - P.ν * P.rl + (1 - P.ρ) / P.ρ * P.ν * P.rh) ^ 2 +
      P.ν ^ 2 * P.δ * (1 - P.ρ) * P.rh ^ 2 / (2 * (1 - P.ν) ^ 2) < 2

end SupplierLearning


