-- Prove2me | Definitions.Def_SupplierLearning_Params_rentBound
-- name    : SupplierLearning_Params_rentBound
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:17.772866+00:00
-- url     : https://prove2.me/theorems/3b96069f-6814-4a9b-bec8-67b9043e21df
-- title:
--   The rent bound $\Gamma^+(q,y,z)$
-- statement:
--   The rent bound
--   $$
--   \Gamma^+(q,y,z)=\Gamma(q,y,z)+\delta(1-\rho)\max\{0,(\Delta c_1-r^hq)(y-z)\},
--   $$
--   which, for $y\ge z$, is (20) and (4) as a single formula.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, eq. (20), App. p.6

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_deltaC
import Definitions.Def_SupplierLearning_Params_rentFloor

namespace SupplierLearning

/-- **The rent bound Γ^+(q,y,z).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, eq. (20), App. p.6 (PDF p.38).

**Formalization Note.** A single formula for both lines of (20) (and of (4)) when `y ≥ z`. Not named in the paper. -/
noncomputable def Params.rentBound (P : Params) (q y z : ℝ) : ℝ :=
  P.rentFloor q y z + P.δ * (1 - P.ρ) * max 0 ((P.deltaC - P.rh * q) * (y - z))

end SupplierLearning


