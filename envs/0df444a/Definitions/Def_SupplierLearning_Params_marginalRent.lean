-- Prove2me | Definitions.Def_SupplierLearning_Params_marginalRent
-- name    : SupplierLearning_Params_marginalRent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:02.756988+00:00
-- url     : https://prove2.me/theorems/49bca7cc-4080-412f-80e9-d26bdecbf1aa
-- title:
--   The partial derivative $\partial U^\ell/\partial q_1^h$, eq. (21)
-- statement:
--   The partial derivative of the rent (4) in $q_1^h$, with the second-period quantities held fixed, in the form of eq. (21):
--   $$
--   \frac{\partial U^\ell}{\partial q_1^h}=\begin{cases}\Delta c_1+\delta\rho y\cdot\Delta r,& c^h-r^hq\le c^\ell,\\ \Delta c_1+\delta\rho y\cdot\Delta r-\delta(1-\rho)r^h(y-z),& c^h-r^hq>c^\ell.\end{cases}
--   $$
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, eq. (21), App. p.8

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_deltaC
import Definitions.Def_SupplierLearning_Params_deltaR

namespace SupplierLearning

/-- **The partial derivative \partial U^ℓ/\partial q_1^h, eq. (21).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, eq. (21), App. p.8 (PDF p.40).

**Formalization Note.** An explicit formula rather than `deriv`: the paper's ∂ holds `q₂^{hΛ}` fixed, and the derivative of (4) does not exist at the kink (a total `deriv` would return 0 there). -/
noncomputable def Params.marginalRent (P : Params) (q y z : ℝ) : ℝ :=
  if P.ch - P.rh * q ≤ P.cl then
    P.deltaC + P.δ * P.ρ * y * P.deltaR
  else
    P.deltaC + P.δ * P.ρ * y * P.deltaR - P.δ * (1 - P.ρ) * P.rh * (y - z)

end SupplierLearning


