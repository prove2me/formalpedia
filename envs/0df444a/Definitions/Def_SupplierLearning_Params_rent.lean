-- Prove2me | Definitions.Def_SupplierLearning_Params_rent
-- name    : SupplierLearning_Params_rent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:37.49013+00:00
-- url     : https://prove2.me/theorems/2e2022ae-0129-4b60-aa80-0101bce8bcf7
-- title:
--   Information rent $U^\ell$, eq. (4)
-- statement:
--   The information rent of type $\ell$ as a function of type $h$'s quantities $(q,y,z)=(q_1^h,q_2^{h1},q_2^{h0})$:
--   $$
--   U^\ell=\begin{cases}\Delta c_1q+\delta\Delta c_1\big[\rho y+(1-\rho)z\big]+\delta\rho qy\cdot\Delta r,& c^h-r^hq\le c^\ell,\\ \Delta c_1q+\delta\Delta c_1y+\delta\rho qy\cdot\Delta r-\delta(1-\rho)r^hq(y-z),& c^h-r^hq>c^\ell.\end{cases}
--   $$
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, eq. (4), p.13; eq. (20), App. p.6

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_deltaC
import Definitions.Def_SupplierLearning_Params_deltaR

namespace SupplierLearning

/-- **Information rent U^ℓ, eq. (4).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, eq. (4), p.13; eq. (20), App. p.6 (PDF p.13, 38).

**Formalization Note.** A function of type `h`'s quantities `(q, y, z)`, with the page's two cases and `≤` at the kink. The formula is the same as (20), with `Δr = r^ℓ − r^h`. -/
noncomputable def Params.rent (P : Params) (q y z : ℝ) : ℝ :=
  if P.ch - P.rh * q ≤ P.cl then
    P.deltaC * q + P.δ * P.deltaC * (P.ρ * y + (1 - P.ρ) * z) + P.δ * P.ρ * q * y * P.deltaR
  else
    P.deltaC * q + P.δ * P.deltaC * y + P.δ * P.ρ * q * y * P.deltaR -
      P.δ * (1 - P.ρ) * P.rh * q * (y - z)

end SupplierLearning


