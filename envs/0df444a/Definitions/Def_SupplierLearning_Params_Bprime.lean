-- Prove2me | Definitions.Def_SupplierLearning_Params_Bprime
-- name    : SupplierLearning_Params_Bprime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:22.670707+00:00
-- url     : https://prove2.me/theorems/15dba1dc-d605-4b05-bf51-93d64abdec78
-- title:
--   The rate $B'=r^h+\kappa(r^h-\rho r^\ell)/\rho$
-- statement:
--   The abbreviation $B'=r^h+\kappa(r^h-\rho r^\ell)/\rho$, twice the slope in $q$ of the separating quantity $\bar y(q)$ under double deviation. It equals $(r^h-\nu r^\ell+\frac{1-\rho}{\rho}\nu r^h)/(1-\nu)$, the expression squared in Condition (A3).
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 2, App. p.7

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_kappa

namespace SupplierLearning

/-- **The rate B'=r^h+κ(r^h-ρ r^ℓ)/ρ.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 2, App. p.7 (PDF p.39).

**Formalization Note.** An abbreviation, not named in the paper: twice the slope of the double-deviation `q̄₂^{h1}` in `q₁^h`. -/
noncomputable def Params.Bprime (P : Params) : ℝ :=
  P.rh + P.kappa * (P.rh - P.ρ * P.rl) / P.ρ

end SupplierLearning


