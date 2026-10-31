-- Prove2me | Definitions.Def_SupplierLearning_Params_slopeRight
-- name    : SupplierLearning_Params_slopeRight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:30.817788+00:00
-- url     : https://prove2.me/theorems/1aba8fac-86c7-4272-87cb-a7ca73f88a28
-- title:
--   The right slope $G(q,y)$ of the reduced objective
-- statement:
--   The expression
--   $$
--   G(q,y)=a_1-c^h-2q+\delta\rho r^hy-\kappa(\Delta c_1+\delta\rho y\Delta r),
--   $$
--   which is the first-order expression of App. p.8 with the first line of (21), using $\partial\mathbb E_{\Lambda|h}W_2/\partial q_1^h=\rho r^hy$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 3, App. p.8

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_deltaC
import Definitions.Def_SupplierLearning_Params_deltaR
import Definitions.Def_SupplierLearning_Params_kappa

namespace SupplierLearning

/-- **The right slope G(q,y) of the reduced objective.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 3, App. p.8 (PDF p.40).

**Formalization Note.** `G` is the right derivative of `F` of App. p.7 in `q`, the expression `a₁ − 2q − c^h + δ ∂E_{Λ|h}W₂/∂q − (ν/(1 − ν)) ∂U^ℓ/∂q` with (21)'s first line. `∂E_{Λ|h}W₂/∂q₁^h = ρ r^h y`. -/
noncomputable def Params.slopeRight (P : Params) (q y : ℝ) : ℝ :=
  P.a₁ - P.ch - 2 * q + P.δ * P.ρ * P.rh * y -
    P.kappa * (P.deltaC + P.δ * P.ρ * y * P.deltaR)

end SupplierLearning


