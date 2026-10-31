-- Prove2me | Definitions.Def_SupplierLearning_Params_slopeGap
-- name    : SupplierLearning_Params_slopeGap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:40.607001+00:00
-- url     : https://prove2.me/theorems/03507cd9-7dcd-44a7-b77b-47d3b2fd057b
-- title:
--   The kink term $g(y,z)$
-- statement:
--   The term $g(y,z)=\kappa\delta(1-\rho)r^h(y-z)$: the difference between the two lines of (21), multiplied by $\kappa$. The first-order expression with the second line of (21) is $G(q,y)+g(y,z)$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, eqs. (21), (D), App. p.8

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_kappa

namespace SupplierLearning

/-- **The kink term g(y,z).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, eqs. (21), (D), App. p.8 (PDF p.40).

**Formalization Note.** `G + g` is the same expression with (21)'s second line, so `g` is the jump of the slope at `r^h q = Δc₁`. -/
noncomputable def Params.slopeGap (P : Params) (y z : ℝ) : ℝ :=
  P.kappa * P.δ * (1 - P.ρ) * P.rh * (y - z)

end SupplierLearning


