-- Prove2me | Definitions.Def_SupplierLearning_Params_separatingHigh
-- name    : SupplierLearning_Params_separatingHigh
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:35.556086+00:00
-- url     : https://prove2.me/theorems/d0061096-2809-42cb-bf5f-682c313d169f
-- title:
--   Separating quantity $\bar q_2^{h1}$ as a function of $q$
-- statement:
--   The separating quantity $\bar y(q)=\bar q_2^{h1}$ for a given $q=q_1^h$, with $\kappa=\nu/(1-\nu)$:
--   $$
--   \bar y(q)=\begin{cases}\dfrac{a_2-c^h+r^hq}{2}-\dfrac12\kappa\Delta c_1-\dfrac12\kappa q\Delta r,& c^h-r^hq\le c^\ell,\\[2mm]\dfrac{a_2-c^h+r^hq}{2}+\dfrac12\kappa\dfrac{r^h-\rho r^\ell}{\rho}q-\dfrac12\kappa\dfrac1\rho\Delta c_1,& c^h-r^hq>c^\ell.\end{cases}
--   $$
--
--   **Formalization Note** The first line is note 9, the second App. p.7. Note 9 alone would be false under double deviation.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, note 9, p.26; proof of Proposition 1, Step 2, App. pp.6–7

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_deltaC
import Definitions.Def_SupplierLearning_Params_deltaR
import Definitions.Def_SupplierLearning_Params_kappa

namespace SupplierLearning

/-- **Separating quantity q̄q_2^{h1} as a function of q.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, note 9, p.26; proof of Proposition 1, Step 2, App. pp.6–7 (PDF p.26, 38, 39).

**Formalization Note.** Note 9's form holds only when `c^h − r^h q ≤ c^ℓ` (single deviation). When `c^h − r^h q > c^ℓ` (double deviation) this is the form of App. p.7 (correction C4). The two forms agree at `r^h q = Δc₁`. -/
noncomputable def Params.separatingHigh (P : Params) (q : ℝ) : ℝ :=
  if P.ch - P.rh * q ≤ P.cl then
    (P.a₂ - P.ch + P.rh * q) / 2 - 1 / 2 * P.kappa * P.deltaC - 1 / 2 * P.kappa * q * P.deltaR
  else
    (P.a₂ - P.ch + P.rh * q) / 2 + 1 / 2 * P.kappa * ((P.rh - P.ρ * P.rl) / P.ρ) * q -
      1 / 2 * P.kappa * (1 / P.ρ) * P.deltaC

end SupplierLearning


