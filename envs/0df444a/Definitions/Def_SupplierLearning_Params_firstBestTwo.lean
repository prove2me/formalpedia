-- Prove2me | Definitions.Def_SupplierLearning_Params_firstBestTwo
-- name    : SupplierLearning_Params_firstBestTwo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:57.584182+00:00
-- url     : https://prove2.me/theorems/a2c94c0e-0871-485c-8293-9a5181ba8d5f
-- title:
--   First-best second-period quantity $q_2^{\theta\Lambda|\mathrm{PP}}$
-- statement:
--   The first-best second-period quantity of Lemma 1(b):
--   $$
--   q_2^{\theta\Lambda|\mathrm{PP}}=\frac{2(a_2-c^\theta)+\Lambda r^\theta(a_1-c^\theta)}{4-\delta\Lambda\rho(r^\theta)^2}.
--   $$
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Lemma 1(b), p.9

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_cost
import Definitions.Def_SupplierLearning_Params_rate
import Definitions.Def_SupplierLearning_outcomeValue

namespace SupplierLearning

/-- **First-best second-period quantity q_2^{θΛ|PP}.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Lemma 1(b), p.9 (PDF p.9).

**Formalization Note.** The printed formula. At `Λ = 0` it is `(a₂ − c^θ)/2`. -/
noncomputable def Params.firstBestTwo (P : Params) (θ : SupplierType) (Λ : Bool) : ℝ :=
  (2 * (P.a₂ - P.cost θ) + outcomeValue Λ * P.rate θ * (P.a₁ - P.cost θ)) /
    (4 - P.δ * outcomeValue Λ * P.ρ * P.rate θ ^ 2)

end SupplierLearning


