-- Prove2me | Definitions.Def_SupplierLearning_Params_firstBestOne
-- name    : SupplierLearning_Params_firstBestOne
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:56.446598+00:00
-- url     : https://prove2.me/theorems/93c38399-ec61-4056-9fae-c24d24ce6515
-- title:
--   First-best first-period quantity $q_1^{\theta|\mathrm{PP}}$
-- statement:
--   The first-best first-period quantity of Lemma 1(b):
--   $$
--   q_1^{\theta|\mathrm{PP}}=\frac{2(a_1-c^\theta)+\delta\rho r^\theta(a_2-c^\theta)}{4-\delta\rho(r^\theta)^2}.
--   $$
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Lemma 1(b), p.9

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_cost
import Definitions.Def_SupplierLearning_Params_rate

namespace SupplierLearning

/-- **First-best first-period quantity q_1^{θ|PP}.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Lemma 1(b), p.9 (PDF p.9).

**Formalization Note.** The printed formula. The denominator is positive under `δρ(r^θ)² < 4`, the hypothesis of every statement using it. -/
noncomputable def Params.firstBestOne (P : Params) (θ : SupplierType) : ℝ :=
  (2 * (P.a₁ - P.cost θ) + P.δ * P.ρ * P.rate θ * (P.a₂ - P.cost θ)) /
    (4 - P.δ * P.ρ * P.rate θ ^ 2)

end SupplierLearning


