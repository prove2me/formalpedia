-- Prove2me | Definitions.Def_SupplierLearning_Params_publicPayoff
-- name    : SupplierLearning_Params_publicPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:09.404293+00:00
-- url     : https://prove2.me/theorems/64cc8de6-95bf-4855-912f-57f97e271faa
-- title:
--   Supplier payoff in the full-information regime $\mathcal P^{\mathrm{PP}}$
-- statement:
--   The supplier's payoff from a term in the full-information regime $\mathcal P^{\mathrm{PP}}$, where both $\theta$ and $\Lambda$ are public, so that no report is made:
--   $$
--   U=p_1-c^\theta q_1+\delta\,\mathbb E_\Lambda\big[p_2^{\Lambda}-(c^\theta-\Lambda r^\theta q_1)q_2^{\Lambda}\big].
--   $$
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Lemma 1(b), proof, App. p.3; (P^PP), p.9

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_cost
import Definitions.Def_SupplierLearning_Params_learnedCost
import Definitions.Def_SupplierLearning_Params_expectOutcome
import Definitions.Def_SupplierLearning_Term

namespace SupplierLearning

/-- **Supplier payoff in the full-information regime P^{PP}.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Lemma 1(b), proof, App. p.3; (P^PP), p.9 (PDF p.9, 35).

**Formalization Note.** With `Λ` public there is no report, so there is no `max`. -/
noncomputable def Params.publicPayoff (P : Params) (θ : SupplierType) (t : Term) : ℝ :=
  t.p₁ - P.cost θ * t.q₁ +
    P.δ * P.expectOutcome fun Λ => t.p₂ Λ - P.learnedCost θ Λ t.q₁ * t.q₂ Λ

end SupplierLearning


