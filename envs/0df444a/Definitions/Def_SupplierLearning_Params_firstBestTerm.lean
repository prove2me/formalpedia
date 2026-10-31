-- Prove2me | Definitions.Def_SupplierLearning_Params_firstBestTerm
-- name    : SupplierLearning_Params_firstBestTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:56.581109+00:00
-- url     : https://prove2.me/theorems/8f3930b0-81d4-4b45-aa60-c931da5ff5fb
-- title:
--   The first-best term $\phi^{\mathrm{PP}}$ with marginal-cost payments
-- statement:
--   The term of type $\theta$ in the contract of Lemma 1(b): the first-best quantities, paid at marginal cost, $p_t^{s|\mathrm{PP}}=c_t^s q_t^{s|\mathrm{PP}}$, where $c_1^s=c^\theta$ and $c_2^{\theta\Lambda}=L(\theta,\Lambda;q_1^{\theta|\mathrm{PP}})$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Lemma 1(b), p.9

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_cost
import Definitions.Def_SupplierLearning_Params_learnedCost
import Definitions.Def_SupplierLearning_Term
import Definitions.Def_SupplierLearning_Params_firstBestOne
import Definitions.Def_SupplierLearning_Params_firstBestTwo

namespace SupplierLearning

/-- **The first-best term φ^{PP} with marginal-cost payments.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Lemma 1(b), p.9 (PDF p.9).

**Formalization Note.** `p_t^s = c_t^s q_t^s`: the first-period cost is `c^θ` and the second-period cost is `L(θ, Λ; q₁^{θ|PP})`. -/
noncomputable def Params.firstBestTerm (P : Params) (θ : SupplierType) : Term where
  p₁ := P.cost θ * P.firstBestOne θ
  q₁ := P.firstBestOne θ
  p₂ := fun Λ => P.learnedCost θ Λ (P.firstBestOne θ) * P.firstBestTwo θ Λ
  q₂ := fun Λ => P.firstBestTwo θ Λ

end SupplierLearning


