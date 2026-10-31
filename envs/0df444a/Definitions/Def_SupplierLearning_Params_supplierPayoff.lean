-- Prove2me | Definitions.Def_SupplierLearning_Params_supplierPayoff
-- name    : SupplierLearning_Params_supplierPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:10.804629+00:00
-- url     : https://prove2.me/theorems/275033e4-5688-469a-a57a-75a5f68217bf
-- title:
--   Supplier payoff $\tilde U(\theta;\tilde\theta)$ from picking a term
-- statement:
--   The payoff of a supplier of true type $\theta$ who picks the term designed for $\tilde\theta$ and then reports optimally:
--   $$
--   \tilde U(\theta;\tilde\theta)=\big[p_1^{\tilde\theta}-c^\theta q_1^{\tilde\theta}\big]+\delta\,\mathbb E_\Lambda\Big[\max_{\tilde\Lambda\in\{0,1\}}\big\{p_2^{\tilde\theta\tilde\Lambda}-(c^\theta-\Lambda r^\theta q_1^{\tilde\theta})q_2^{\tilde\theta\tilde\Lambda}\big\}\Big].
--   $$
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.8

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_cost
import Definitions.Def_SupplierLearning_Params_expectOutcome
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_stagePayoff

namespace SupplierLearning

/-- **Supplier payoff Ũ(θ;θ̃) from picking a term.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.8 (PDF p.8).

**Formalization Note.** The `max` over the reported outcome is taken inside the expectation, on both sides of IC^θ, as on p.8. -/
noncomputable def Params.supplierPayoff (P : Params) (φ : Contract) (θ θ' : SupplierType) : ℝ :=
  (φ θ').p₁ - P.cost θ * (φ θ').q₁ +
    P.δ * P.expectOutcome fun Λ =>
      max (P.stagePayoff θ Λ (φ θ') false) (P.stagePayoff θ Λ (φ θ') true)

end SupplierLearning


