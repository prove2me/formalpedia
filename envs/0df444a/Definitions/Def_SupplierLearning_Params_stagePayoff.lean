-- Prove2me | Definitions.Def_SupplierLearning_Params_stagePayoff
-- name    : SupplierLearning_Params_stagePayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:03.167655+00:00
-- url     : https://prove2.me/theorems/04228d95-43f6-4e78-b9fe-ce11181b5448
-- title:
--   Second-period payoff of a report $\tilde\Lambda$
-- statement:
--   The second-period payoff of a supplier of true type $\theta$ with true outcome $\Lambda$ who picked the term of type $\tilde\theta$ and reports $\tilde\Lambda$:
--   $$
--   p_2^{\tilde\theta\tilde\Lambda}-(c^\theta-\Lambda r^\theta q_1^{\tilde\theta})\,q_2^{\tilde\theta\tilde\Lambda}.
--   $$
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.8, IC^θΛ

import Definitions.Def_SupplierLearning_SupplierType
import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_learnedCost
import Definitions.Def_SupplierLearning_Term

namespace SupplierLearning

/-- **Second-period payoff of a report \tildeΛ.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.8, IC^θΛ (PDF p.8).

**Formalization Note.** `θ` and `Λ` are the true type and outcome, `t` the term picked in period 1 and `Λ'` the reported outcome. The cost uses the true type's `c^θ, r^θ` and the picked term's `q₁`. -/
noncomputable def Params.stagePayoff (P : Params) (θ : SupplierType) (Λ : Bool) (t : Term)
    (Λ' : Bool) : ℝ :=
  t.p₂ Λ' - P.learnedCost θ Λ t.q₁ * t.q₂ Λ'

end SupplierLearning


