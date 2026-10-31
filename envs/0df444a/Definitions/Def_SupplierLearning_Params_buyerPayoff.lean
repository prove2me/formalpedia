-- Prove2me | Definitions.Def_SupplierLearning_Params_buyerPayoff
-- name    : SupplierLearning_Params_buyerPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:54.876621+00:00
-- url     : https://prove2.me/theorems/42ceae93-0fd6-481c-b46c-db9f50e61573
-- title:
--   Buyer's expected payoff $\tilde V(\phi)$
-- statement:
--   The buyer's expected payoff under a contract:
--   $$
--   \tilde V(\phi)=\mathbb E_\theta\Big\{\big[(a_1-q_1^\theta)q_1^\theta-p_1^\theta\big]+\delta\,\mathbb E_\Lambda\big[(a_2-q_2^{\theta\Lambda})q_2^{\theta\Lambda}-p_2^{\theta\Lambda}\big]\Big\}.
--   $$
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.8; written out on App. p.5

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_expectType
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_termBuyerPayoff

namespace SupplierLearning

/-- **Buyer's expected payoff \tilde V(φ).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.8; written out on App. p.5 (PDF p.8, 37). -/
noncomputable def Params.buyerPayoff (P : Params) (φ : Contract) : ℝ :=
  P.expectType fun θ => P.termBuyerPayoff (φ θ)

end SupplierLearning


