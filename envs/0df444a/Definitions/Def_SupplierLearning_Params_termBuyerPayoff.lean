-- Prove2me | Definitions.Def_SupplierLearning_Params_termBuyerPayoff
-- name    : SupplierLearning_Params_termBuyerPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:19.385855+00:00
-- url     : https://prove2.me/theorems/a1214509-2223-4b5a-8012-338f63ea3d2c
-- title:
--   Buyer's payoff from one term
-- statement:
--   The buyer's discounted payoff from a single term:
--   $$
--   \big[(a_1-q_1)q_1-p_1\big]+\delta\,\mathbb E_\Lambda\big[(a_2-q_2^{\Lambda})q_2^{\Lambda}-p_2^{\Lambda}\big].
--   $$
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.8, Ṽ(φ)

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_expectOutcome
import Definitions.Def_SupplierLearning_Term

namespace SupplierLearning

/-- **Buyer's payoff from one term.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2.2, p.8, Ṽ(φ) (PDF p.8). -/
noncomputable def Params.termBuyerPayoff (P : Params) (t : Term) : ℝ :=
  (P.a₁ - t.q₁) * t.q₁ - t.p₁ +
    P.δ * P.expectOutcome fun Λ => (P.a₂ - t.q₂ Λ) * t.q₂ Λ - t.p₂ Λ

end SupplierLearning


