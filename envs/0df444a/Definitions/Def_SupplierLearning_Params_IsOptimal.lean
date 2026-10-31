-- Prove2me | Definitions.Def_SupplierLearning_Params_IsOptimal
-- name    : SupplierLearning_Params_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:52:15.349999+00:00
-- url     : https://prove2.me/theorems/1f888985-64c5-4a5d-8c44-00cf62e7c8a4
-- title:
--   Optimal contract for $(\mathcal P^{\mathrm{AL}})$
-- statement:
--   A contract $\phi$ is **optimal** for $V=\max\{\tilde V(\phi):\mathrm{IR}^\theta,\mathrm{IC}^\theta,\mathrm{IC}^{\theta\Lambda},\forall\theta,\Lambda\}$ when it is feasible and $\tilde V(\phi')\le\tilde V(\phi)$ for every feasible $\phi'$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §4.3, p.13, (P^AL)

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Contract
import Definitions.Def_SupplierLearning_Params_Feasible
import Definitions.Def_SupplierLearning_Params_buyerPayoff

namespace SupplierLearning

/-- **Optimal contract for (P^{AL}).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §4.3, p.13, (P^AL) (PDF p.13).

**Formalization Note.** Optimality is membership in `Φ` plus a universal bound, not a comparison with a real supremum: without second-order conditions the supremum can be `+∞` (correction C2), and a real supremum of an unbounded set is `0`. -/
def Params.IsOptimal (P : Params) (φ : Contract) : Prop :=
  P.Feasible φ ∧ ∀ φ', P.Feasible φ' → P.buyerPayoff φ' ≤ P.buyerPayoff φ

end SupplierLearning


