-- Prove2me | Definitions.Def_SupplierLearning_Params_reducedValue
-- name    : SupplierLearning_Params_reducedValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:50:14.155686+00:00
-- url     : https://prove2.me/theorems/1d3f6bf3-739e-4efa-988d-62c6dacecb05
-- title:
--   The reduced function $F(q_1^h)$
-- statement:
--   The reduced function $F(q)=H\big(q,y^*(q),z^*(q)\big)$, where $(y^*(q),z^*(q))$ is the pair selected by Proposition 1(b). The paper writes $F(q_1^h)\equiv\max_{q_2^{h1},q_2^{h0}}[\cdots]$.
--
--   **Formalization Note** $F$ is defined by this explicit formula. That it equals the maximum is a milestone.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 3, App. p.7

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_reducedObjective
import Definitions.Def_SupplierLearning_Params_periodTwoHigh
import Definitions.Def_SupplierLearning_Params_periodTwoLow

namespace SupplierLearning

/-- **The reduced function F(q_1^h).**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 3, App. p.7 (PDF p.39).

**Formalization Note.** Defined by the explicit formula, not by a real supremum (trap 5). The milestones `period_two_single` and `period_two_double` show it is the maximum over `{y ≥ z}` of `H(q, ·, ·)`. -/
noncomputable def Params.reducedValue (P : Params) (q : ℝ) : ℝ :=
  P.reducedObjective q (P.periodTwoHigh q) (P.periodTwoLow q)

end SupplierLearning


