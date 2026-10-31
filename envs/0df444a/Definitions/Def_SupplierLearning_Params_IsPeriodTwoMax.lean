-- Prove2me | Definitions.Def_SupplierLearning_Params_IsPeriodTwoMax
-- name    : SupplierLearning_Params_IsPeriodTwoMax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:33.625534+00:00
-- url     : https://prove2.me/theorems/a289961d-e2ab-46ab-a373-63ec36e6e3ff
-- title:
--   Unique period-2 maximizer of $H(q,\cdot,\cdot)$ on $\{y\ge z\}$
-- statement:
--   The pair $(y,z)$ with $y\ge z$ is the **unique maximizer** of $H(q,\cdot,\cdot)$ on the set $\{(y',z'):y'\ge z'\}$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 2, App. pp.6–7

import Definitions.Def_SupplierLearning_Params
import Definitions.Def_SupplierLearning_Params_reducedObjective

namespace SupplierLearning

/-- **Unique period-2 maximizer of H(q,·,·) on {y≥ z}.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, proof of Proposition 1, Step 2, App. pp.6–7 (PDF p.38, 39).

**Formalization Note.** The set `{y ≥ z}` is the second-period domain: by Claim 2 a feasible contract with `q₁^h > 0` has `q₂^{h1} ≥ q₂^{h0}`. -/
def Params.IsPeriodTwoMax (P : Params) (q y z : ℝ) : Prop :=
  z ≤ y ∧ ∀ y' z', z' ≤ y' →
    P.reducedObjective q y' z' ≤ P.reducedObjective q y z ∧
      (P.reducedObjective q y' z' = P.reducedObjective q y z → y' = y ∧ z' = z)

end SupplierLearning


