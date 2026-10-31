-- Prove2me | Definitions.Def_SupplierLearning_Params_capacityDomain
-- name    : SupplierLearning_Params_capacityDomain
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:40.755266+00:00
-- url     : https://prove2.me/theorems/4c8f392f-7c7a-4731-8a96-87c8aec63d4c
-- title:
--   The domain $[0,Q]$ of $q_1$
-- statement:
--   The set of admissible first-period quantities: $0\le q$ with Condition (C), $(r^h-r^\ell)q\le\Delta c_1$. This is the interval $[0,Q]$, unbounded when $r^\ell\ge r^h$.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Condition (C), p.7

import Definitions.Def_SupplierLearning_Params

namespace SupplierLearning

/-- **The domain [0,Q] of q_1.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, Condition (C), p.7 (PDF p.7).

**Formalization Note.** `[0, Q]` with `(C)` in the encoded form, so it needs no `∞`. -/
def Params.capacityDomain (P : Params) : Set ℝ :=
  {q | 0 ≤ q ∧ (P.rh - P.rl) * q ≤ P.ch - P.cl}

end SupplierLearning


