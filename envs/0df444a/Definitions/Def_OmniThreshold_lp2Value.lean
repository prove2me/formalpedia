-- Prove2me | Definitions.Def_OmniThreshold_lp2Value
-- name    : OmniThreshold_lp2Value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:53.115023+00:00
-- url     : https://prove2.me/theorems/598a2851-b72c-439c-80d5-b7e52c25aa5d
-- title:
--   Optimal value of LP (2)
-- statement:
--   The **optimal value of LP (2)** is the minimum fulfillment cost
--   $$
--   V_2(\mathcal I,\mathcal D^P,A^O)=\inf\Bigl\{\sum_i\Bigl(c_iC_i+\sum_js_{ji}F_{ji}\Bigr):\ (C,R,F)\ \text{feasible}\Bigr\},
--   $$
--   taken over the constraints of LP (1), given the inventories, the in-store demands and the accepted online orders $A^O$.
--
--   **Formalization Note** This is the real infimum over real feasible points. The feasible set is nonempty and compact, so the infimum is attained.
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, LP (2), p.9

import Mathlib
import Definitions.Def_OmniThreshold_IsFeasible
import Definitions.Def_OmniThreshold_lp2Objective

namespace OmniThreshold

/-- The **optimal value of LP (2)** (Jia, Karp, Ravi & Tayur, *Effective Online Order Acceptance
Policies for Omni-Channel Fulfillment*, SSRN 3932692, LP (2), p.9): the infimum of the fulfillment
cost `lp2Objective` over the real `x = (C, R, F)` satisfying the constraints `IsFeasible` of
LP (1), given the inventory `I`, the in-store demand `DP` and the accepted orders `A`.

**Formalization Note** Real `sInf`; the feasible set is nonempty (`C = A`, `F = 0`) and compact, and
the objective is nonnegative on it when `0 ≤ c`, `0 ≤ s`, so the `sInf` is the attained minimum. -/
noncomputable def lp2Value {n : ℕ} (c : Fin n → ℝ) (s : Fin n → Fin n → ℝ)
    (I DP A : Fin n → ℕ) : ℝ :=
  sInf (lp2Objective c s '' {x | IsFeasible I DP A x})

end OmniThreshold


