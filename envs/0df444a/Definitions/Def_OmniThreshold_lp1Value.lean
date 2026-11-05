-- Prove2me | Definitions.Def_OmniThreshold_lp1Value
-- name    : OmniThreshold_lp1Value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:44.789745+00:00
-- url     : https://prove2.me/theorems/e77119e5-f9f4-4b42-9bc3-4e50cc64cde8
-- title:
--   Optimal value of the second-stage problem LP (1)
-- statement:
--   The **optimal value of LP (1)** is
--   $$
--   Q(\mathcal I,\mathcal D^P,\mathcal D^O,A^O)=\inf\{\text{objective of LP (1) at }(C,R,F):\ (C,R,F)\ \text{feasible}\},
--   $$
--   the minimum second-stage cost of the Omni-Channel Fulfillment Model for given in-store demand, online demand and accepted online orders.
--
--   **Formalization Note** This is the real infimum over real feasible points. The feasible set is nonempty ($C=A^O$, $R=\mathcal I-\min(\mathcal D^P,\mathcal I)$, $F=0$) and compact, so the infimum is attained. The objective is nonnegative under nonnegative costs and $A^O\le\mathcal D^O$. Both facts are proved in the mission's verification files.
-- source:
--   Jia, Karp, Ravi & Tayur, Effective Online Order Acceptance Policies for Omni-Channel Fulfillment, SSRN 3932692, LP (1), p.3

import Mathlib
import Definitions.Def_OmniThreshold_IsFeasible
import Definitions.Def_OmniThreshold_lp1Objective

namespace OmniThreshold

/-- The **optimal value of the second-stage problem LP (1)** (Jia, Karp, Ravi & Tayur, *Effective
Online Order Acceptance Policies for Omni-Channel Fulfillment*, SSRN 3932692, LP (1), p.3): the
infimum of `lp1Objective` over the real `x = (C, R, F)` satisfying the constraints `IsFeasible`.
This is "the objective function of the Omni-Channel Fulfillment Model" for one realization of
inventory use, given the in-store demand `DP`, the online demand `DO` and the accepted orders `A`.

**Formalization Note** The value is the real `sInf` of the objective over the feasible set. The set
is nonempty (`C = A`, `R = I − min(D^P, I)`, `F = 0`) and, when `0 ≤ p`, `0 ≤ c`, `0 ≤ s` and
`A ≤ D^O`, the objective is nonnegative on it and the feasible set is compact, so the `sInf` is the
attained minimum (checked in `Solutions/verification`). -/
noncomputable def lp1Value {n : ℕ} (p : ℝ) (c : Fin n → ℝ) (s : Fin n → Fin n → ℝ)
    (I DP DO A : Fin n → ℕ) : ℝ :=
  sInf (lp1Objective p c s I DP DO A '' {x | IsFeasible I DP A x})

end OmniThreshold


