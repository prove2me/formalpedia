-- Prove2me | Definitions.Def_RobustFcstAgg_RandRule_IsOrderAgentLE
-- name    : RobustFcstAgg_RandRule_IsOrderAgentLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:59:14.64858+00:00
-- url     : https://prove2.me/theorems/9bec7744-f76d-4f8a-ba2b-5a82ac861966
-- title:
--   The class $\mathcal A^{\mathrm{ord}}_d$ of randomized rules
-- statement:
--   A randomized rule has order and agent complexity at most $d$ if the realized rule does for $P$-almost every context. This is the class $\mathcal A^{\mathrm{ord}}_d$ of the source.
--
--   **Formalization Note** Joint almost-everywhere measurability of the output in $(z,x)$ for each instance is a clause, because the expected squared error presupposes it.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Definition 4, p.6; p.12

import Mathlib
import Definitions.Def_RobustFcstAgg_RandRule
import Definitions.Def_RobustFcstAgg_Rule_output
import Definitions.Def_RobustFcstAgg_Rule_HasOrderAgentLE
import Definitions.Def_RobustFcstAgg_InfoStruct_jointLaw
open MeasureTheory

namespace RobustFcstAgg

/-- **Randomized rule with order and agent complexity at most `d`** (the class `A^ord_d`). Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Definition 4, p.6:
"`P` has query, order, or agent complexity at most `d` if the corresponding complexity of `Q` is at most `d` for
`P_Q`-almost every query collection `Q`"; p.12 for the class.

**Formalization Note.** Joint a.e.-measurability of the output is a clause, because the expectation in the loss
presupposes it; a non-measurable output is not an approximator. -/
def RandRule.IsOrderAgentLE {n : ℕ} (R : RandRule n) (d : ℕ) : Prop :=
  (∀ᵐ z ∂(R.P), (R.rule z).HasOrderAgentLE d) ∧
  ∀ D : InfoStruct n,
    AEMeasurable (fun p : R.Z × Signals n => (R.rule p.1).output D p.2) (R.P.prod D.jointLaw)

end RobustFcstAgg


