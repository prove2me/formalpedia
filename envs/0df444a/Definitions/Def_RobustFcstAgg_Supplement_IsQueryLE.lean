-- Prove2me | Definitions.Def_RobustFcstAgg_Supplement_IsQueryLE
-- name    : RobustFcstAgg_Supplement_IsQueryLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:37:46.200221+00:00
-- url     : https://prove2.me/theorems/626d69e6-e8bd-44d9-85eb-99cc600eb7ed
-- title:
--   Randomized DAG-elicitable rules of query complexity at most $d$ (the class $\mathcal A^{\mathrm{qry}}_d$)
-- statement:
--   A randomized aggregation rule $P$ (a random context $Z\sim P$ selecting a deterministic rule $(\mathcal Q_Z,f_Z)$) belongs to the class $\mathcal A^{\mathrm{qry}}_d$ when:
--
--   1. for $P$-almost every context $z$, the realized query collection $\mathcal Q_z$ is DAG-elicitable and has at most $d$ queries, $|\mathcal Q_z|\le d$;
--   2. for every instance $\mathcal D$, the output $f_Z(\mathcal Q_Z)$ is jointly almost-everywhere measurable in the context and the signals.
--
--   No bound on order or agent complexity is imposed. The minimum error over this class is $1-d/n$ (Theorem 3).
--
--   **Formalization Note** DAG-elicitability is the base `IsDAGElicits`, which includes Condition 1 on the variables scored along the DAG's edges and one payment function for all instances. Clause 2 is the same as in the base class $\mathcal A^{\mathrm{ord}}_d$: the expectation in the loss presupposes it.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 4.1, p.11; Definition 4, p.6; Section 2.2, p.5

import Mathlib
import Definitions.Def_RobustFcstAgg_RandRule
import Definitions.Def_RobustFcstAgg_Rule_output
import Definitions.Def_RobustFcstAgg_IsDAGElicits
import Definitions.Def_RobustFcstAgg_InfoStruct_jointLaw
open MeasureTheory

namespace RobustFcstAgg.Supplement

/-- **DAG-elicitable randomized rule of query complexity at most `d`** (the class `A^qry_d`).
Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 4.1, p.11:
"`A^qry_d` denote[s] the set of approximators `A` that are implemented by DAG-elicitable, randomized aggregation rules
restricted to query complexity at most `d`"; Definition 4, p.6 ("`query-c(Q) := |Q|`"; "`P` has query … complexity at most
`d` if the corresponding complexity of `Q` is at most `d` for `P_Q`-almost every query collection `Q`"); Sec. 2.2, p.5 (`P`
is DAG-elicitable if `Q` is DAG-elicitable for `P_Q`-almost every `Q`).

**Formalization Note.** For a.e. context `z`, the realized collection has an eliciting DAG (base `IsDAGElicits`, with
Condition 1) and at most `d` queries. No order or agent bound. Joint a.e.-measurability of the output in (context,
signals) is a clause, exactly as in the base `RandRule.IsOrderAgentLE`: the expectation in the loss presupposes it. -/
def IsQueryLE {n : ℕ} (R : RandRule n) (d : ℕ) : Prop :=
  (∀ᵐ z ∂(R.P), (∃ out : (R.rule z).ι → Finset (Option (R.rule z).ι),
      IsDAGElicits (R.rule z).Q out) ∧ Fintype.card (R.rule z).ι ≤ d) ∧
  ∀ D : InfoStruct n,
    AEMeasurable (fun p : R.Z × Signals n => (R.rule p.1).output D p.2) (R.P.prod D.jointLaw)

end RobustFcstAgg.Supplement


