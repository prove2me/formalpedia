-- Prove2me | Definitions.Def_RobustFcstAgg_Rule_HasOrderAgentLE
-- name    : RobustFcstAgg_Rule_HasOrderAgentLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:55:58.56981+00:00
-- url     : https://prove2.me/theorems/d8b706e4-acda-4db2-ac4f-45d320c008e6
-- title:
--   Rule of order and agent complexity at most $d$
-- statement:
--   A rule has **order and agent complexity at most $d$** if some DAG eliciting $\mathcal Q$ has order at most $d$ and some DAG eliciting $\mathcal Q$ has agent complexity at most $d$. The bounds are imposed separately and "may be witnessed by different elicitation DAGs" (p.12).
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Definition 4, p.6; p.12

import Mathlib
import Definitions.Def_RobustFcstAgg_Rule
import Definitions.Def_RobustFcstAgg_IsDAGElicits
import Definitions.Def_RobustFcstAgg_OrderLE
import Definitions.Def_RobustFcstAgg_AgentLE

namespace RobustFcstAgg

/-- **Order and agent complexity at most `d`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Definition 4, p.6, and p.12: "We impose bounds on agent and
order complexity separately, so the two bounds may be witnessed by different elicitation DAGs."

**Formalization Note.** `order-c(𝒬) ≤ d` and `agent-c(𝒬) ≤ d` are read as existence of an eliciting DAG meeting the
bound, since the `min` in Definition 4 runs over a set of naturals. Two possibly different DAGs. -/
def Rule.HasOrderAgentLE {n : ℕ} (R : Rule n) (d : ℕ) : Prop :=
  (∃ out : R.ι → Finset (Option R.ι), IsDAGElicits R.Q out ∧ OrderLE out d) ∧
  (∃ out : R.ι → Finset (Option R.ι), IsDAGElicits R.Q out ∧ AgentLE R.Q out d)

end RobustFcstAgg


