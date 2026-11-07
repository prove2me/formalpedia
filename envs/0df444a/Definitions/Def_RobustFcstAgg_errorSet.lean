-- Prove2me | Definitions.Def_RobustFcstAgg_errorSet
-- name    : RobustFcstAgg_errorSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:01:03.744+00:00
-- url     : https://prove2.me/theorems/21b5386e-627e-4c73-8cb4-19f404492f85
-- title:
--   Errors of $\mathcal A^{\mathrm{ord}}_d$
-- statement:
--   The set of worst-case errors of randomized rules of order and agent complexity at most $d$. Its least element is $\min_{A\in\mathcal A^{\mathrm{ord}}_d}\mathrm{error}(A)$.
--
--   **Formalization Note** The error of an approximator depends only on the almost-sure class of the rule's output, so the minimum over approximators is the minimum over rules.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, p.12

import Mathlib
import Definitions.Def_RobustFcstAgg_RandRule_IsOrderAgentLE
import Definitions.Def_RobustFcstAgg_RandRule_error
open scoped ENNReal

namespace RobustFcstAgg

/-- **Errors of `A^ord_d`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, p.12: the errors of the approximators implementable by randomized aggregation rules
of agent and order complexity at most `d`.

**Formalization Note.** `error(A)` depends only on the a.s. class of the rule's output, so
`min_{A ∈ A^ord_d} error(A)` is the least element of this set. -/
def errorSet (n d : ℕ) : Set ℝ≥0∞ :=
  {e | ∃ R : RandRule n, R.IsOrderAgentLE d ∧ R.error = e}

end RobustFcstAgg


