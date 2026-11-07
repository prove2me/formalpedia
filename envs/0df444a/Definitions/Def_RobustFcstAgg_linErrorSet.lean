-- Prove2me | Definitions.Def_RobustFcstAgg_linErrorSet
-- name    : RobustFcstAgg_linErrorSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:57:23.340476+00:00
-- url     : https://prove2.me/theorems/052bde30-2094-409d-bccc-3602d1fbebc5
-- title:
--   Errors of $\mathcal A^{\mathrm{lin}}_d$
-- statement:
--   The set of worst-case errors of deterministic linear intersection rules with coefficients indexed by $1\le|S|\le d$. Its least element is $\min_{A\in\mathcal A^{\mathrm{lin}}_d}\mathrm{error}(A)$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, p.12

import Mathlib
import Definitions.Def_RobustFcstAgg_linRule
import Definitions.Def_RobustFcstAgg_Rule_toRand
import Definitions.Def_RobustFcstAgg_RandRule_error
open scoped ENNReal

namespace RobustFcstAgg

/-- **Errors of `A^lin_d`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, p.12: the errors of the approximators implementable by deterministic linear
intersection rules of order at most `d`. -/
def linErrorSet (n d : ℕ) : Set ℝ≥0∞ :=
  Set.range fun β : InterIndex n d → ℝ => (linRule n d β).toRand.error

end RobustFcstAgg


