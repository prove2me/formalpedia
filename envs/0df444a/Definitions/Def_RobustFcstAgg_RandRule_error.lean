-- Prove2me | Definitions.Def_RobustFcstAgg_RandRule_error
-- name    : RobustFcstAgg_RandRule_error
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:54:15.236815+00:00
-- url     : https://prove2.me/theorems/6f1664f4-e27d-489a-b2be-c2297c7562bf
-- title:
--   Worst-case error (Eq. (2))
-- statement:
--   The worst-case error of an approximator in the partial information model is
--   $$\mathrm{error}(A)=\sup_{\mathcal D}\frac{L_{\mathcal D}(A)}{\mathrm{Var}_{\mathcal D}(Y)}.$$
--   This is the form (2) that the source derives from (1) for this model, where $L_{\mathcal D}(A^*)=0$.
--
--   **Formalization Note** Valued in $[0,\infty]$. The rule is fixed first, then the supremum over instances is taken.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Eq. (2), p.8

import Mathlib
import Definitions.Def_RobustFcstAgg_RandRule_loss
import Definitions.Def_RobustFcstAgg_InfoStruct_varY
open MeasureTheory
open scoped ENNReal

namespace RobustFcstAgg

/-- **Worst-case error.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Eq. (2), p.8: "`error(A) = sup_D L_D(A) / Var_D(Y)`". The source derives (2) from (1), p.4,
for the partial information model, where `L_D(A*) = 0`.

**Formalization Note.** In `ℝ≥0∞`. The rule is fixed first, then the supremum over `D` is taken. `D.varY > 0` for every
`D` by the clause `InfoStruct.nondeg`, so there is no division by zero. -/
noncomputable def RandRule.error {n : ℕ} (R : RandRule n) : ℝ≥0∞ :=
  ⨆ D : InfoStruct n, R.loss D / ENNReal.ofReal D.varY

end RobustFcstAgg


