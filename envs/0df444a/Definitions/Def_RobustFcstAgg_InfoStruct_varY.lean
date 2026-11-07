-- Prove2me | Definitions.Def_RobustFcstAgg_InfoStruct_varY
-- name    : RobustFcstAgg_InfoStruct_varY
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:56.063211+00:00
-- url     : https://prove2.me/theorems/2b41a598-6237-483d-9572-8cd0b741b10d
-- title:
--   $\mathrm{Var}_{\mathcal D}(Y)=\sum_T\mathrm{Var}_{\mathcal D}(X_T)$
-- statement:
--   The variance of the target, $\mathrm{Var}_{\mathcal D}(Y)=\sum_T\mathrm{Var}_{\mathcal D}(X_T)$. It is the denominator of the worst-case error, and is positive for every instance.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Eq. (2), p.8

import Mathlib
import Definitions.Def_RobustFcstAgg_InfoStruct_varT

namespace RobustFcstAgg

/-- **`Var_D(Y) = Σ_T Var_D(X_T)`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Eq. (2), p.8: the denominator of the error. -/
noncomputable def InfoStruct.varY {n : ℕ} (D : InfoStruct n) : ℝ :=
  ∑ T, D.varT T

end RobustFcstAgg


