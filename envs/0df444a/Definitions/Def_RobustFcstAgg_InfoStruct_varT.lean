-- Prove2me | Definitions.Def_RobustFcstAgg_InfoStruct_varT
-- name    : RobustFcstAgg_InfoStruct_varT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:44:29.548808+00:00
-- url     : https://prove2.me/theorems/f4e986ae-a069-4f08-9a6f-3324d0c17173
-- title:
--   $\mathrm{Var}_{\mathcal D}(X_T)$
-- statement:
--   The variance of the signal $X_T$ under $\mathcal D$, namely $\mathrm{Var}_{\mathcal D}(X_T)=\mathbb E_{\mathcal D}[X_T^2]$, since the signals have mean zero.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.3, p.7

import Mathlib
import Definitions.Def_RobustFcstAgg_InfoStruct
open MeasureTheory

namespace RobustFcstAgg

/-- **`Var_D(X_T)`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.3, p.7: "`Var_D(X_T) := E_D[X_T²]`". -/
noncomputable def InfoStruct.varT {n : ℕ} (D : InfoStruct n) (T : Subs n) : ℝ :=
  ∫ x, x ^ 2 ∂D.law T

end RobustFcstAgg


