-- Prove2me | Definitions.Def_RobustFcstAgg_InfoStruct_restLaw
-- name    : RobustFcstAgg_InfoStruct_restLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:18.987194+00:00
-- url     : https://prove2.me/theorems/77734e64-36dd-498a-b00d-ab84c860d35e
-- title:
--   Law of the signals hidden from expert $i$
-- statement:
--   The law of the signals hidden from expert $i$ under $\mathcal D$: the product of the $\mathcal D_T$ over $T\not\ni i$. By independence it is also their conditional law given $S_i$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.3, p.7

import Mathlib
import Definitions.Def_RobustFcstAgg_InfoStruct
import Definitions.Def_RobustFcstAgg_Rest
open MeasureTheory

namespace RobustFcstAgg

/-- **Law of the signals hidden from expert `i`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.3, p.7: the product of the `D_T` over
`T ∌ i`. By independence it is also the conditional law of those signals given `S_i`. -/
noncomputable def InfoStruct.restLaw {n : ℕ} (D : InfoStruct n) (i : Fin n) :
    Measure (Rest i → ℝ) :=
  Measure.pi fun T : Rest i => D.law T.1

end RobustFcstAgg


