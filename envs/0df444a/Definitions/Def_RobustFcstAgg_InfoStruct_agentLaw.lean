-- Prove2me | Definitions.Def_RobustFcstAgg_InfoStruct_agentLaw
-- name    : RobustFcstAgg_InfoStruct_agentLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:46:58.432717+00:00
-- url     : https://prove2.me/theorems/e15920a2-aa7a-441b-982e-93e8bffb4f3e
-- title:
--   Law of $S_i$
-- statement:
--   The law of the signal $S_i$ of expert $i$ under $\mathcal D$: the product of the $\mathcal D_T$ over $T\ni i$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.3, p.7

import Mathlib
import Definitions.Def_RobustFcstAgg_InfoStruct
import Definitions.Def_RobustFcstAgg_AgentSig
open MeasureTheory

namespace RobustFcstAgg

/-- **Law of `S_i`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.3, p.7: the product of the `D_T` over `T ∋ i`. -/
noncomputable def InfoStruct.agentLaw {n : ℕ} (D : InfoStruct n) (i : Fin n) :
    Measure (AgentSig i → ℝ) :=
  Measure.pi fun T : AgentSig i => D.law T.1

end RobustFcstAgg


