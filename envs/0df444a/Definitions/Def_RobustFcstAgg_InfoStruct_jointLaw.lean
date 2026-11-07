-- Prove2me | Definitions.Def_RobustFcstAgg_InfoStruct_jointLaw
-- name    : RobustFcstAgg_InfoStruct_jointLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:44:39.755513+00:00
-- url     : https://prove2.me/theorems/8da9ce9f-badf-4a07-8ce2-4914613c0d2e
-- title:
--   Joint law of the signals
-- statement:
--   Under an instance $\mathcal D$ the signals are independent, so the joint law of $(X_T)_T$ is the product measure $\bigotimes_T\mathcal D_T$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Section 2.3, p.7

import Mathlib
import Definitions.Def_RobustFcstAgg_Signals
import Definitions.Def_RobustFcstAgg_InfoStruct
open MeasureTheory

namespace RobustFcstAgg

/-- **Joint law of the signals.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Sec. 2.3, p.7: the signals are independent, so their joint
law is the product of the `D_T`. -/
noncomputable def InfoStruct.jointLaw {n : ℕ} (D : InfoStruct n) : Measure (Signals n) :=
  Measure.pi D.law

instance InfoStruct.instIsProbabilityMeasureJointLaw {n : ℕ} (D : InfoStruct n) :
    IsProbabilityMeasure D.jointLaw := by
  unfold InfoStruct.jointLaw; infer_instance

end RobustFcstAgg


