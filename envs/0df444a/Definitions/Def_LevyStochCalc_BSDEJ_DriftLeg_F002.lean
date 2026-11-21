-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_DriftLeg_F002
-- name    : LevyStochCalc_BSDEJ_DriftLeg_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:09:56.8622+00:00
-- url     : https://prove2.me/theorems/ec727a09-a7ff-48f4-8ebe-545a2e181d0d
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.DriftLeg
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.DriftLeg. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_DriftLeg_F000
import Definitions.Def_SourceProof_95eaf7edddd1af971f664384

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The drift leg of a Picard iterate

For a drift `b : Ω → ℝ → ℝ` of finite energy on the horizon `[0, T]` and vanishing off it, the
drift leg is the primitive `t ↦ ∫_{[0, t]} b ω s ds`, restricted to the sample points on which
`b ω` is integrable over `[0, T]` and set to `0` elsewhere. That restriction is a `P`-conull set,
so the drift leg is a version of the raw primitive, and on it every path is the primitive of a
globally integrable function, hence continuous.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.integrablePaths` — the sample points whose drift path is integrable
  over the horizon.
* `LevyStochCalc.BSDEJ.Solves.driftLeg` — the primitive of the drift, cut to those sample points.

## Main statements

* `driftLeg_ae_eq` — the drift leg is a version of the raw primitive.
* `setIntegral_Icc_eq_intervalIntegral` — the integral over `[0, t]` is the interval integral
  from `0` to `t`, for every real `t`.
* `continuous_driftLeg` — every path of the drift leg is continuous.
* `stronglyAdapted_driftLeg`, `adapted_driftLeg` — the drift leg is adapted to the filtration of
  the drift.
* `adapted_driftLeg_of_rightCont` — the drift leg is adapted to the filtration already when the
  drift is progressive for the right-continuous filtration.
* `measurable_uncurry_driftLeg` — the drift leg is jointly measurable in time and sample point.
* `driftLeg_sub_ae` — the drift leg at the horizon splits at an intermediate time.
* `lintegral_biSup_sq_driftLeg_lt_top` — the drift leg has finite `S²` seminorm.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {b : Ω → ℝ → ℝ} {T : ℝ}

/-! ### The paths on which the drift is integrable -/

/-! ### The drift leg -/

/-- The drift leg of a drift of finite energy that vanishes off the horizon and is
progressively measurable for the right-continuous filtration is adapted to the filtration
itself, provided the filtration contains the `P`-null sets at time `0`. -/
theorem adapted_driftLeg_of_rightCont (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ.rightCont b)
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    Adapted ℱ (driftLeg b T) := by
  intro t
  rcases le_or_gt 0 t with ht | ht
  · exact (_root_.Prove2MeSourceProof.h_95eaf7edddd1af971f664384 hbm hbp hbz hbq hnull ht).measurable
  · have heq : driftLeg b T t = fun _ => (0 : ℝ) := by
      funext ω
      by_cases hω : ω ∈ integrablePaths b T
      · rw [driftLeg_of_mem hω t, Set.Icc_eq_empty (not_le.mpr ht), setIntegral_empty]
      · exact driftLeg_of_notMem hω t
    rw [heq]
    exact measurable_const
/-- The drift leg of a drift progressively measurable for the right-continuous filtration is
adapted to that filtration. -/
theorem adapted_driftLeg_rightCont_of_rightCont (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ.rightCont b)
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    Adapted ℱ.rightCont (driftLeg b T) := fun t =>
  (adapted_driftLeg_of_rightCont hbm hbp hbz hbq hnull t).mono (ℱ.le_rightCont t) le_rfl
end LevyStochCalc.BSDEJ.Solves


