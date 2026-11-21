-- Prove2me | Definitions.Def_SourceProof_cf0436ca36261036186bd5e0
-- name    : SourceProof_cf0436ca36261036186bd5e0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:24:00.443307+00:00
-- url     : https://prove2.me/theorems/624894d9-615a-48ab-93cf-7f286ff82d34
-- title:
--   LevyStochCalc source module: SourceProof_cf0436ca36261036186bd5e0
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.continuous_driftLeg` comes from the `LevyStochCalc.BSDEJ.DriftLeg` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_DriftLeg_F000

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


theorem _root_.Prove2MeSourceProof.h_cf0436ca36261036186bd5e0 (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0) (ω : Ω) :
    Continuous fun t => driftLeg b T t ω := by
  by_cases hω : ω ∈ LevyStochCalc.BSDEJ.Solves.integrablePaths b T
  · have hind : Integrable ((Set.Icc (0 : ℝ) T).indicator (b ω)) volume :=
      (integrable_indicator_iff measurableSet_Icc).mpr hω
    have hint : Integrable (b ω) volume := by
      refine hind.congr (Filter.Eventually.of_forall fun s => ?_)
      by_cases hs : s ∈ Set.Icc (0 : ℝ) T
      · rw [Set.indicator_of_mem hs]
      · rw [Set.indicator_of_notMem hs, hbz ω s hs]
    have heq : (fun t => LevyStochCalc.BSDEJ.Solves.driftLeg b T t ω) = fun t => ∫ s in (0 : ℝ)..t, b ω s := by
      funext t
      rw [LevyStochCalc.BSDEJ.Solves.driftLeg_of_mem hω t, LevyStochCalc.BSDEJ.Solves.setIntegral_Icc_eq_intervalIntegral hbz ω t]
    rw [heq]
    exact hint.continuous_primitive 0
  · have heq : (fun t => LevyStochCalc.BSDEJ.Solves.driftLeg b T t ω) = fun _ => (0 : ℝ) := by
      funext t
      exact LevyStochCalc.BSDEJ.Solves.driftLeg_of_notMem hω t
    rw [heq]
    exact continuous_const
end LevyStochCalc.BSDEJ.Solves


