-- Prove2me | Definitions.Def_SourceProof_328d6eb72effc016d76dc016
-- name    : SourceProof_328d6eb72effc016d76dc016
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:21:08.326476+00:00
-- url     : https://prove2.me/theorems/bc49da29-21d6-4bb2-92d4-d742ab8d359e
-- title:
--   LevyStochCalc source module: SourceProof_328d6eb72effc016d76dc016
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.lintegral_biSup_sq_driftLeg_lt_top` comes from the `LevyStochCalc.BSDEJ.DriftLeg` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_328d6eb72effc016d76dc016 (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
  have key : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖LevyStochCalc.BSDEJ.Solves.driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2)
      ≤ ENNReal.ofReal T * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    by_cases hω : ω ∈ LevyStochCalc.BSDEJ.Solves.integrablePaths b T
    · have hslice : Measurable (b ω) := hbm.comp (measurable_const.prodMk measurable_id)
      calc (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖LevyStochCalc.BSDEJ.Solves.driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2)
          = ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖∫ s in Set.Icc (0 : ℝ) t, b ω s‖₊ : ℝ≥0∞) ^ 2 := by
            simp_rw [LevyStochCalc.BSDEJ.Solves.driftLeg_of_mem hω]
        _ ≤ (∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ∂volume) ^ 2 :=
            LevyStochCalc.BSDEJ.SupBound.biSup_sq_setIntegral_le b T ω
        _ ≤ ENNReal.ofReal T * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
            _root_.Prove2MeSourceProof.h_d4d30e0975338aead626e008 T
              hslice.aestronglyMeasurable.enorm
    · simp [LevyStochCalc.BSDEJ.Solves.driftLeg_of_notMem hω]
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖LevyStochCalc.BSDEJ.Solves.driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal T
          * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P := lintegral_mono key
    _ = ENNReal.ofReal T * LevyStochCalc.Brownian.Ito.energy P T b :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbq.lt_top
end LevyStochCalc.BSDEJ.Solves


