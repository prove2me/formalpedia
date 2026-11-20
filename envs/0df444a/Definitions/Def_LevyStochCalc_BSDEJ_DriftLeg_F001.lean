-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_DriftLeg_F001
-- name    : LevyStochCalc_BSDEJ_DriftLeg_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:22:18.850561+00:00
-- url     : https://prove2.me/theorems/a20dd81e-efb8-4e85-b051-f1c040be189c
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.DriftLeg
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.DriftLeg. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

/-- The drift leg of a progressively measurable drift of finite energy is strongly adapted,
provided the filtration contains the `P`-null sets at time `0`. -/
theorem stronglyAdapted_driftLeg (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ b) (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    StronglyAdapted ℱ (driftLeg b T) := by
  intro t
  rcases le_or_gt 0 t with ht | ht
  · have hnullc : P (integrablePaths b T)ᶜ = 0 :=
      ae_iff.mp (ae_mem_integrablePaths hbm hbq)
    have h0 : MeasurableSet[ℱ 0] (integrablePaths b T)ᶜ :=
      hnull _ (measurableSet_integrablePaths hbm).compl hnullc
    have h1 : MeasurableSet[ℱ 0] (integrablePaths b T) := by
      simpa using h0.compl
    have hgood : MeasurableSet[ℱ t] (integrablePaths b T) := ℱ.mono ht _ h1
    have hsm : StronglyMeasurable[ℱ t] fun ω => ∫ s in Set.Icc (0 : ℝ) t, b ω s :=
      hbp.stronglyMeasurable_setIntegral measurableSet_Icc Set.Icc_subset_Iic_self volume
    exact hsm.indicator hgood
  · have heq : driftLeg b T t = fun _ => (0 : ℝ) := by
      funext ω
      by_cases hω : ω ∈ integrablePaths b T
      · rw [driftLeg_of_mem hω t, Set.Icc_eq_empty (not_le.mpr ht), setIntegral_empty]
      · exact driftLeg_of_notMem hω t
    rw [heq]
    exact stronglyMeasurable_const
/-- The drift leg of a progressively measurable drift of finite energy is adapted, provided the
filtration contains the `P`-null sets at time `0`. -/
theorem adapted_driftLeg (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ b) (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    Adapted ℱ (driftLeg b T) := fun t =>
  (stronglyAdapted_driftLeg hbm hbp hbq hnull t).measurable
/-- The drift leg is adapted to the right-continuous filtration. -/
theorem adapted_driftLeg_rightCont (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ b) (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    Adapted ℱ.rightCont (driftLeg b T) := fun t =>
  (adapted_driftLeg hbm hbp hbq hnull t).mono (ℱ.le_rightCont t) le_rfl
end LevyStochCalc.BSDEJ.Solves


