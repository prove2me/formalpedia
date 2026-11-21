-- Prove2me | Definitions.Def_SourceProof_95eaf7edddd1af971f664384
-- name    : SourceProof_95eaf7edddd1af971f664384
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:08:56.91953+00:00
-- url     : https://prove2.me/theorems/40e98b2d-6950-499f-9faf-0bc2545b0c5f
-- title:
--   LevyStochCalc source module: SourceProof_95eaf7edddd1af971f664384
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.stronglyMeasurable_setIntegral_of_rightCont` comes from the `LevyStochCalc.BSDEJ.DriftLeg` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_cf0436ca36261036186bd5e0

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


theorem _root_.Prove2MeSourceProof.h_95eaf7edddd1af971f664384 (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ.rightCont b)
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) {t : ℝ}
    (ht : 0 ≤ t) :
    StronglyMeasurable[ℱ t] fun ω =>
      (integrablePaths b T).indicator (fun ω => ∫ s in Set.Icc (0 : ℝ) t, b ω s) ω := by
  have hnullc : P (LevyStochCalc.BSDEJ.Solves.integrablePaths b T)ᶜ = 0 := ae_iff.mp (LevyStochCalc.BSDEJ.Solves.ae_mem_integrablePaths hbm hbq)
  have h0 : MeasurableSet[ℱ 0] (LevyStochCalc.BSDEJ.Solves.integrablePaths b T)ᶜ :=
    hnull _ (LevyStochCalc.BSDEJ.Solves.measurableSet_integrablePaths hbm).compl hnullc
  have h1 : MeasurableSet[ℱ 0] (LevyStochCalc.BSDEJ.Solves.integrablePaths b T) := by simpa using h0.compl
  have hgood : MeasurableSet[ℱ t] (LevyStochCalc.BSDEJ.Solves.integrablePaths b T) := ℱ.mono ht _ h1
  have hstep : ∀ n : ℕ, StronglyMeasurable[ℱ t] (LevyStochCalc.BSDEJ.Solves.driftLeg b T (t - 1 / ((n : ℝ) + 1))) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hle : ℱ.rightCont (t - 1 / ((n : ℝ) + 1)) ≤ ℱ t := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le t (by linarith)
    exact ((hbp.stronglyMeasurable_setIntegral measurableSet_Icc Set.Icc_subset_Iic_self
      volume).mono hle).indicator hgood
  have hc : Filter.Tendsto (fun n : ℕ => t - 1 / ((n : ℝ) + 1)) Filter.atTop (nhds t) := by
    have h : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun n : ℕ => t - 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (t - 0)) :=
      tendsto_const_nhds.sub h
    simpa using h2
  have hlim : Filter.Tendsto (fun n : ℕ => LevyStochCalc.BSDEJ.Solves.driftLeg b T (t - 1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds (LevyStochCalc.BSDEJ.Solves.driftLeg b T t)) := by
    rw [tendsto_pi_nhds]
    intro ω
    exact ((_root_.Prove2MeSourceProof.h_cf0436ca36261036186bd5e0 hbz ω).tendsto t).comp hc
  exact stronglyMeasurable_of_tendsto (m := ℱ t) Filter.atTop hstep hlim
end LevyStochCalc.BSDEJ.Solves


