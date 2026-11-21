-- Prove2me | Definitions.Def_SourceProof_846c5a27154f5e7706e6988e
-- name    : SourceProof_846c5a27154f5e7706e6988e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:22:08.587121+00:00
-- url     : https://prove2.me/theorems/ce7aa8c9-19e2-4c78-8b9f-43ee4e491151
-- title:
--   LevyStochCalc source module: SourceProof_846c5a27154f5e7706e6988e
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.measurable_uncurry_driftLeg` comes from the `LevyStochCalc.BSDEJ.DriftLeg` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_846c5a27154f5e7706e6988e (hbm : Measurable (Function.uncurry b)) :
    Measurable (Function.uncurry (driftLeg b T)) := by
  have hset : MeasurableSet {q : (ℝ × Ω) × ℝ | q.2 ∈ Set.Icc (0 : ℝ) q.1.1} := by
    have heq : {q : (ℝ × Ω) × ℝ | q.2 ∈ Set.Icc (0 : ℝ) q.1.1}
        = {q : (ℝ × Ω) × ℝ | (0 : ℝ) ≤ q.2} ∩ {q : (ℝ × Ω) × ℝ | q.2 ≤ q.1.1} := by
      ext q
      exact Set.mem_Icc
    rw [heq]
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.fst)
  have hb : Measurable fun q : (ℝ × Ω) × ℝ => b q.1.2 q.2 :=
    hbm.comp (measurable_fst.snd.prodMk measurable_snd)
  have hF : StronglyMeasurable fun q : (ℝ × Ω) × ℝ =>
      (Set.Icc (0 : ℝ) q.1.1).indicator (b q.1.2) q.2 := by
    have heq : (fun q : (ℝ × Ω) × ℝ => (Set.Icc (0 : ℝ) q.1.1).indicator (b q.1.2) q.2)
        = {q : (ℝ × Ω) × ℝ | q.2 ∈ Set.Icc (0 : ℝ) q.1.1}.indicator
          fun q => b q.1.2 q.2 := by
      funext q
      by_cases hq : q.2 ∈ Set.Icc (0 : ℝ) q.1.1
      · have hq' : q ∈ {q : (ℝ × Ω) × ℝ | q.2 ∈ Set.Icc (0 : ℝ) q.1.1} := hq
        rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq']
      · have hq' : q ∉ {q : (ℝ × Ω) × ℝ | q.2 ∈ Set.Icc (0 : ℝ) q.1.1} := hq
        rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq']
    rw [heq]
    exact (hb.indicator hset).stronglyMeasurable
  have hint : StronglyMeasurable fun p : ℝ × Ω => ∫ s in Set.Icc (0 : ℝ) p.1, b p.2 s := by
    have heq : (fun p : ℝ × Ω => ∫ s in Set.Icc (0 : ℝ) p.1, b p.2 s)
        = fun p : ℝ × Ω => ∫ s, (Set.Icc (0 : ℝ) p.1).indicator (b p.2) s := by
      funext p
      rw [integral_indicator measurableSet_Icc]
    rw [heq]
    exact hF.integral_prod_right'
  have hsnd : MeasurableSet {p : ℝ × Ω | p.2 ∈ LevyStochCalc.BSDEJ.Solves.integrablePaths b T} :=
    measurable_snd (LevyStochCalc.BSDEJ.Solves.measurableSet_integrablePaths hbm)
  have heq : Function.uncurry (LevyStochCalc.BSDEJ.Solves.driftLeg b T)
      = {p : ℝ × Ω | p.2 ∈ LevyStochCalc.BSDEJ.Solves.integrablePaths b T}.indicator
        fun p => ∫ s in Set.Icc (0 : ℝ) p.1, b p.2 s := by
    funext p
    by_cases hp : p.2 ∈ LevyStochCalc.BSDEJ.Solves.integrablePaths b T
    · have hp' : p ∈ {p : ℝ × Ω | p.2 ∈ LevyStochCalc.BSDEJ.Solves.integrablePaths b T} := hp
      rw [Set.indicator_of_mem hp']
      exact LevyStochCalc.BSDEJ.Solves.driftLeg_of_mem hp p.1
    · have hp' : p ∉ {p : ℝ × Ω | p.2 ∈ LevyStochCalc.BSDEJ.Solves.integrablePaths b T} := hp
      rw [Set.indicator_of_notMem hp']
      exact LevyStochCalc.BSDEJ.Solves.driftLeg_of_notMem hp p.1
  rw [heq]
  exact hint.measurable.indicator hsnd
end LevyStochCalc.BSDEJ.Solves


