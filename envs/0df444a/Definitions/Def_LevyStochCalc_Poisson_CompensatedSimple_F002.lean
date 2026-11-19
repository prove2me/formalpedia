-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F002
-- name    : LevyStochCalc_Poisson_CompensatedSimple_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:24:04.834213+00:00
-- url     : https://prove2.me/theorems/1f43ac5e-3127-434c-8be6-71b576d39552
-- title:
--   LevyStochCalc source module: LevyStochCalc.Poisson.CompensatedSimple
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Poisson.CompensatedSimple in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Compensated Poisson integral: simple predictable integrands

The simple predictable integrands `φ = ∑_i ξ_i · 1_{(t_i, t_{i+1}] × A_i}` and
their integral `simpleIntegral` against the compensated Poisson measure
`Ñ(dt, de) := N(dt, de) − ν(de) dt`, with the indicator/rectangle bookkeeping
lemmas. The moment identities are in `Poisson/CompensatedMoments.lean`; the
L²-isometry in `Poisson/CompensatedIsometry.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- The double-lintegral of the constant-indicator on `fullRect i` over `[0, T] × E`
equals `c · referenceIntensity ν (fullRect i)`. -/
lemma SimplePredictable.lintegral_indicator_fullRect
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (c : ℝ≥0∞) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (φ.fullRect i).indicator (fun _ : ℝ × E => c) (s, e) ∂ν ∂volume
      = c * LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) := by
  have h_meas_fullRect : MeasurableSet (φ.fullRect i) := by
    unfold SimplePredictable.fullRect
    exact measurableSet_Ioc.prod (φ.A_measurable i)
  have h_t_i_nn : 0 ≤ φ.partition i.castSucc := by
    have : φ.partition 0 ≤ φ.partition i.castSucc :=
      φ.partition_strictMono.monotone (Fin.zero_le _)
    rw [φ.partition_zero] at this
    exact this
  have h_t_i_succ_le_T : φ.partition i.succ ≤ T :=
    le_trans (φ.partition_strictMono.monotone (Fin.le_last _)) φ.partition_le_T
  have h_subset_T :
      Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ) ⊆ Set.Icc (0 : ℝ) T := by
    intro x hx
    exact ⟨h_t_i_nn.trans (le_of_lt hx.1), hx.2.trans h_t_i_succ_le_T⟩
  -- Convert iterated lintegral to product lintegral (Fubini).
  rw [MeasureTheory.lintegral_lintegral
    (f := fun s e => (φ.fullRect i).indicator (fun _ : ℝ × E => c) (s, e))
    (Measurable.indicator measurable_const h_meas_fullRect).aemeasurable]
  -- ∫⁻ z, ind (fullRect i) (fun _ => c) z ∂((volume.restrict [0,T]).prod ν)
  rw [show (fun (z : ℝ × E) => (φ.fullRect i).indicator (fun _ : ℝ × E => c) (z.1, z.2))
        = (φ.fullRect i).indicator (fun _ : ℝ × E => c) from by funext z; rfl]
  rw [MeasureTheory.lintegral_indicator_const h_meas_fullRect]
  -- c * ((volume.restrict (Icc 0 T)).prod ν)(fullRect i)
  -- = c * (volume.restrict (Icc 0 T))(Ioc) * ν(A_i)
  -- = c * volume(Ioc) * ν(A_i)
  -- = c * referenceIntensity ν (fullRect i)
  unfold SimplePredictable.fullRect LevyStochCalc.Poisson.referenceIntensity
  rw [MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.prod_prod]
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  rw [Set.inter_eq_left.mpr h_subset_T]
  have h_subset_Ici :
      Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ) ⊆ Set.Ici (0 : ℝ) := by
    intro x hx; exact h_t_i_nn.trans (le_of_lt hx.1)
  rw [Set.inter_eq_left.mpr h_subset_Ici]
end LevyStochCalc.Poisson.Compensated


