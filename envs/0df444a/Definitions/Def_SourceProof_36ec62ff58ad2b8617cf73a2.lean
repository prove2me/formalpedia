-- Prove2me | Definitions.Def_SourceProof_36ec62ff58ad2b8617cf73a2
-- name    : SourceProof_36ec62ff58ad2b8617cf73a2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:28:29.846764+00:00
-- url     : https://prove2.me/theorems/b1c10a4d-8d8b-4f5b-acf0-83a0e5f8789f
-- title:
--   LevyStochCalc source module: SourceProof_36ec62ff58ad2b8617cf73a2
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_window_abs_sub_le` comes from the `LevyStochCalc.Brownian.ItoProcessWindow` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_3ef6041059753d947ebe758f

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Window averages of an Itô process's increments

Freezing a continuous version of an Itô process at the left endpoint of a window and integrating
the resulting displacement over the window and the sample space gives a bound of order
`(v − u)·√(v − u)`, which is what makes the grid Riemann sums of the Itô formula converge.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_window_abs_sub_le` — the `L¹` window bound.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_window_sq_sub_le` — the `L²` window bound.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Window

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_36ec62ff58ad2b8617cf73a2
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∫⁻ ω, ∫⁻ s in Set.Ioc u v, ENNReal.ofReal |X s ω - X u ω| ∂volume ∂P
      ≤ ENNReal.ofReal ((v - u) * (B * (v - u) + C * Real.sqrt (v - u))) := by
  have hjoint : Measurable (Function.uncurry fun ω s => ENNReal.ofReal |X s ω - X u ω|) :=
    (ENNReal.measurable_ofReal.comp
      ((h.measurable_uncurry.sub ((h.measurable u).comp measurable_fst)).abs))
  have hswap := MeasureTheory.lintegral_lintegral_swap
    (μ := P) (ν := volume.restrict (Set.Ioc u v))
    (f := fun ω s => ENNReal.ofReal |X s ω - X u ω|) hjoint.aemeasurable
  rw [hswap]
  have hbnd : (0 : ℝ) ≤ B * (v - u) + C * Real.sqrt (v - u) := by
    have := sub_nonneg.mpr huv
    positivity
  have hinner : ∀ s ∈ Set.Ioc u v, ∫⁻ ω, ENNReal.ofReal |X s ω - X u ω| ∂P
      ≤ ENNReal.ofReal (B * (v - u) + C * Real.sqrt (v - u)) := by
    intro s hs
    obtain ⟨hint, hle⟩ := (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_3ef6041059753d947ebe758f p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB hu hs.1.le
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (hle.trans ?_)
    have hsu : (0 : ℝ) ≤ s - u := sub_nonneg.mpr hs.1.le
    have hsv : s - u ≤ v - u := by linarith [hs.2]
    gcongr
  calc ∫⁻ s in Set.Ioc u v, ∫⁻ ω, ENNReal.ofReal |X s ω - X u ω| ∂P ∂volume
      ≤ ∫⁻ _s in Set.Ioc u v, ENNReal.ofReal (B * (v - u) + C * Real.sqrt (v - u)) ∂volume :=
        MeasureTheory.setLIntegral_mono' measurableSet_Ioc hinner
    _ = ENNReal.ofReal (B * (v - u) + C * Real.sqrt (v - u)) * ENNReal.ofReal (v - u) := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc]
    _ = ENNReal.ofReal ((v - u) * (B * (v - u) + C * Real.sqrt (v - u))) := by
        rw [← ENNReal.ofReal_mul hbnd, mul_comm]
end Window

end LevyStochCalc.Brownian.Ito


