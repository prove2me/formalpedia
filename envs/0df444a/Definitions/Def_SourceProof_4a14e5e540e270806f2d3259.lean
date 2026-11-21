-- Prove2me | Definitions.Def_SourceProof_4a14e5e540e270806f2d3259
-- name    : SourceProof_4a14e5e540e270806f2d3259
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:18:36.476191+00:00
-- url     : https://prove2.me/theorems/a45d4cfa-7b4c-420b-9c9d-92e200e1e52b
-- title:
--   LevyStochCalc source module: SourceProof_4a14e5e540e270806f2d3259
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.lintegral_sq_sub_le_of_bound` comes from the `LevyStochCalc.Brownian.ItoFormulaGrid` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcess_F000
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The uniform grid and the third-moment remainder

The uniform partition of `[0, T]` into `m` cells, and the bound it gives for the sum of third
absolute moments of the increments of an Itô process — the size of the Taylor remainder in
Itô's formula.

## Main statements

* `LevyStochCalc.Brownian.Ito.unifGrid` — the uniform grid on `[0, T]`.
* `LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid` — the simple integrand carried by
  the uniform grid.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_sub_pow_three_le` — the sum of third absolute
  moments of the Itô-integral increments across the grid, of order `m^{-1/2}`.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_itoIncrement_pow_three_le` — the same for the
  increments of a full Itô process, drift included.
* `LevyStochCalc.Brownian.Ito.tendsto_riemann_weighted_unifGrid` — the Riemann sums of a
  continuous weight against a bounded density converge as the grid refines.
* `LevyStochCalc.Brownian.Ito.exists_unifGrid_cell` — every time in `(0, T]` lies in a cell.
* `LevyStochCalc.Brownian.Ito.abs_ofUnifGrid_eval_sub_le` — the grid step weight is within the
  weight's modulus of continuity at the mesh.
* `LevyStochCalc.Brownian.Ito.lintegral_sq_sub_le_of_bound` — a uniform pathwise bound on
  `(0, T]` gives the `L²` distance over the window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section ThirdMomentSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end ThirdMomentSum


theorem _root_.Prove2MeSourceProof.h_4a14e5e540e270806f2d3259 {P : Measure Ω} [IsProbabilityMeasure P]
    (u v : Ω → ℝ → ℝ) {ε T : ℝ} (hε0 : 0 ≤ ε)
    (hbound : ∀ (ω : Ω), ∀ s ∈ Set.Ioc (0 : ℝ) T, |u ω s - v ω s| ≤ ε) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (ε ^ 2 * T) := by
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
      ≤ ENNReal.ofReal (ε ^ 2 * T) := by
    intro ω
    have hset : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
        = ∫⁻ s in Set.Ioc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
      by rw [MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioc_ae_eq_Icc)]
    rw [hset]
    have hptw : ∀ s ∈ Set.Ioc (0 : ℝ) T,
        (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (ε ^ 2) := by
      intro s hs
      have h1 : (‖u ω s - v ω s‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_eq_coe_nnreal hε0]
        refine ENNReal.coe_le_coe.mpr ?_
        rw [← NNReal.coe_le_coe]
        simpa [Real.norm_eq_abs] using hbound ω s hs
      calc (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal ε ^ 2 := pow_le_pow_left' h1 2
        _ = ENNReal.ofReal (ε ^ 2) := (ENNReal.ofReal_pow hε0 2).symm
    calc ∫⁻ s in Set.Ioc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
        ≤ ∫⁻ _s in Set.Ioc (0 : ℝ) T, ENNReal.ofReal (ε ^ 2) ∂volume :=
          MeasureTheory.setLIntegral_mono' measurableSet_Ioc hptw
      _ = ENNReal.ofReal (ε ^ 2) * volume (Set.Ioc (0 : ℝ) T) := by
          rw [MeasureTheory.setLIntegral_const]
      _ = ENNReal.ofReal (ε ^ 2 * T) := by
          rw [Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ω : Ω, ENNReal.ofReal (ε ^ 2 * T) ∂P := lintegral_mono hinner
    _ = ENNReal.ofReal (ε ^ 2 * T) := by simp
section RiemannLimit

end RiemannLimit

section ItoIncrement

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end ItoIncrement

end LevyStochCalc.Brownian.Ito


