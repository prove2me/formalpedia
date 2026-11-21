-- Prove2me | Definitions.Def_SourceProof_5e84cb76e3723bb35ee92ba4
-- name    : SourceProof_5e84cb76e3723bb35ee92ba4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:18:39.965258+00:00
-- url     : https://prove2.me/theorems/3a429502-1b44-4d3b-b02f-f49e50d61d12
-- title:
--   LevyStochCalc source module: SourceProof_5e84cb76e3723bb35ee92ba4
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_abs_add_pow_three_le` comes from the `LevyStochCalc.Brownian.ItoFormulaGrid` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_5e84cb76e3723bb35ee92ba4 {P : Measure Ω} {u v : Ω → ℝ}
    (hu : MeasureTheory.Integrable (fun ω => |u ω| ^ 3) P)
    (hv : MeasureTheory.Integrable (fun ω => |v ω| ^ 3) P)
    (huv : MeasureTheory.Integrable (fun ω => |u ω + v ω| ^ 3) P) :
    ∫ ω, |u ω + v ω| ^ 3 ∂P ≤ 4 * ((∫ ω, |u ω| ^ 3 ∂P) + ∫ ω, |v ω| ^ 3 ∂P) := by
  have hpt : ∀ ω : Ω, |u ω + v ω| ^ 3 ≤ 4 * (|u ω| ^ 3 + |v ω| ^ 3) := by
    intro ω
    have h3 : |u ω + v ω| ^ 3 ≤ (|u ω| + |v ω|) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) 3
    have h2 : (|u ω| + |v ω|) ^ 3 ≤ 4 * (|u ω| ^ 3 + |v ω| ^ 3) :=
      LevyStochCalc.Brownian.Ito.add_pow_three_le_four (abs_nonneg _) (abs_nonneg _)
    linarith
  calc ∫ ω, |u ω + v ω| ^ 3 ∂P ≤ ∫ ω, 4 * (|u ω| ^ 3 + |v ω| ^ 3) ∂P :=
        MeasureTheory.integral_mono huv ((hu.add hv).const_mul 4) hpt
    _ = 4 * ((∫ ω, |u ω| ^ 3 ∂P) + ∫ ω, |v ω| ^ 3 ∂P) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hu hv]
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


