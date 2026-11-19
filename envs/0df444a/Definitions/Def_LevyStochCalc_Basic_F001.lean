-- Prove2me | Definitions.Def_LevyStochCalc_Basic_F001
-- name    : LevyStochCalc_Basic_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:46:46.626423+00:00
-- url     : https://prove2.me/theorems/2f2eb0cd-7bcf-4faf-9bc4-2907f43c2412
-- title:
--   LevyStochCalc source module: LevyStochCalc.Basic
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Basic in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# LevyStochCalc.Basic

Common imports plus small L² helper lemmas shared across the library:
`eLpNorm` reverse-triangle / difference bounds and L²-continuity (Bochner-L²
limit) lemmas in the plain, Brownian, and compensated-Poisson integrand shapes.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc

/-- **Bridge: nested-lintegral-of-squared-norm = `eLpNorm²` on (binary) product measure.**

For any `ℝ`-valued measurable `h : α × β → ℝ` and SFinite `μ`, `ν`,
`∫⁻ x, ∫⁻ y, ‖h (x, y)‖₊² ∂ν ∂μ = eLpNorm h 2 (μ.prod ν) ^ (2:ℝ)`.

Tonelli + `eLpNorm_nnreal_pow_eq_lintegral` (instantiated at `p = 2`). -/
lemma lintegral_sq_eq_eLpNorm_sq_on_prod
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (h : α × β → ℝ) (hh : Measurable h) :
    ∫⁻ x, ∫⁻ y, (‖h (x, y)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂μ
      = MeasureTheory.eLpNorm h 2 (μ.prod ν) ^ (2 : ℝ) := by
  set μν := μ.prod ν with hμν
  have h_aem_sq : AEMeasurable
      (fun p : α × β => (‖h p‖₊ : ℝ≥0∞) ^ 2) μν :=
    (hh.enorm.pow_const 2).aemeasurable
  -- Tonelli on the squared integrand.
  have h_Tonelli :
      ∫⁻ x, ∫⁻ y, (‖h (x, y)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂μ
        = ∫⁻ p, (‖h p‖₊ : ℝ≥0∞) ^ 2 ∂μν := by
    rw [MeasureTheory.lintegral_prod _ h_aem_sq]
  rw [h_Tonelli]
  -- Bridge: ∫⁻ p, (‖h p‖₊ : ℝ≥0∞)^2 ∂μν = eLpNorm h 2 μν ^ (2:ℝ).
  have h_pow_lemma := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
    (μ := μν) (p := (2 : NNReal)) (f := h)
    (by norm_num : (2 : NNReal) ≠ 0)
  have h_two_R : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_num
  have h_two_ENNReal : ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) := by simp
  rw [h_two_ENNReal, h_two_R] at h_pow_lemma
  rw [h_pow_lemma]
  refine lintegral_congr (fun p => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rfl
end LevyStochCalc


