-- Prove2me | Definitions.Def_SourceProof_9ba9941dfe7d03e124bfe576
-- name    : SourceProof_9ba9941dfe7d03e124bfe576
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:25:07.666731+00:00
-- url     : https://prove2.me/theorems/ab6c5057-e1b5-4f9c-8e25-dd33ddd2a4e7
-- title:
--   LevyStochCalc source module: SourceProof_9ba9941dfe7d03e124bfe576
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.SupBound.lintegral_biSup_sq_const_add_add_add_lt_top` comes from the `LevyStochCalc.BSDEJ.SupBound` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The `S²` norm of a sum of a constant, two martingales and a drift

The solution space `S²` of a backward equation asks for
`∫⁻ ω, ⨆ t ∈ [0, T], ‖Y t ω‖ₑ² ∂μ < ⊤`, a supremum over the window taken *inside* the square,
while Doob's `L²` maximal inequality
(`LevyStochCalc.Probability.lintegral_iSup_sq_le_of_martingale`) is stated with the square
outside a supremum over the subtype `↥(Set.Icc 0 T)`. The two shapes agree, because squaring
commutes with suprema in `ℝ≥0∞`, and the resulting bound is stable under the decomposition
`Y = c + M₁ + M₂ + A` of a Picard iterate into a constant, two stochastic integrals and a
time integral of the generator.

## Main statements

* `biSup_sq_eq_iSup_subtype_sq` — the two shapes of the squared supremum over `[0, T]` agree.
* `lintegral_biSup_sq_le_of_martingale` — Doob's `L²` maximal inequality in the `S²` shape.
* `lintegral_biSup_sq_add_le` — the `S²` seminorm is subadditive up to a factor `2`.
* `lintegral_biSup_sq_const_add_add_add_lt_top` — a sum of a constant and three processes of
  finite `S²` seminorm has finite `S²` seminorm.
* `lintegral_biSup_sq_setIntegral_le` — the `S²` seminorm of a time integral, by Cauchy–Schwarz.
* `lintegral_biSup_sq_const_mul` — the `S²` seminorm of a scalar multiple of a process.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.SupBound

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Squares and suprema in `ℝ≥0∞` -/

/-! ### Doob's `L²` maximal inequality in the `S²` shape -/

/-! ### Subadditivity of the `S²` seminorm -/


theorem _root_.Prove2MeSourceProof.h_9ba9941dfe7d03e124bfe576 [IsFiniteMeasure μ] (c : ℝ)
    (M₁ M₂ A : ℝ → Ω → ℝ) (T : ℝ)
    (hM₁ : AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M₁ t ω‖₊ : ℝ≥0∞) ^ 2) μ)
    (hM₂ : AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M₂ t ω‖₊ : ℝ≥0∞) ^ 2) μ)
    (hA : AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2) μ)
    (h₁ : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M₁ t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤)
    (h₂ : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M₂ t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤)
    (h₃ : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
        (‖c + M₁ t ω + M₂ t ω + A t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤ := by
  have two_lt : (2 : ℝ≥0∞) < ⊤ := by norm_num
  have hc := LevyStochCalc.BSDEJ.SupBound.lintegral_biSup_sq_const_lt_top (μ := μ) c T
  have hstep3 := LevyStochCalc.BSDEJ.SupBound.lintegral_biSup_sq_add_le (μ := μ) (fun _ _ => c) M₁ T hM₁
  have hstep2 := LevyStochCalc.BSDEJ.SupBound.lintegral_biSup_sq_add_le (μ := μ) (fun t ω => c + M₁ t ω) M₂ T hM₂
  have hstep1 := LevyStochCalc.BSDEJ.SupBound.lintegral_biSup_sq_add_le (μ := μ)
    (fun t ω => c + M₁ t ω + M₂ t ω) A T hA
  have h3 : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖c + M₁ t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤ :=
    lt_of_le_of_lt hstep3
      (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top two_lt hc, ENNReal.mul_lt_top two_lt h₁⟩)
  have h2' : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
      (‖c + M₁ t ω + M₂ t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤ :=
    lt_of_le_of_lt hstep2
      (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top two_lt h3, ENNReal.mul_lt_top two_lt h₂⟩)
  exact lt_of_le_of_lt hstep1
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top two_lt h2', ENNReal.mul_lt_top two_lt h₃⟩)
/-! ### The drift term -/

/-! ### Scalar multiples -/

end LevyStochCalc.BSDEJ.SupBound


