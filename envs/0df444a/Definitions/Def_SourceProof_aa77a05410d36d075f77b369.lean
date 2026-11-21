-- Prove2me | Definitions.Def_SourceProof_aa77a05410d36d075f77b369
-- name    : SourceProof_aa77a05410d36d075f77b369
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:43:51.840349+00:00
-- url     : https://prove2.me/theorems/3ebc3993-82be-45b9-ab39-72db8a30ad81
-- title:
--   LevyStochCalc source module: SourceProof_aa77a05410d36d075f77b369
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.lintegral_sq_lt_top_of_bounded` comes from the `LevyStochCalc.Brownian.ItoTrigIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_ScaledTrig_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for the scaled cosine and sine of a Brownian increment

`x ↦ cos (l * x)` and `x ↦ sin (l * x)` satisfy the hypotheses of Itô's formula for a scalar Itô
process, so for a version of `∫ 1_{(a,b]} dW` they give

  `cos (l * X_T) − cos (l * X_0) = ∫ (−l sin (l X)) 1_{(a,b]} dW − (l²/2) ∫ cos (l X) 1_{(a,b]} ds`

and the companion identity for the sine.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_aa77a05410d36d075f77b369 {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Ω → ℝ → ℝ} {M : ℝ} (hM : ∀ ω s, |F ω s| ≤ M) (T : ℝ) (_hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hpt : ∀ (ω : Ω) (s : ℝ),
      (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ≤ (ENNReal.ofReal (max M 0)) ^ 2 := by
    intro ω s
    refine pow_le_pow_left' ?_ 2
    calc (‖F ω s‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖F ω s‖ := by
          rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl
      _ ≤ ENNReal.ofReal (max M 0) :=
          ENNReal.ofReal_le_ofReal
            (((Real.norm_eq_abs _).le.trans (hM ω s)).trans (le_max_left _ _))
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ : Ω, ∫⁻ _ in Set.Icc (0 : ℝ) T,
          (ENNReal.ofReal (max M 0)) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ < ⊤ := by
        simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
          measure_univ, mul_one]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top
section Trig

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

variable (hC0 : (0 : ℝ) ≤ 1) (hCH : ∀ (ω : Ω) (s : ℝ), |indIoc Ω a b ω s| ≤ 1)

end Trig

end LevyStochCalc.Brownian.Ito


