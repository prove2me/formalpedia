-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoTrigIncrement_F000
-- name    : LevyStochCalc_Brownian_ItoTrigIncrement_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:49:29.568409+00:00
-- url     : https://prove2.me/theorems/76e1c6ae-9d5a-4e84-8d59-f7a6d782338b
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoTrigIncrement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoTrigIncrement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_ScaledTrig_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaScalar_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrement_F001
import Definitions.Def_SourceProof_aa77a05410d36d075f77b369

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

section Trig

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

/-- The integrand of the `dW` term is jointly measurable. -/
theorem measurable_trig_integrand
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry fun ω s => g (X s ω) * indIoc Ω a b ω s) :=
  (hg.measurable.comp hX.measurable_uncurry).mul hm
/-- The integrand of the `dW` term is progressively measurable. -/
theorem progressivelyMeasurable_trig_integrand
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => g (X s ω) * indIoc Ω a b ω s :=
  (hX.progressivelyMeasurable_comp hg).mul hp
/-- The integrand of the `dW` term has finite `L²` mass over every window. -/
theorem lintegral_sq_trig_integrand_lt_top {g : ℝ → ℝ} {M : ℝ} (hgM : ∀ x, |g x| ≤ M)
    (hM0 : 0 ≤ M) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖g (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  refine _root_.Prove2MeSourceProof.h_aa77a05410d36d075f77b369 (M := M) (fun ω s => ?_) T hT
  rw [abs_mul]
  calc |g (X s ω)| * |indIoc Ω a b ω s| ≤ M * 1 :=
        mul_le_mul (hgM _) (indIoc_le_one a b ω s) (abs_nonneg _) hM0
    _ = M := mul_one M
variable (hC0 : (0 : ℝ) ≤ 1) (hCH : ∀ (ω : Ω) (s : ℝ), |indIoc Ω a b ω s| ≤ 1)

end Trig

end LevyStochCalc.Brownian.Ito


