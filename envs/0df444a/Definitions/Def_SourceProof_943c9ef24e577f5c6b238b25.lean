-- Prove2me | Definitions.Def_SourceProof_943c9ef24e577f5c6b238b25
-- name    : SourceProof_943c9ef24e577f5c6b238b25
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:54:13.905227+00:00
-- url     : https://prove2.me/theorems/5b8238df-fcc1-4dd6-aa57-a890f450ac68
-- title:
--   LevyStochCalc source module: SourceProof_943c9ef24e577f5c6b238b25
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.abs_trigDriftCell_le` comes from the `LevyStochCalc.Brownian.CellCharacter` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CellCharacter_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The trigonometric functions of a Brownian increment are Itô processes

For a continuous version `X` of `∫ 1_{(a,b]} dW`, Itô's formula for the scaled cosine and sine
says that `cos (l X)` and `sin (l X)` are themselves Itô processes: their integrands are
`∓ l sin (l X) 1_{(a,b]}` and `± l cos (l X) 1_{(a,b]}` and their drifts are
`−(l²/2) cos (l X) 1_{(a,b]}²` and `−(l²/2) sin (l X) 1_{(a,b]}²`, with initial value `1` and `0`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Version

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_943c9ef24e577f5c6b238b25 (l : ℝ) {g : ℝ → ℝ} {M : ℝ} (hg : ∀ x, |g x| ≤ M) (hM0 : 0 ≤ M)
    (X : ℝ → Ω → ℝ) (a b : ℝ) (ω : Ω) (s : ℝ) :
    |trigDriftCell l g X a b ω s| ≤ 1 / 2 * (l ^ 2 * M) := by
  unfold LevyStochCalc.Brownian.Ito.trigDriftCell
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_mul, abs_mul, abs_neg,
    abs_pow, abs_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have h1 : |l| ^ 2 * |g (X s ω)| ≤ l ^ 2 * M := by
    rw [sq_abs]
    exact mul_le_mul_of_nonneg_left (hg _) (sq_nonneg l)
  have h2 : |LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s| ^ 2 ≤ 1 :=
    (pow_le_pow_left₀ (abs_nonneg _) (LevyStochCalc.Brownian.Ito.indIoc_le_one a b ω s) 2).trans (by norm_num)
  calc |l| ^ 2 * |g (X s ω)| * |LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s| ^ 2 ≤ (l ^ 2 * M) * 1 :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = l ^ 2 * M := mul_one _
end Version

end LevyStochCalc.Brownian.Ito


