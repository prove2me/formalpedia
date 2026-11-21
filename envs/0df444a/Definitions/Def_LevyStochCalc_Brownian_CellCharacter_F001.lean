-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_CellCharacter_F001
-- name    : LevyStochCalc_Brownian_CellCharacter_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:54:35.675516+00:00
-- url     : https://prove2.me/theorems/7a1f7023-2bda-483d-a0c9-ade401d6b561
-- title:
--   Source declarations: LevyStochCalc.Brownian.CellCharacter
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.CellCharacter. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

theorem measurable_trigDriftCell
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (l : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry (trigDriftCell l g X a b)) :=
  (((hg.measurable.comp hX.measurable_uncurry).const_mul (-l ^ 2)).mul
    (hm.pow_const 2)).const_mul (1 / 2)
theorem progressivelyMeasurable_trigDriftCell
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (l : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    Probability.ProgressivelyMeasurable ℱ (trigDriftCell l g X a b) := by
  have hconst : ∀ c : ℝ, Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => c :=
    fun c => _root_.Prove2MeSourceProof.h_35d8365844de2771203e553f
      (MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous
        (fun _ => stronglyMeasurable_const) fun _ => continuous_const)
  have h1 : Probability.ProgressivelyMeasurable ℱ fun ω s => -l ^ 2 * g (X s ω) :=
    (hconst (-l ^ 2)).mul (hX.progressivelyMeasurable_comp hg)
  have h2 : Probability.ProgressivelyMeasurable ℱ fun ω s => indIoc Ω a b ω s ^ 2 := by
    have := hp.mul hp
    simpa [sq] using this
  exact (hconst (1 / 2)).mul (h1.mul h2)
end Version

end LevyStochCalc.Brownian.Ito


