-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellFubini_F001
-- name    : LevyStochCalc_Driver_CellFubini_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:11:56.394264+00:00
-- url     : https://prove2.me/theorems/70d07bcc-4565-41ac-bd96-9a485e526875
-- title:
--   Source declarations: LevyStochCalc.Driver.CellFubini
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CellFubini. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellIdentity_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Swapping the pairing with the time and window integrals

The two surviving terms of the paired cell identity are an integral over the sample space of a
set integral: over a time interval for the drift, over a window of times and marks for the
compensator. Both are instances of `LevyStochCalc.Probability.integral_mul_setIntegral_swap`,
which lives in the measure-theoretic layer; only the instantiations are here.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Probability
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Cell

variable {E : Type v} [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
  [MeasurableSingletonClass E] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {W : LevyStochCalc.Brownian.BrownianMotion P} {hℱW : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}
  {Z : Ω → ℝ} {V : Ω → ℝ} {Mv : ℝ}

omit [IsProbabilityMeasure P] in
/-- The drift factor of the paired cell identity is deterministic, so it comes out of the
pairing. -/
theorem integral_mul_trigDriftCell (l : ℝ) (g : ℝ → ℝ) (Y : ℝ → Ω → ℝ) (s : ℝ) :
    ∫ ω, Z ω * V ω * (Y s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s) ∂P
      = -(l ^ 2) / 2 * ((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s) ^ 2
        * ∫ ω, Z ω * V ω * (g (l * X s ω) * Y s ω) ∂P := by
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [trigDriftCell, indIoc]
  ring
end Cell

end LevyStochCalc.Driver


