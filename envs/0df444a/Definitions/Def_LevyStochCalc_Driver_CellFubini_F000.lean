-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellFubini_F000
-- name    : LevyStochCalc_Driver_CellFubini_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:11:12.11721+00:00
-- url     : https://prove2.me/theorems/eacd681d-ab36-4062-b110-e8c16031b901
-- title:
--   Source declarations: LevyStochCalc.Driver.CellFubini
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CellFubini. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellIdentity_F000
import Definitions.Def_SourceProof_6b34c1879b36aa5cac429147

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

/-- The drift term of the paired cell identity, with the time integral outside. -/
theorem integral_mul_setIntegral_drift
    (hX : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (l : ℝ) {g : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    {Y : ℝ → Ω → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hYb : ∀ s ω, |Y s ω| ≤ 1)
    (hZ1 : Integrable Z P) (hVm : AEStronglyMeasurable V P) (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv) (t : ℝ) :
    ∫ ω, Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t,
        Y s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume) ∂P
      = ∫ s in Set.Ioc (0 : ℝ) t, ∫ ω, Z ω * V ω *
          (Y s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s) ∂P ∂volume := by
  have hgl : Continuous fun x => g (l * x) := hgc.comp (continuous_const.mul continuous_id)
  have hglb : ∀ x, |g (l * x)| ≤ 1 := fun x => hgb _
  refine _root_.Prove2MeSourceProof.h_6b34c1879b36aa5cac429147 (μ := volume) (S := Set.Ioc (0 : ℝ) t)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hZ1 hVm hMv0 hVb
    (hYm.mul (measurable_trigDriftCell hX l hgl)) (MF := 1 * (1 / 2 * (l ^ 2 * 1))) ?_
  intro ω s
  rw [abs_mul]
  exact mul_le_mul (hYb s ω) (_root_.Prove2MeSourceProof.h_943c9ef24e577f5c6b238b25 l hglb zero_le_one X a b ω s)
    (abs_nonneg _) zero_le_one
end Cell

end LevyStochCalc.Driver


