-- Prove2me | Definitions.Def_SourceProof_96c6857824b08f108587924a
-- name    : SourceProof_96c6857824b08f108587924a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:10:24.002027+00:00
-- url     : https://prove2.me/theorems/7561938f-11de-4502-bc23-76ec5ae0d7b0
-- title:
--   LevyStochCalc source module: SourceProof_96c6857824b08f108587924a
-- statement:
--   The original source theorem `LevyStochCalc.Driver.integral_mul_setIntegral_jump` comes from the `LevyStochCalc.Driver.CellFubini` module. The staged Lean declaration includes its source proof and dependency references.
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

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.Prove2MeSourceProof.h_96c6857824b08f108587924a
    (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    (l : ℝ) {g : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    {A : Set E} (hAν : ν A ≠ ⊤)
    {K : Ω → ℝ → E → ℝ} (hKm : Measurable fun p : Ω × ℝ × E => K p.1 p.2.1 p.2.2)
    {MK : ℝ} (hKb : ∀ ω s e, |K ω s e| ≤ MK)
    (hZ1 : Integrable Z P) (hVm : AEStronglyMeasurable V P) (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv) (t : ℝ) :
    ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
        g (l * X q.1 ω) * K ω q.1 q.2 ∂(referenceIntensity ν)) ∂P
      = ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, ∫ ω, Z ω * V ω *
          (g (l * X q.1 ω) * K ω q.1 q.2) ∂P ∂(referenceIntensity ν) := by
  haveI : SigmaFinite (LevyStochCalc.Poisson.referenceIntensity ν) := by
    rw [LevyStochCalc.Poisson.referenceIntensity]; infer_instance
  have hXq : Measurable fun p : Ω × ℝ × E => X p.2.1 p.1 :=
    hXm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  refine _root_.Prove2MeSourceProof.h_6b34c1879b36aa5cac429147 (μ := LevyStochCalc.Poisson.referenceIntensity ν)
    (S := Set.Ioc (0 : ℝ) t ×ˢ A) (MF := 1 * MK)
    (LevyStochCalc.Poisson.referenceIntensity_Ioc_prod_ne_top hAν t) hZ1 hVm hMv0 hVb
    ((hgc.measurable.comp (measurable_const.mul hXq)).mul hKm) ?_
  intro ω q
  rw [abs_mul]
  exact mul_le_mul (hgb _) (hKb ω q.1 q.2) (abs_nonneg _) zero_le_one
end Cell

end LevyStochCalc.Driver


