-- Prove2me | Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F000
-- name    : LevyStochCalc_Ito_FiniteActivityMixedSteps_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:30:26.139471+00:00
-- url     : https://prove2.me/theorems/9bb1caaa-9f4b-47d2-a806-04d2d5320d49
-- title:
--   Source declarations: LevyStochCalc.Ito.FiniteActivityMixedSteps
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.FiniteActivityMixedSteps. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F000
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaMeasurableShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaChainStopped_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Steps of the finite-activity Itô–Lévy identity in the mixed form

Regularity of the time-augmented path, window integrability of the mixed integrands, the
dictionary identifying the time-augmented drift and quadratic terms with the mixed drift
integrand, and the predictability and admissibility of the mixed jump increment read at the
left limits.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.measurable_uncurry_timeAugProcess`
* `LevyStochCalc.Ito.JumpFormula.measurable_timeAugProcess_adapted`
* `LevyStochCalc.Ito.JumpFormula.tendsto_timeAugProcess_nhdsWithin_gt`
* `LevyStochCalc.Ito.JumpFormula.ae_integrableOn_mixed_window`
* `LevyStochCalc.Ito.JumpFormula.ae_setIntegral_timeAug_eq_mixedDrift`
* `LevyStochCalc.Ito.JumpFormula.admissible_mixedJumpIncrement_leftLim`
* `LevyStochCalc.Ito.JumpFormula.ae_countable_setOf_leftLim_ne_pair`
* `LevyStochCalc.Ito.JumpFormula.markedPredictable_zeroExtPos_mixedJumpIncrement_leftLim`
* `LevyStochCalc.Ito.JumpFormula.lintegral_referenceIntensity_window_ne_top`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability
open LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim LevyStochCalc.Ito.BigJump
open LevyStochCalc.Ito.JumpSplitting

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section TimeAug

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} {y : ℝ → Ω → Fin n → ℝ}

/-- The time augmentation of a jointly measurable path is jointly measurable. -/
theorem measurable_uncurry_timeAugProcess (hy_m : Measurable (Function.uncurry y)) :
    Measurable (Function.uncurry fun ω s => timeAugProcess y s ω) := by
  refine measurable_pi_iff.mpr fun p => ?_
  induction p using Fin.cases with
  | zero =>
    simp only [Function.uncurry, timeAugProcess, Fin.cons_zero]
    exact measurable_snd
  | succ q =>
    simp only [Function.uncurry, timeAugProcess, Fin.cons_succ]
    exact (measurable_pi_apply q).comp (hy_m.comp (measurable_snd.prodMk measurable_fst))
/-- The time augmentation of a path adapted to a filtration is adapted to that filtration. -/
theorem measurable_timeAugProcess_adapted (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hy_ad : ∀ t : ℝ, Measurable[ℱ t] (y t)) (t : ℝ) :
    Measurable[ℱ t] (timeAugProcess y t) := by
  letI : MeasurableSpace Ω := ℱ t
  refine measurable_pi_iff.mpr fun p => ?_
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugProcess, Fin.cons_zero]
    exact measurable_const
  | succ q =>
    simp only [timeAugProcess, Fin.cons_succ]
    exact (measurable_pi_apply q).comp (hy_ad t)
omit [MeasurableSpace Ω] in
/-- The time augmentation of a right-continuous path is right-continuous. -/
theorem tendsto_timeAugProcess_nhdsWithin_gt
    (hy_rc : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => y s ω) (𝓝[>] t) (𝓝 (y t ω)))
    (ω : Ω) (t : ℝ) :
    Tendsto (fun s => timeAugProcess y s ω) (𝓝[>] t) (𝓝 (timeAugProcess y t ω)) := by
  refine tendsto_pi_nhds.mpr fun p => ?_
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugProcess, Fin.cons_zero]
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  | succ q =>
    simp only [timeAugProcess, Fin.cons_succ]
    exact ((continuous_apply q).tendsto _).comp (hy_rc ω t)
end TimeAug

section Mixed

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

end Mixed

end LevyStochCalc.Ito.JumpFormula


