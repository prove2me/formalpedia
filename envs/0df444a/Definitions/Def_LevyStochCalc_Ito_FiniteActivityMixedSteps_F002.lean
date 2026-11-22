-- Prove2me | Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedSteps_F002
-- name    : LevyStochCalc_Ito_FiniteActivityMixedSteps_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:32:30.259438+00:00
-- url     : https://prove2.me/theorems/98c087f5-743d-4862-8311-b5ed136152cb
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

end TimeAug

section Mixed

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

omit [IsProbabilityMeasure P] in
/-- A marked integrand of finite mark energy on every bounded window has finite energy on the
window against the reference intensity of the mark measure. -/
theorem lintegral_referenceIntensity_window_ne_top {φ : Ω → ℝ → E → ℝ}
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (B : Set E) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ B,
      ‖φ ω q.1 q.2‖ₑ ^ 2 ∂(LevyStochCalc.Poisson.referenceIntensity ν) ∂P ≠ ⊤ := by
  refine ne_top_of_le_ne_top (hφq T hT).ne (lintegral_mono fun ω => ?_)
  rw [LevyStochCalc.Poisson.lintegral_referenceIntensity_window
    (f := fun q : ℝ × E => ‖φ ω q.1 q.2‖ₑ ^ 2) ((hφm.comp
      (by fun_prop :
        Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).enorm.pow_const 2) B T]
  refine (lintegral_mono_set Set.Ioc_subset_Icc_self).trans (lintegral_mono fun s => ?_)
  exact lintegral_mono' Measure.restrict_le_self fun e => le_rfl
end Mixed

end LevyStochCalc.Ito.JumpFormula


