-- Prove2me | Definitions.Def_SourceProof_60c6ff49320d94ec8490b751
-- name    : SourceProof_60c6ff49320d94ec8490b751
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:35:09.051357+00:00
-- url     : https://prove2.me/theorems/391432b2-0dd8-44f6-9765-b64fa532dc6c
-- title:
--   LevyStochCalc source module: SourceProof_60c6ff49320d94ec8490b751
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.markedPredictable_zeroExtPos_mixedJumpIncrement_leftLim` comes from the `LevyStochCalc.Ito.FiniteActivityMixedSteps` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F000
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaMeasurableShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaChainStopped_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F001
import Definitions.Def_SourceProof_7d28da0da84ad86b2d151781

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


theorem _root_.Prove2MeSourceProof.h_60c6ff49320d94ec8490b751 (S : SdeData X)
    (hXadapt : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t))
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hγmeasi : ∀ i : Fin n,
      Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2 i)
    {u : ℝ → (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 (Function.uncurry u))
    {y : ℝ → Ω → Fin n → ℝ} (hy_ad : ∀ t : ℝ, Measurable[S.ℱ t] (y t))
    (hy_left : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => y s ω j) (𝓝[<] t) (𝓝 L)) :
    MarkedPredictable S.ℱ ν (zeroExtPos fun ω s e =>
      mixedJumpIncrement u coeffs.γ s (leftLimPathAt y s ω) (leftLimPathAt X.X s ω) e) := by
  have hY := _root_.Prove2MeSourceProof.h_7d28da0da84ad86b2d151781 y S.ℱ hy_ad
    (fun ω t _ i => hy_left ω t i)
  have hΓ : LevyStochCalc.Probability.MarkedPredictable S.ℱ ν fun (ω : Ω) (s : ℝ) (e : E) =>
      (if 0 < s then coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e else 0 : Fin n → ℝ) := by
    unfold LevyStochCalc.Probability.MarkedPredictable
    letI : MeasurableSpace (Ω × ℝ × E) := LevyStochCalc.Probability.markedPredictableSigma S.ℱ ν
    refine measurable_pi_lambda _ fun i => ?_
    have h := LevyStochCalc.Ito.JumpSplitting.markedPredictable_zeroExtPos_jumpCoeff_leftLimPathAt (ν := ν) X.X S.ℱ i hXadapt
      (fun ω t _ j => hXleft ω t j) (hγmeasi i)
    unfold LevyStochCalc.Probability.MarkedPredictable at h
    convert h using 2 with p
    by_cases hs : (0 : ℝ) < p.2.1 <;> simp [LevyStochCalc.Ito.JumpFormula.zeroExtPos, hs]
  have hF : Measurable fun q : ℝ × (Fin n → ℝ) × (Fin n → ℝ) =>
      u q.1 (q.2.1 + q.2.2) - u q.1 q.2.1 :=
    ((hu.continuous.comp (continuous_fst.prodMk
      (continuous_snd.fst.add continuous_snd.snd))).sub
      (hu.continuous.comp (continuous_fst.prodMk continuous_snd.fst))).measurable
  have h := _root_.Prove2MeSourceProof.h_d6ed8f97bdea5b0368dd302f (ℱ := S.ℱ) (ν := ν) hF
    (Y := fun ω s => LevyStochCalc.Ito.JumpSplitting.leftLimPathAtPos y s ω) hY hΓ
  convert h using 1
  funext ω s e
  by_cases hs : (0 : ℝ) < s <;> simp [LevyStochCalc.Ito.JumpFormula.zeroExtPos, hs, LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement, LevyStochCalc.Ito.JumpSplitting.leftLimPathAtPos]
end Mixed

end LevyStochCalc.Ito.JumpFormula


