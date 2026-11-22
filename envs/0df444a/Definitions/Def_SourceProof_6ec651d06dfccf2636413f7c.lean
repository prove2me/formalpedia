-- Prove2me | Definitions.Def_SourceProof_6ec651d06dfccf2636413f7c
-- name    : SourceProof_6ec651d06dfccf2636413f7c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:28:38.762095+00:00
-- url     : https://prove2.me/theorems/4f25772a-3927-4f99-8986-9c0e8a088d1a
-- title:
--   LevyStochCalc source module: SourceProof_6ec651d06dfccf2636413f7c
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.admissible_mixedJumpIncrement_leftLim` comes from the `LevyStochCalc.Ito.FiniteActivityMixedSteps` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F000
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaMeasurableShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaChainStopped_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F001
import Definitions.Def_SourceProof_7ac4f497a1ed78b320395909
import Definitions.Def_SourceProof_c52cb68531741ca4a978b2b1

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


theorem _root_.Prove2MeSourceProof.h_6ec651d06dfccf2636413f7c (S : SdeData X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    {u : ℝ → (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₁ : ℝ} (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    {y : ℝ → Ω → Fin n → ℝ} (hy_m : Measurable (Function.uncurry y))
    (hy_ad : ∀ t : ℝ, Measurable[S.ℱ t] (y t))
    (hy_left : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => y s ω j) (𝓝[<] t) (𝓝 L))
    (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt X.X p.2.1 p.1) p.2.2 i)
    (hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable S.ℱ
      fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i)
    (hγqL : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    Measurable (fun p : Ω × ℝ × E => mixedJumpIncrement u coeffs.γ p.2.1
        (leftLimPathAt y p.2.1 p.1) (leftLimPathAt X.X p.2.1 p.1) p.2.2)
      ∧ Probability.MarkedProgressivelyMeasurable S.ℱ (fun ω s e =>
          mixedJumpIncrement u coeffs.γ s (leftLimPathAt y s ω) (leftLimPathAt X.X s ω) e)
      ∧ ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖mixedJumpIncrement u coeffs.γ s (leftLimPathAt y s ω)
            (leftLimPathAt X.X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  have hK₁'' : ∀ s x i, |LevyStochCalc.Ito.JumpFormula.gradient u s x i| ≤ max K₁ 0 :=
    fun s x i => (hK₁ s x i).trans (le_max_left _ _)
  have hK₁0' : (0 : ℝ) ≤ max K₁ 0 := le_max_right _ _
  have hyLm : Measurable fun q : ℝ × Ω => LevyStochCalc.Ito.JumpSplitting.leftLimPathAt y q.1 q.2 :=
    LevyStochCalc.Ito.JumpSplitting.measurable_uncurry_leftLimPathAt hy_m hy_left
  refine ⟨?_, ?_, fun T' hT' => ?_⟩
  · have hy : Measurable fun p : Ω × ℝ × E => LevyStochCalc.Ito.JumpSplitting.leftLimPathAt y p.2.1 p.1 :=
      hyLm.comp (measurable_snd.fst.prodMk measurable_fst)
    have hγ : Measurable fun p : Ω × ℝ × E =>
        coeffs.γ p.2.1 (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X p.2.1 p.1) p.2.2 :=
      measurable_pi_lambda _ fun i => hγmL i
    exact (hu.continuous.measurable.comp (measurable_snd.fst.prodMk (hy.add hγ))).sub
      (hu.continuous.measurable.comp (measurable_snd.fst.prodMk hy))
  · have hZ := _root_.Prove2MeSourceProof.h_c52cb68531741ca4a978b2b1 (ℱ := S.ℱ) (coeffs := coeffs)
      (Xp := LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X) (Y := LevyStochCalc.Ito.JumpSplitting.leftLimPathAt y)
      (fun i => LevyStochCalc.Ito.JumpSplitting.progressivelyMeasurable_leftLimPathAt hℱ0 hy_ad hy_left i) hγpL
    have hg : Continuous fun q : ℝ × (Fin n → ℝ) × (Fin n → ℝ) =>
        u q.1 (q.2.1 + q.2.2) - u q.1 q.2.1 :=
      (hu.continuous.comp (continuous_fst.prodMk
        (continuous_snd.fst.add continuous_snd.snd))).sub
        (hu.continuous.comp (continuous_fst.prodMk continuous_snd.fst))
    have hg0 : (fun q : ℝ × (Fin n → ℝ) × (Fin n → ℝ) =>
        u q.1 (q.2.1 + q.2.2) - u q.1 q.2.1) 0 = 0 := by simp
    exact hg.comp_markedProgressivelyMeasurable hg0 hZ
  · exact _root_.Prove2MeSourceProof.h_7ac4f497a1ed78b320395909
      (a := fun i ω s e => coeffs.γ s (LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω) e i) (c := n * max K₁ 0) hγmL
      (fun ω s e => LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le hu hK₁'' hK₁0' s _ _ e) T'
      (fun i => hγqL i T' hT')
end Mixed

end LevyStochCalc.Ito.JumpFormula


