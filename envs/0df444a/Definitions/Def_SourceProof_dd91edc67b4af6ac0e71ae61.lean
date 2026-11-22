-- Prove2me | Definitions.Def_SourceProof_dd91edc67b4af6ac0e71ae61
-- name    : SourceProof_dd91edc67b4af6ac0e71ae61
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:27:25.099398+00:00
-- url     : https://prove2.me/theorems/815bb7dc-5d90-4517-a338-fb4a73f0c756
-- title:
--   LevyStochCalc source module: SourceProof_dd91edc67b4af6ac0e71ae61
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.ae_setIntegral_timeAug_eq_mixedDrift` comes from the `LevyStochCalc.Ito.FiniteActivityMixedSteps` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F000
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaMeasurableShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaChainStopped_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F001
import Definitions.Def_SourceProof_f39314033c27f38b5a9bdf13

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


theorem _root_.Prove2MeSourceProof.h_dd91edc67b4af6ac0e71ae61
    {f : (Fin (n + 1) → ℝ) → ℝ}
    {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    {u : ℝ → (Fin n → ℝ) → ℝ} (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (B : Set E) (T : ℝ) (hT : 0 < T) (y : ℝ → Ω → Fin n → ℝ)
    (bdr : Fin n → Ω → ℝ → ℝ)
    (hbdr : ∀ (i : Fin n) (ω : Ω) (s : ℝ),
      bdr i ω s = continuousDriftLeftAt coeffs ν X.X B i ω s)
    (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (hH : ∀ (i : Fin n) (j : Fin d) (ω : Ω) (s : ℝ), H i j ω s = coeffs.σ s (X.X s ω) i j)
    (hmD : ∀ p : Fin (n + 1), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (timeAugProcess y s ω) * timeAugDrift bdr p ω s))
    (hqD : ∀ (p : Fin (n + 1)) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (timeAugProcess y s ω) * timeAugDrift bdr p ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hQint : ∀ᵐ ω ∂P, ∀ p q : Fin (n + 1), IntegrableOn
      (fun s => coordDeriv₂ f'' p q (timeAugProcess y s ω)
        * ∑ j : Fin d, timeAugDiffusion H p j ω s * timeAugDiffusion H q j ω s)
      (Set.Ioc (0 : ℝ) T) volume) :
    ∀ᵐ ω ∂P, (∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (timeAugProcess y s ω) * timeAugDrift bdr p ω s ∂volume)
        + 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (timeAugProcess y s ω)
              * (∑ j : Fin d, timeAugDiffusion H p j ω s * timeAugDiffusion H q j ω s) ∂volume
      = ∫ s in Set.Icc (0 : ℝ) T, (mixedDriftIntegrand u coeffs s (y s ω) (X.X s ω)
          - ∑ i : Fin n, gradient u s (y s ω) i * ∫ e in B, coeffs.γ s (X.X s ω) e i ∂ν) := by
  have hDint : ∀ᵐ ω ∂P, ∀ p : Fin (n + 1), IntegrableOn
      (fun s => LevyStochCalc.coordDeriv f' p (LevyStochCalc.Brownian.Ito.timeAugProcess y s ω) * LevyStochCalc.Brownian.Ito.timeAugDrift bdr p ω s)
      (Set.Ioc (0 : ℝ) T) volume :=
    MeasureTheory.ae_all_iff.mpr fun p => LevyStochCalc.Brownian.Ito.ae_integrableOn_Ioc_of_energy (hmD p) (hqD p T hT)
  filter_upwards [hDint, hQint, X.cadlag_paths] with ω hDω hQω hcadω
  set bpt : Fin (n + 1) → ℝ → ℝ := fun p s => LevyStochCalc.Brownian.Ito.timeAugDrift
    (fun q (_ : Ω) s => coeffs.μ s (X.X s ω) q - ∫ e in B, coeffs.γ s (X.X s ω) e q ∂ν) p ω s
    with hbptdef
  have hcount : {s : ℝ | 0 < s ∧ LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω ≠ X.X s ω}.Countable :=
    LevyStochCalc.Ito.JumpFormula.countable_setOf_pos_leftLimPathAt_ne (fun t ht => (hcadω t ht).1)
      (fun t ht i => (hcadω t ht.le).2 i)
  have hae : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), LevyStochCalc.Ito.JumpSplitting.leftLimPathAt X.X s ω = X.X s ω :=
    ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self
      (LevyStochCalc.Ito.ae_restrict_eq_of_countable_ne hcount T)
  have hbeq : ∀ p : Fin (n + 1), ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      LevyStochCalc.coordDeriv f' p (LevyStochCalc.Brownian.Ito.timeAugProcess y s ω) * LevyStochCalc.Brownian.Ito.timeAugDrift bdr p ω s
        = LevyStochCalc.coordDeriv f' p (LevyStochCalc.Brownian.Ito.timeAugProcess y s ω) * bpt p s := by
    intro p
    induction p using Fin.cases with
    | zero => exact Filter.Eventually.of_forall fun s => rfl
    | succ q =>
      filter_upwards [hae] with s hs
      simp only [bpt, LevyStochCalc.Brownian.Ito.timeAugDrift, Fin.cons_succ, hbdr, LevyStochCalc.Ito.JumpSplitting.continuousDriftLeftAt, hs]
  have hD' : ∀ p : Fin (n + 1), IntegrableOn
      (fun s => LevyStochCalc.coordDeriv f' p (LevyStochCalc.Brownian.Ito.timeAugProcess y s ω) * bpt p s) (Set.Ioc (0 : ℝ) T) volume :=
    fun p => (hDω p).congr_fun_ae (hbeq p)
  have hdrift_eq : ∀ p : Fin (n + 1), (∫ s in Set.Ioc (0 : ℝ) T,
        LevyStochCalc.coordDeriv f' p (LevyStochCalc.Brownian.Ito.timeAugProcess y s ω) * LevyStochCalc.Brownian.Ito.timeAugDrift bdr p ω s ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T, LevyStochCalc.coordDeriv f' p (LevyStochCalc.Brownian.Ito.timeAugProcess y s ω) * bpt p s ∂volume :=
    fun p => integral_congr_ae (hbeq p)
  rw [Finset.sum_congr rfl fun p _ => hdrift_eq p, LevyStochCalc.Ito.JumpFormula.setIntegral_Icc_eq_setIntegral_Ioc]
  exact _root_.Prove2MeSourceProof.h_f39314033c27f38b5a9bdf13 hfu hf hf' coeffs B T (fun s => y s ω)
    (fun s => X.X s ω) bpt (fun p j s => LevyStochCalc.Brownian.Ito.timeAugDiffusion H p j ω s) (fun s => rfl)
    (fun q s => rfl) (fun j s => rfl) (fun p j s => hH p j ω s) hD' hQω
end Mixed

end LevyStochCalc.Ito.JumpFormula


