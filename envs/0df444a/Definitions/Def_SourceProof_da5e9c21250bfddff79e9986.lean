-- Prove2me | Definitions.Def_SourceProof_da5e9c21250bfddff79e9986
-- name    : SourceProof_da5e9c21250bfddff79e9986
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T12:33:12.695204+00:00
-- url     : https://prove2.me/theorems/f69674b1-d7ac-4e7d-a37c-dcb20964297e
-- title:
--   LevyStochCalc source module: SourceProof_da5e9c21250bfddff79e9986
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.ae_integrableOn_mixed_window` comes from the `LevyStochCalc.Ito.FiniteActivityMixedSteps` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F000
import Definitions.Def_LevyStochCalc_Ito_FiniteActivityMixedPrelims_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaMeasurableShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaChainStopped_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F000
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F001
import Definitions.Def_SourceProof_190b24feee30508af1f5a5e6

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


theorem _root_.Prove2MeSourceProof.h_da5e9c21250bfddff79e9986 (S : SdeData X)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₀ K₁ K₂ : ℝ}
    (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T)
    {B : Set E} (hBν : ν B ≠ ⊤)
    (y : ℝ → Ω → Fin n → ℝ) (hy_m : Measurable (Function.uncurry y)) :
    ∀ᵐ ω ∂P,
      (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i : Fin n,
        IntegrableOn (fun e => coeffs.γ s (X.X s ω) e i) B ν)
      ∧ (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        IntegrableOn (fun e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) B ν)
      ∧ IntegrableOn (fun s => ∫ e in B, mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e ∂ν)
          (Set.Icc (0 : ℝ) T) volume
      ∧ IntegrableOn (fun s => ∑ i : Fin n,
          gradient u s (y s ω) i * ∫ e in B, coeffs.γ s (X.X s ω) e i ∂ν)
          (Set.Icc (0 : ℝ) T) volume
      ∧ IntegrableOn (fun s => mixedDriftIntegrand u coeffs s (y s ω) (X.X s ω))
          (Set.Icc (0 : ℝ) T) volume := by
  haveI hBfin : IsFiniteMeasure (ν.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hBν⟩
  have hK₁'' : ∀ s x i, |LevyStochCalc.Ito.JumpFormula.gradient u s x i| ≤ max K₁ 0 :=
    fun s x i => (hK₁ s x i).trans (le_max_left _ _)
  have hK₁0' : (0 : ℝ) ≤ max K₁ 0 := le_max_right _ _
  have hyω : ∀ ω : Ω, Measurable fun s => y s ω :=
    fun ω => hy_m.comp (measurable_id.prodMk measurable_const)
  have hγsec : ∀ (ω : Ω) (s : ℝ), Measurable fun e => coeffs.γ s (X.X s ω) e :=
    fun ω s => hγmeas.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  -- the jump coefficient at the point values is square integrable in the mark at a.e. time
  have hγL2 : ∀ i : Fin n, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∫⁻ e, (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν < ⊤ := by
    intro i
    filter_upwards [MeasureTheory.ae_lt_top (LevyStochCalc.Poisson.Compensated.measurable_markEnergy
      (f := fun ω s e => (‖LevyStochCalc.Ito.SmallJump.pathJumpCoeff coeffs X.X i ω s e‖₊ : ℝ≥0∞) ^ 2)
      (((S.γ_meas i).nnnorm.coe_nnreal_ennreal).pow_const 2) T) (S.γ_sq i T hT).ne] with ω hω
    exact MeasureTheory.ae_lt_top ((((S.γ_meas i).nnnorm.coe_nnreal_ennreal).pow_const 2).comp
      (by fun_prop :
        Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).lintegral_prod_right' hω.ne
  have hγi : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i : Fin n,
      IntegrableOn (fun e => coeffs.γ s (X.X s ω) e i) B ν := by
    filter_upwards [MeasureTheory.ae_all_iff.mpr hγL2] with ω hω
    filter_upwards [MeasureTheory.ae_all_iff.mpr hω] with s hs i
    exact ((LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top
      ((measurable_pi_apply i).comp (hγsec ω s)).aestronglyMeasurable
      (hs i)).restrict B).integrable one_le_two
  -- the mark integrals of the point-evaluated jump coefficient and of its absolute value are
  -- integrable in time
  have hmarkInt : ∀ i : Fin n, ∀ᵐ ω ∂P,
      IntegrableOn (fun s => ∫ e in B, coeffs.γ s (X.X s ω) e i ∂ν) (Set.Icc (0 : ℝ) T)
        volume := by
    intro i
    refine LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top
      (LevyStochCalc.Ito.JumpSplitting.stronglyMeasurable_setIntegral_mark B (LevyStochCalc.Ito.SmallJump.pathJumpCoeff coeffs X.X i)
        (S.γ_meas i)).measurable ?_
    exact lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_63d33904140915cafacf5d43 hBν _ (S.γ_meas i) T)
      (ENNReal.mul_lt_top (S.γ_sq i T hT) (lt_top_iff_ne_top.mpr hBν))
  have hmarkAbs : ∀ i : Fin n, ∀ᵐ ω ∂P,
      IntegrableOn (fun s => ∫ e in B, |coeffs.γ s (X.X s ω) e i| ∂ν) (Set.Icc (0 : ℝ) T)
        volume := by
    intro i
    refine LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top
      (LevyStochCalc.Ito.JumpSplitting.stronglyMeasurable_setIntegral_mark B
        (fun ω s e => |LevyStochCalc.Ito.SmallJump.pathJumpCoeff coeffs X.X i ω s e|)
        (S.γ_meas i).abs).measurable ?_
    refine lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_63d33904140915cafacf5d43 hBν _ (S.γ_meas i).abs T) ?_
    refine ENNReal.mul_lt_top ?_ (lt_top_iff_ne_top.mpr hBν)
    simpa [LevyStochCalc.Ito.SmallJump.pathJumpCoeff] using S.γ_sq i T hT
  have hμint : ∀ᵐ ω ∂P, ∀ p : Fin n,
      IntegrableOn (fun s => coeffs.μ s (X.X s ω) p) (Set.Icc (0 : ℝ) T) :=
    MeasureTheory.ae_all_iff.mpr fun p =>
      LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top (hμm p) (hμq p T hT)
  have hσsq : ∀ᵐ ω ∂P, ∀ (p : Fin n) (j : Fin d),
      IntegrableOn (fun s => coeffs.σ s (X.X s ω) p j ^ 2) (Set.Icc (0 : ℝ) T) := by
    refine MeasureTheory.ae_all_iff.mpr fun p => MeasureTheory.ae_all_iff.mpr fun j => ?_
    filter_upwards [MeasureTheory.ae_lt_top (LevyStochCalc.Brownian.Ito.measurable_energyDensity (S.σ_meas p j) T)
      (S.σ_sq p j T hT).ne] with ω hω
    exact (LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top
      (Measurable.of_uncurry_left (S.σ_meas p j)) hω).integrable_sq
  have hΔm : Measurable fun p : Ω × ℝ × E =>
      LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement u coeffs.γ p.2.1 (y p.2.1 p.1) (X.X p.2.1 p.1) p.2.2 := by
    have hy : Measurable fun p : Ω × ℝ × E => y p.2.1 p.1 :=
      hy_m.comp (measurable_snd.fst.prodMk measurable_fst)
    have hγ : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 :=
      measurable_pi_lambda _ fun i => S.γ_meas i
    exact (hu.continuous.measurable.comp (measurable_snd.fst.prodMk (hy.add hγ))).sub
      (hu.continuous.measurable.comp (measurable_snd.fst.prodMk hy))
  filter_upwards [hγi, MeasureTheory.ae_all_iff.mpr hmarkInt,
    MeasureTheory.ae_all_iff.mpr hmarkAbs, hμint, hσsq] with ω hγω hmiω hmaω hμω hσω
  have hΔω : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      IntegrableOn (fun e => LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) B ν := by
    filter_upwards [hγω] with s hs
    refine Integrable.mono'
      (g := fun e => (n : ℝ) * max K₁ 0 * ∑ i, |coeffs.γ s (X.X s ω) e i|)
      ((integrable_finsetSum Finset.univ fun i _ => (hs i).abs).const_mul
        ((n : ℝ) * max K₁ 0)) ?_ ?_
    · exact ((hu.continuous.measurable.comp (measurable_const.prodMk
        (measurable_const.add (hγsec ω s)))).sub measurable_const).aestronglyMeasurable
    · filter_upwards with e
      rw [Real.norm_eq_abs]
      exact LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le hu hK₁'' hK₁0' s _ _ e
  refine ⟨hγω, hΔω, ?_, ?_, ?_⟩
  · -- the mark integral of the mixed jump increment is integrable in time
    refine Integrable.mono'
      (g := fun s => (n : ℝ) * max K₁ 0 * ∑ i, ∫ e in B, |coeffs.γ s (X.X s ω) e i| ∂ν)
      ((integrable_finsetSum Finset.univ fun i _ => hmaω i).const_mul
        ((n : ℝ) * max K₁ 0)) ?_ ?_
    · exact ((LevyStochCalc.Ito.JumpSplitting.stronglyMeasurable_setIntegral_mark B
        (fun ω s e => LevyStochCalc.Ito.JumpFormula.mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) hΔm).comp_measurable
        measurable_prodMk_left).aestronglyMeasurable
    · filter_upwards [hγω] with s hs
      have hgint : Integrable (fun e => (n : ℝ) * max K₁ 0 * ∑ i, |coeffs.γ s (X.X s ω) e i|)
          (ν.restrict B) :=
        (integrable_finsetSum Finset.univ fun i _ => (hs i).abs).const_mul _
      refine (norm_integral_le_of_norm_le hgint ?_).trans (le_of_eq ?_)
      · filter_upwards with e
        rw [Real.norm_eq_abs]
        exact LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le hu hK₁'' hK₁0' s _ _ e
      · rw [integral_const_mul, integral_finsetSum _ fun i _ => (hs i).abs]
  · -- the first-order term is integrable in time
    refine integrable_finsetSum _ fun i _ => Integrable.bdd_mul (c := K₁) (hmiω i) ?_ ?_
    · exact ((LevyStochCalc.Ito.JumpFormula.continuous_gradient_uncurry hu i).measurable.comp
        (measurable_id.prodMk (hyω ω))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs]; exact hK₁ s _ i
  · -- the mixed drift integrand is integrable in time
    have hK₀' : ∀ s x, |LevyStochCalc.Ito.JumpFormula.timeDeriv u s x| ≤ max K₀ 0 :=
      fun s x => (hK₀ s x).trans (le_max_left _ _)
    have hK₂'' : ∀ s x i j, |LevyStochCalc.Ito.JumpFormula.hessian u s x i j| ≤ max K₂ 0 :=
      fun s x i j => (hK₂ s x i j).trans (le_max_left _ _)
    have hK₂0 : (0 : ℝ) ≤ max K₂ 0 := le_max_right _ _
    refine Integrable.mono' (g := fun s => max K₀ 0 + max K₁ 0 * ∑ p, |coeffs.μ s (X.X s ω) p|
      + (1 / 2) * max K₂ 0 * ∑ p, ∑ q, ∑ j,
        (coeffs.σ s (X.X s ω) p j ^ 2 + coeffs.σ s (X.X s ω) q j ^ 2) / 2) ?_ ?_ ?_
    · refine Integrable.add (Integrable.add (integrable_const _) ?_) ?_
      · exact (integrable_finsetSum _ fun p _ => (hμω p).abs).const_mul _
      · refine Integrable.const_mul ?_ _
        refine integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
          integrable_finsetSum _ fun j _ => ?_
        exact ((hσω p j).add (hσω q j)).div_const 2
    · refine Measurable.aestronglyMeasurable ?_
      refine Measurable.add ((LevyStochCalc.Ito.JumpFormula.continuous_timeDeriv hu).measurable.comp
        (measurable_id.prodMk (hyω ω))) (Measurable.add ?_ (measurable_const.mul ?_))
      · exact Finset.measurable_sum _ fun p _ => (Measurable.of_uncurry_left (hμm p)).mul
          ((LevyStochCalc.Ito.JumpFormula.continuous_gradient_uncurry hu p).measurable.comp (measurable_id.prodMk (hyω ω)))
      · refine Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun q _ =>
          Finset.measurable_sum _ fun j _ => ?_
        exact ((Measurable.of_uncurry_left (S.σ_meas p j)).mul
          (Measurable.of_uncurry_left (S.σ_meas q j))).mul
          ((LevyStochCalc.Ito.JumpFormula.continuous_hessian hu p q).measurable.comp (measurable_id.prodMk (hyω ω)))
    · refine Filter.Eventually.of_forall fun s => ?_
      rw [Real.norm_eq_abs]
      exact _root_.Prove2MeSourceProof.h_190b24feee30508af1f5a5e6 coeffs hK₂0 hK₀' hK₁'' hK₂'' s _ _
end Mixed

end LevyStochCalc.Ito.JumpFormula


