-- Prove2me | Definitions.Def_SourceProof_2bacfe260b21496ede907710
-- name    : SourceProof_2bacfe260b21496ede907710
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:47:33.811971+00:00
-- url     : https://prove2.me/theorems/7be8bda8-e025-4ab2-8065-73aba9a65589
-- title:
--   LevyStochCalc source module: SourceProof_2bacfe260b21496ede907710
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpSide.stochasticIntegral_eq_neg_setIntegral_of_atoms_zero_spanning` comes from the `LevyStochCalc.Ito.JumpSideCompensator` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpSideCompensator_F000
import Definitions.Def_SourceProof_e0d6fbca60a06b5eea589fa2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A predictable integrand vanishing at the atoms

On a window of finite intensity the compensated integral of a predictable integrand is the
integral against the random measure minus the integral against the reference intensity, so an
integrand vanishing at every atom of the window has compensated integral minus its compensator.
The mark sets of finite intensity exhaust the mark space, the compensated integrals of the cut
integrands converge to the compensated integral of the integrand, and the compensators converge
to the compensator, so the identity survives at infinite activity.

## Main statements

* `stochasticIntegral_eq_neg_setIntegral_of_atoms_zero_spanning` — the identity for an integrand
  vanishing at the atoms of every window built from the spanning sets of the mark measure. Both
  the vanishing and the integrability of the compensator are asked only on a set of sample
  points, and the conclusion holds there: an integrand that is square integrable against the
  intensity need not be integrable against it, so the compensator converges only where the
  hypothesis puts it.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSide

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated LevyStochCalc.Ito.IntegralLimit

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.Prove2MeSourceProof.h_2bacfe260b21496ede907710
    (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hφpred : Probability.MarkedPredictable ℱ ν φ)
    (hφ0 : ∀ (ω : Ω) (s : ℝ) (e : E), s ≤ 0 → φ ω s e = 0) {T : ℝ} (hT : 0 < T) (G : Set Ω)
    (hint : ∀ᵐ ω ∂P, ω ∈ G → IntegrableOn (fun q : ℝ × E => φ ω q.1 q.2)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E)) (referenceIntensity ν))
    (hatoms : ∀ᵐ ω ∂P, ω ∈ G → ∀ j : ℕ,
      ∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j, φ ω q.1 q.2 ∂(N.N ω) = 0) :
    ∀ᵐ ω ∂P, ω ∈ G →
      Compensated.stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T ω
        = -∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E), φ ω q.1 q.2
            ∂(referenceIntensity ν) := by
  classical
  set A : ℕ → Set E := fun j => (spanningSets ν j)ᶜ with hAdef
  have hA : ∀ j, MeasurableSet (A j) := fun j => (measurableSet_spanningSets ν j).compl
  have hAc : ∀ j, (A j)ᶜ = spanningSets ν j := fun j => compl_compl _
  -- the identity at each finite-intensity level
  have hlevel : ∀ j : ℕ, ∀ᵐ ω ∂P, ω ∈ G →
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markCut (A j)ᶜ φ)
          (LevyStochCalc.Poisson.Compensated.measurable_markCut h_meas (hA j).compl)
          ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b h_progMeas) (hA j).compl)
          (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut h_sq (A j)ᶜ T' hT') T ω
        = -∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j, φ ω q.1 q.2
            ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
    intro j
    have hAνj : ν ((A j)ᶜ) ≠ ⊤ := by
      rw [hAc j]
      exact (measure_spanningSets_lt_top ν j).ne
    have hsupp : ∀ ω s e, e ∉ (A j)ᶜ → LevyStochCalc.Poisson.Compensated.markCut (A j)ᶜ φ ω s e = 0 := by
      intro ω s e he
      rw [LevyStochCalc.Poisson.Compensated.markCut_apply, Set.indicator_of_notMem he]
    have hzero : ∀ᵐ ω ∂P, ω ∈ G →
        ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (A j)ᶜ, LevyStochCalc.Poisson.Compensated.markCut (A j)ᶜ φ ω q.1 q.2 ∂(N.N ω) = 0 := by
      filter_upwards [hatoms] with ω hω hG
      have hcongr : ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (A j)ᶜ, LevyStochCalc.Poisson.Compensated.markCut (A j)ᶜ φ ω q.1 q.2 ∂(N.N ω)
          = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (A j)ᶜ, φ ω q.1 q.2 ∂(N.N ω) := by
        refine setIntegral_congr_fun (measurableSet_Ioc.prod (hA j).compl) fun q hq => ?_
        rw [LevyStochCalc.Poisson.Compensated.markCut_apply, Set.indicator_of_mem hq.2]
      rw [hcongr, hAc j]
      exact hω hG j
    have hmain := LevyStochCalc.Poisson.stochasticIntegral_eq_neg_setIntegral_of_atoms_zero N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markCut (A j)ᶜ φ)
      (LevyStochCalc.Poisson.Compensated.measurable_markCut h_meas (hA j).compl) ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b h_progMeas) (hA j).compl)
      (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut h_sq (A j)ᶜ T' hT') (hA j).compl
      (_root_.Prove2MeSourceProof.h_e0d6fbca60a06b5eea589fa2 hφpred hφ0 (hA j).compl)
      hAνj hsupp hT G hzero
    filter_upwards [hmain] with ω hω hG
    rw [hω hG, hAc j]
    congr 1
    refine setIntegral_congr_fun (measurableSet_Ioc.prod (measurableSet_spanningSets ν j))
      fun q hq => ?_
    rw [LevyStochCalc.Poisson.Compensated.markCut_apply, Set.indicator_of_mem hq.2]
  -- the two limits
  obtain ⟨k, hk, hkge, hlim⟩ := _root_.Prove2MeSourceProof.h_833bf70f39cc09b3b010a09e N ℱ hℱ φ
    h_meas h_progMeas h_sq A hA LevyStochCalc.Ito.JumpSide.ae_eventually_mem_spanningSets hT
  have hunion : ⋃ m : ℕ, Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν (k m)
      = Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E) := by
    rw [← Set.prod_iUnion]
    congr 1
    refine Set.eq_univ_of_subset ?_ (iUnion_spanningSets ν)
    exact Set.iUnion_mono' fun m => ⟨m, monotone_spanningSets ν (hkge m)⟩
  have hmono : Monotone fun m : ℕ => Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν (k m) := by
    intro a b hab
    exact Set.prod_mono_right (monotone_spanningSets ν (hk.monotone hab))
  have hcomp : ∀ᵐ ω ∂P, ω ∈ G → Tendsto
      (fun m => ∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν (k m), φ ω q.1 q.2
        ∂(LevyStochCalc.Poisson.referenceIntensity ν)) atTop
      (𝓝 (∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E), φ ω q.1 q.2
        ∂(LevyStochCalc.Poisson.referenceIntensity ν))) := by
    filter_upwards [hint] with ω hω hG
    have := MeasureTheory.tendsto_setIntegral_of_monotone
      (μ := LevyStochCalc.Poisson.referenceIntensity ν) (f := fun q : ℝ × E => φ ω q.1 q.2)
      (fun m => measurableSet_Ioc.prod (measurableSet_spanningSets ν (k m))) hmono
      (by rw [hunion]; exact hω hG)
    rwa [hunion] at this
  filter_upwards [hlim, hcomp, MeasureTheory.ae_all_iff.mpr hlevel] with ω hω hcω hlω hG
  refine tendsto_nhds_unique hω ?_
  have : (fun m => LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ (LevyStochCalc.Poisson.Compensated.markCut (A (k m))ᶜ φ)
      (LevyStochCalc.Poisson.Compensated.measurable_markCut h_meas (hA (k m)).compl)
      ((_root_.Prove2MeSourceProof.h_455c5c72b05cf697a7135f1b h_progMeas) (hA (k m)).compl)
      (fun T' hT' => LevyStochCalc.Poisson.Compensated.sq_markCut h_sq (A (k m))ᶜ T' hT') T ω)
      = fun m => -∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν (k m), φ ω q.1 q.2
          ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
    funext m
    exact hlω (k m) hG
  rw [this]
  exact (hcω hG).neg
end LevyStochCalc.Ito.JumpSide


