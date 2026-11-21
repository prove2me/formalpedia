-- Prove2me | Definitions.Def_SourceProof_7a12160ca4d56ce7d0871bc7
-- name    : SourceProof_7a12160ca4d56ce7d0871bc7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:01:02.429205+00:00
-- url     : https://prove2.me/theorems/b87edc4d-415d-4e1f-8134-6744fdd43e98
-- title:
--   LevyStochCalc source module: SourceProof_7a12160ca4d56ce7d0871bc7
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.tendsto_setLIntegral_Ioc_prod_zero` comes from the `LevyStochCalc.Brownian.ItoL2CompletionConvergence` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionIncrement_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: `L¹`/`L²` convergence and adapted approximation

Transfer of the martingale property along `L¹`-limits, criteria for `L¹`
convergence of squares from `L²` bounds, the endpoint `L²` bound for differences of
simple integrals, and the existence of an adapted `SimplePredictable` integrand
within a prescribed `L²([0, T] × Ω)` tolerance of a progressively measurable
square-integrable integrand, together with the norm and increment identities they
use.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_7a12160ca4d56ce7d0871bc7
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (φ : Ω → ℝ → ℝ≥0∞) (hφ : Measurable (Function.uncurry φ))
    {s₀ T : ℝ} (hs₀ : 0 ≤ s₀) (hs₀T : s₀ < T)
    (h_fin : ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, φ ω u ∂volume ∂P ≠ ⊤) :
    Filter.Tendsto (fun r => ∫⁻ ω, ∫⁻ u in Set.Ioc s₀ r, φ ω u ∂volume ∂P)
      (nhdsWithin s₀ (Set.Ioi s₀)) (nhds 0) := by
  have hset : MeasurableSet ((Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) T) :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Icc
  set f : Ω × ℝ → ℝ≥0∞ :=
    ((Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) T).indicator (Function.uncurry φ) with hf
  have h_tot : ∫⁻ z, f z ∂(P.prod volume) ≠ ⊤ := by
    rw [hf, MeasureTheory.lintegral_indicator hset,
        MeasureTheory.setLIntegral_prod _ (hφ.aemeasurable.restrict),
        MeasureTheory.Measure.restrict_univ]
    simpa using h_fin
  have h_meas_to_zero : Filter.Tendsto
      (fun r => (P.prod volume) ((Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r))
      (nhdsWithin s₀ (Set.Ioi s₀)) (nhds 0) := by
    have hval : (fun r => (P.prod volume) ((Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r))
        = fun r => ENNReal.ofReal (r - s₀) := by
      funext r
      rw [MeasureTheory.Measure.prod_prod, measure_univ, one_mul, Real.volume_Ioc]
    rw [hval]
    have h1 : Filter.Tendsto (fun r => r - s₀)
        (nhdsWithin s₀ (Set.Ioi s₀)) (nhds 0) := by
      have h0 : Filter.Tendsto (fun r => r - s₀) (nhds s₀) (nhds (s₀ - s₀)) :=
        (continuous_sub_right s₀).tendsto s₀
      rw [sub_self] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    simpa [Function.comp_def] using this
  have h_zero := MeasureTheory.tendsto_setLIntegral_zero (μ := P.prod volume) (f := f)
    (s := fun r => (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r) h_tot h_meas_to_zero
  refine h_zero.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hs₀T] with r hr
  have hsub : (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r ⊆ (Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) T :=
    Set.prod_mono (le_refl _) (fun u hu => ⟨le_of_lt (lt_of_le_of_lt hs₀ hu.1),
      le_of_lt (lt_of_le_of_lt hu.2 hr.2)⟩)
  have hset' : MeasurableSet ((Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r) :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Ioc
  have hstep1 : ∫⁻ z in (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r, f z ∂(P.prod volume)
      = ∫⁻ z in (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r, Function.uncurry φ z ∂(P.prod volume) := by
    refine MeasureTheory.setLIntegral_congr_fun hset' (fun z hz => ?_)
    rw [hf, Set.indicator_of_mem (hsub hz)]
  rw [hstep1, MeasureTheory.setLIntegral_prod _ (hφ.aemeasurable.restrict),
      MeasureTheory.Measure.restrict_univ]
  rfl
end LevyStochCalc.Brownian.Ito


