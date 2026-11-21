-- Prove2me | Definitions.Def_SourceProof_d535c014a12fb1a12728f5c9
-- name    : SourceProof_d535c014a12fb1a12728f5c9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:52:23.341931+00:00
-- url     : https://prove2.me/theorems/b19321f4-9dbc-44cb-b0c4-35f3ceaadc1c
-- title:
--   LevyStochCalc source module: SourceProof_d535c014a12fb1a12728f5c9
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.ae_tendsto_drift_clamp` comes from the `LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integrands of the clamped approximation of a vector Itô process

For a function whose first and second derivatives are bounded, the drift integrals, the quadratic
variation terms and the diffusion integrands built from the coefficients clamped at a level growing
to infinity converge to the ones built from the original coefficients: the drift and quadratic
variation terms pathwise, the diffusion integrands in energy on a bounded window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Limits

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_d535c014a12fb1a12728f5c9
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    {T : ℝ}
    (hbq : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω))) :
    ∀ᵐ ω ∂P, ∀ p : Fin n, Filter.Tendsto (fun i => ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv f' p (Y i s ω) * clampDrift b (ns i) p ω s ∂volume) Filter.atTop
      (𝓝 (∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (X s ω) * b p ω s ∂volume)) := by
  have hK₁0 : (0 : ℝ) ≤ K₁ := le_trans (norm_nonneg _) (hf'bd 0)
  have hint : ∀ p : Fin n, ∀ᵐ ω ∂P,
      IntegrableOn (b p ω) (Set.Icc (0 : ℝ) T) volume :=
    fun p => LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top (hbm p) (hbq p)
  have hintall : ∀ᵐ ω ∂P, ∀ p : Fin n, IntegrableOn (b p ω) (Set.Icc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    exact hint
  filter_upwards [hae, hintall] with ω hω hbint
  intro p
  have haeIoc : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self hω
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun s => K₁ * |b p ω s|) (fun i => ?_) ?_ (fun i => ?_) ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    exact (((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp
      (Measurable.of_uncurry_left (hYm i))).mul
      ((LevyStochCalc.continuous_clampAt (((ns i : ℕ) : ℝ))).measurable.comp
        (Measurable.of_uncurry_left (hbm p))))
  · exact ((hbint p).mono_set Set.Ioc_subset_Icc_self).abs.const_mul K₁
  · refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (LevyStochCalc.abs_coordDeriv_le hf'bd p _)
      (LevyStochCalc.abs_clampAt_le_abs (Nat.cast_nonneg _) _) (abs_nonneg _) hK₁0
  · filter_upwards [haeIoc] with s hs
    exact ((LevyStochCalc.continuous_coordDeriv hf'c p).continuousAt.tendsto.comp hs).mul
      (LevyStochCalc.Brownian.Ito.tendsto_clampAt_comp hge (b p ω s))
end Limits

end Clamped

end LevyStochCalc.Brownian.Ito


