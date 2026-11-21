-- Prove2me | Definitions.Def_SourceProof_68cf78692a1b2aaaa5a8b410
-- name    : SourceProof_68cf78692a1b2aaaa5a8b410
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:24:39.420793+00:00
-- url     : https://prove2.me/theorems/4782c5bc-6b97-42fa-88ab-da06318d5184
-- title:
--   LevyStochCalc source module: SourceProof_68cf78692a1b2aaaa5a8b410
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.truncation_L2_converges_brownian` comes from the `LevyStochCalc.Brownian.ItoDensityDyadicAverages` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F000

open private truncation_dominated_brownian truncation_pointwise_tendsto_brownian from Definitions.Def_LevyStochCalc_Brownian_ItoDensityDyadicAverages_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncation in `L²` and dyadic cell averages

Truncation of an `L²(Ω × [0,T])` integrand at level `M` together with the `L²` error it
incurs, the dyadic partition of `[0,T]`, the cell averages of an integrand over the
partition intervals, and the simple predictable process whose values on the `n`-th dyadic
grid are those averages.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.

theorem _root_.Prove2MeSourceProof.h_68cf78692a1b2aaaa5a8b410
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ}
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Filter.Tendsto
      (fun M : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - max (-(M : ℝ)) (min (M : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) ?_ ?_ h_sq_int.ne ?_
  · -- AEMeasurable via Measurable.lintegral_prod_right'.
    intro M
    have h_F_joint : Measurable (fun (p : Ω × ℝ) =>
        (‖H p.1 p.2 - max (-(M : ℝ)) (min (M : ℝ) (H p.1 p.2))‖₊ : ℝ≥0∞) ^ 2) := by
      have h_clip : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
      have h_sub : Measurable (fun (p : Ω × ℝ) =>
          H p.1 p.2 - max (-(M : ℝ)) (min (M : ℝ) (H p.1 p.2))) :=
        h_meas.sub (h_clip.comp h_meas)
      exact (ENNReal.continuous_coe.measurable.comp h_sub.nnnorm).pow_const 2
    refine Measurable.aemeasurable ?_
    exact Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_F_joint
  · -- Bound: F_M ω ≤ G ω everywhere.
    intro M
    refine Filter.Eventually.of_forall (fun ω => ?_)
    refine MeasureTheory.lintegral_mono (fun s => ?_)
    exact truncation_dominated_brownian _ _
  · -- Pointwise: F_M ω → 0 for a.e. ω with finite inner integral.
    have h_finite_inner : ∀ᵐ ω ∂P,
        ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ := by
      have h_bound_h : Measurable (fun ω =>
          ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) :=
        Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0:ℝ) T))
          ((ENNReal.continuous_coe.measurable.comp h_meas.nnnorm).pow_const 2)
      exact MeasureTheory.ae_lt_top h_bound_h h_sq_int.ne
    filter_upwards [h_finite_inner] with ω h_ω_finite
    -- For this ω, apply DCT on the s-integral.
    rw [show (0 : ℝ≥0∞)
        = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume.restrict (Set.Icc (0:ℝ) T)) from by simp]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2) ?_ ?_ h_ω_finite.ne ?_
    · intro M
      refine Measurable.aemeasurable ?_
      have h_clip : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
      have h_meas_slice : Measurable (fun s : ℝ => H ω s) :=
        h_meas.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s)))
      exact (ENNReal.continuous_coe.measurable.comp
        (h_meas_slice.sub (h_clip.comp h_meas_slice)).nnnorm).pow_const 2
    · intro M
      refine Filter.Eventually.of_forall (fun s => ?_)
      exact truncation_dominated_brownian _ _
    · refine Filter.Eventually.of_forall (fun s => ?_)
      exact truncation_pointwise_tendsto_brownian _
-- `omit` the unused `[MeasurableSpace Ω]` section variable (this lemma's
-- `g : Ω → ℝ → ℝ` does not need it).

end LevyStochCalc.Brownian.Ito


