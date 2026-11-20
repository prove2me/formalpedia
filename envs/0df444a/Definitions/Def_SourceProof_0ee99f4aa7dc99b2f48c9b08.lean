-- Prove2me | Definitions.Def_SourceProof_0ee99f4aa7dc99b2f48c9b08
-- name    : SourceProof_0ee99f4aa7dc99b2f48c9b08
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:58:57.398031+00:00
-- url     : https://prove2.me/theorems/39800e37-0a8f-41bf-9dcb-c790e8da55e0
-- title:
--   LevyStochCalc source module: SourceProof_0ee99f4aa7dc99b2f48c9b08
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_L2_tendsto` comes from the `LevyStochCalc.Poisson.CompensatedDensityShifted` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityShifted_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The adapted (left-shifted) dyadic eval

The variant of the dyadic evaluation whose coefficient on the `i`-th dyadic interval is the
average of `φ` over the *previous* interval, hence `ℱ_{tᵢ}`-measurable for progressively
measurable `φ`. Its almost-everywhere and `L²(P ⊗ ds ⊗ ν)` convergence to `φ` follow from the
same Lebesgue-density and dominated-convergence arguments, the left shift contributing a
vanishing displacement.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Adapted (left-shifted) eval

The coefficient on the `i`-th dyadic interval is the average over the *previous*
interval (`dyadicAvg_shifted`), making it `ℱ_{tᵢ}`-measurable for progressively
measurable `φ` — the predictable/adapted version of `dyadicEval`. -/

set_option maxHeartbeats 1000000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.

theorem _root_.Prove2MeSourceProof.h_0ee99f4aa7dc99b2f48c9b08
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] {T : ℝ} (hT : 0 < T)
    (φ : Ω → ℝ → E → ℝ) (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M)
    {S : Set E} (hS_meas : MeasurableSet S) (hS_fin : ν S ≠ ⊤)
    (hSupp : ∀ ω e, e ∉ S → ∀ u, φ ω u e = 0) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  set M' : ℝ := max M 0 with hM'def
  have hM'_nn : 0 ≤ M' := le_max_right _ _
  have hφM' : ∀ ω s e, |φ ω s e| ≤ M' := fun ω s e => (hM ω s e).trans (le_max_left _ _)
  set cT : ℝ≥0∞ := ENNReal.ofReal ((2 * M') ^ 2 * T) with hcT
  have hFmeas : ∀ n : ℕ, Measurable (fun p : Ω × ℝ × E =>
      (‖φ p.1 p.2.1 p.2.2 - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n p.2.1 p.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) := fun n =>
    (ENNReal.continuous_coe.measurable.comp
      (h_meas.sub (LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_measurable_triple φ h_meas n)).nnnorm).pow_const 2
  have hF_se : ∀ n ω, Measurable (fun q : ℝ × E =>
      (‖φ ω q.1 q.2 - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n q.1 ω q.2‖₊ : ℝ≥0∞) ^ 2) := fun n ω =>
    (ENNReal.continuous_coe.measurable.comp
      ((h_meas.comp (by fun_prop : Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).sub
        ((LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_measurable_prod φ h_meas n ω))).nnnorm).pow_const 2
  have hswap : ∀ n ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
      = ∫⁻ e, (∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂ν := by
    intro n ω
    exact MeasureTheory.lintegral_lintegral_swap (hF_se n ω).aemeasurable
  have h_inner_le : ∀ n ω e,
      (∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        ≤ S.indicator (fun _ => cT) e := by
    intro n ω e
    by_cases he : e ∈ S
    · rw [Set.indicator_of_mem he]
      calc (∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((2 * M') ^ 2) ∂volume := by
            refine MeasureTheory.lintegral_mono (fun s => ?_)
            rw [show (‖φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2
                  = ENNReal.ofReal (‖φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e‖ ^ 2) from by
                rw [show (‖φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞)
                      = ENNReal.ofReal ‖φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e‖ from
                    (ofReal_norm _).symm, ← ENNReal.ofReal_pow (norm_nonneg _)]]
            refine ENNReal.ofReal_le_ofReal ?_
            have hb : ‖φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e‖ ≤ 2 * M' := by
              rw [Real.norm_eq_abs]
              calc |φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e|
                  ≤ |φ ω s e| + |LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e| := abs_sub _ _
                _ ≤ M' + M' := add_le_add (hφM' ω s e) (LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_bounded hT φ hM n s ω e)
                _ = 2 * M' := by ring
            nlinarith [norm_nonneg (φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e), hb, hM'_nn]
        _ = cT := by
            rw [MeasureTheory.setLIntegral_const, Real.volume_Icc, hcT,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1; rw [sub_zero]
    · have hzero : ∀ s, φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e = 0 := by
        intro s
        rw [hSupp ω e he s, LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_eq_zero φ n s ω e (hSupp ω e he), sub_zero]
      rw [Set.indicator_of_notMem he]
      simp only [hzero, nnnorm_zero, ENNReal.coe_zero]
      simp
  simp_rw [hswap]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun _ => cT * ν S) ?_ ?_ (by
      rw [MeasureTheory.lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS_fin)
        (MeasureTheory.measure_ne_top _ _)) ?_
  · intro n
    refine Measurable.aemeasurable ?_
    have hmeas2 : Measurable (fun q : Ω × E => ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖φ q.1 s q.2 - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s q.1 q.2‖₊ : ℝ≥0∞) ^ 2 ∂volume) := by
      have hr : Measurable (fun p : (Ω × E) × ℝ =>
          (‖φ p.1.1 p.2 p.1.2 - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n p.2 p.1.1 p.1.2‖₊ : ℝ≥0∞) ^ 2) :=
        (hFmeas n).comp (by fun_prop :
          Measurable fun p : (Ω × E) × ℝ => ((p.1.1, p.2, p.1.2) : Ω × ℝ × E))
      exact hr.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))
    exact hmeas2.lintegral_prod_right' (ν := ν)
  · intro n
    refine Filter.Eventually.of_forall (fun ω => ?_)
    calc (∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν)
        ≤ ∫⁻ e, S.indicator (fun _ => cT) e ∂ν :=
          MeasureTheory.lintegral_mono (fun e => h_inner_le n ω e)
      _ = cT * ν S := by
          rw [MeasureTheory.lintegral_indicator hS_meas, MeasureTheory.setLIntegral_const]
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [show (0 : ℝ≥0∞) = ∫⁻ _ : E, (0 : ℝ≥0∞) ∂ν from by simp]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun e => S.indicator (fun _ => cT) e) ?_ ?_ (by
        rw [MeasureTheory.lintegral_indicator hS_meas, MeasureTheory.setLIntegral_const]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS_fin) ?_
    · intro n
      have hes : Measurable (fun q : E × ℝ =>
          (‖φ ω q.2 q.1 - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n q.2 ω q.1‖₊ : ℝ≥0∞) ^ 2) := by
        refine (ENNReal.continuous_coe.measurable.comp (Measurable.sub ?_ ?_).nnnorm).pow_const 2
        · exact h_meas.comp (by fun_prop : Measurable fun q : E × ℝ => ((ω, q.2, q.1) : Ω × ℝ × E))
        · exact (LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_measurable_prod φ h_meas n ω).comp measurable_swap
      exact (hes.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))).aemeasurable
    · intro n
      exact Filter.Eventually.of_forall (fun e => h_inner_le n ω e)
    · exact Filter.Eventually.of_forall
        (fun e => LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_inner_L2_tendsto hT φ h_meas hM ω e)
end LevyStochCalc.Poisson.Compensated


