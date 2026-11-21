-- Prove2me | Definitions.Def_SourceProof_98f8d351dfc96ce2a734c0bf
-- name    : SourceProof_98f8d351dfc96ce2a734c0bf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:12:58.905451+00:00
-- url     : https://prove2.me/theorems/34b37463-a5f1-4f9d-9a08-b0b211a0b9cc
-- title:
--   LevyStochCalc source module: SourceProof_98f8d351dfc96ce2a734c0bf
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.exists_markEval_L2_tendsto` comes from the `LevyStochCalc.Poisson.CompensatedDensityMarkApprox` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F001
import Definitions.Def_SourceProof_0ee99f4aa7dc99b2f48c9b08
import Definitions.Def_SourceProof_64b57ddfa082ba813e2cbaf7
import Definitions.Def_SourceProof_95164fb14a286c888ca62b65

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mark discretisation of the shifted dyadic eval

Approximation of the mark dependence of the adapted dyadic eval by finite mark-simple functions
`∑ₖ cₖ(ω) 𝟙_{Bₖ}(e)` with bounded, adapted coefficients, obtained by running the rectangle
density argument on each time piece over the trimmed product measure. Summing the per-piece
errors gives an `L²(P ⊗ ds ⊗ ν)` approximating sequence of adapted, mark-simple,
piecewise-constant-in-time integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_98f8d351dfc96ce2a734c0bf
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ} (hT : 0 < T)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M)
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hSupp : ∀ ω e, e ∉ S → ∀ u, φ ω u e = 0) :
    ∃ (Ki : (n : ℕ) → Fin (2 ^ n) → ℕ)
      (Bi : (n : ℕ) → (i : Fin (2 ^ n)) → Fin (Ki n i) → Set E)
      (ci : (n : ℕ) → (i : Fin (2 ^ n)) → Fin (Ki n i) → Ω → ℝ),
      (∀ n i k, MeasurableSet (Bi n i k)) ∧ (∀ n i k, Bi n i k ⊆ S) ∧
      (∀ n i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (dyadicPartition T n i.castSucc))
        (ci n i k)) ∧
      (∀ n i k, ∃ C, ∀ ω, |ci n i k ω| ≤ C) ∧
      Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - ∑ i : Fin (2 ^ n),
            (Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ)).indicator
              (fun _ => (1 : ℝ)) s
            * ∑ k, ci n i k ω * (Bi n i k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P) Filter.atTop (nhds 0) := by
  classical
  have hδne : ∀ n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := fun n =>
    ENNReal.inv_ne_zero.mpr (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩)
  choose Ki Bi ci hBim hBiS hcim hcib herr using fun n =>
    _root_.Prove2MeSourceProof.h_95164fb14a286c888ca62b65 N ℱ hT φ h_meas h_progMeas hM hS hSfin hSupp n (hδne n)
  refine ⟨Ki, Bi, ci, hBim, hBiS, hcim, hcib, ?_⟩
  -- the markEval step approximant and its triple-measurability.
  set mk : ℕ → Ω → ℝ → E → ℝ := fun n ω s e =>
    ∑ i : Fin (2 ^ n),
      (Set.Ioc (LevyStochCalc.Poisson.Compensated.dyadicPartition T n i.castSucc) (LevyStochCalc.Poisson.Compensated.dyadicPartition T n i.succ)).indicator
        (fun _ => (1 : ℝ)) s
      * ∑ k, ci n i k ω * (Bi n i k).indicator (fun _ => (1 : ℝ)) e with hmkdef
  have hmkm : ∀ n, Measurable (fun p : Ω × ℝ × E => mk n p.1 p.2.1 p.2.2) := by
    intro n
    refine Finset.measurable_sum _ (fun i _ => Measurable.mul ?_ ?_)
    · exact (measurable_const.indicator measurableSet_Ioc).comp
        (measurable_fst.comp measurable_snd)
    · refine Finset.measurable_sum _ (fun k _ => Measurable.mul ?_ ?_)
      · exact (((hcim n i k).measurable.mono
            (ℱ.le _) le_rfl)).comp measurable_fst
      · exact (measurable_const.indicator (hBim n i k)).comp
          (measurable_snd.comp measurable_snd)
  -- joint measurabilities of the two triangle summands.
  have hφm : ∀ n, Measurable (fun p : Ω × ℝ × E =>
      (‖φ p.1 p.2.1 p.2.2 - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n p.2.1 p.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) := fun n =>
    (ENNReal.continuous_coe.measurable.comp
      (h_meas.sub (LevyStochCalc.Poisson.Compensated.dyadicEvalShifted_measurable_triple φ h_meas n)).nnnorm).pow_const 2
  set A : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P with hAdef
  have htime : Filter.Tendsto A Filter.atTop (nhds 0) :=
    _root_.Prove2MeSourceProof.h_0ee99f4aa7dc99b2f48c9b08 hT φ h_meas hM hS hSfin hSupp
  -- the markEval error is dominated by `2·Aₙ + 2·(T·δₙ)`.
  have hbound : ∀ n, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e - mk n ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      ≤ 2 * A n + 2 * (ENNReal.ofReal T * ((n : ℝ≥0∞) + 1)⁻¹) := by
    intro n
    calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e - mk n ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (2 * (‖φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2
              + 2 * (‖LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e - mk n ω s e‖₊ : ℝ≥0∞) ^ 2)
            ∂ν ∂volume ∂P := by
          refine lintegral_mono (fun ω => lintegral_mono (fun s => lintegral_mono (fun e => ?_)))
          have h := LevyStochCalc.Poisson.Compensated.sq_nnnorm_add_le_two_mul (φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e)
            (LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e - mk n ω s e)
          rw [show φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e
                + (LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e - mk n ω s e) = φ ω s e - mk n ω s e from by ring,
            mul_add] at h
          exact h
      _ = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            2 * (‖φ ω s e - LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            2 * (‖LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e - mk n ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
          _root_.Prove2MeSourceProof.h_64b57ddfa082ba813e2cbaf7 ((hφm n).const_mul 2)
      _ = 2 * A n + 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e - mk n ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) := by
          rw [LevyStochCalc.Poisson.Compensated.lintegral_triple_const_mul 2 (by norm_num) _,
            LevyStochCalc.Poisson.Compensated.lintegral_triple_const_mul 2 (by norm_num) _]
      _ ≤ 2 * A n + 2 * (ENNReal.ofReal T * ((n : ℝ≥0∞) + 1)⁻¹) := by
          gcongr
          exact herr n
  -- the dominating sequence tends to `0`; squeeze.
  have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
    have hcomp : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Nat.cast_add, Nat.cast_one] using hcomp
  have hup : Filter.Tendsto (fun n => 2 * A n + 2 * (ENNReal.ofReal T * ((n : ℝ≥0∞) + 1)⁻¹))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n => 2 * A n) Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul htime (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      simpa using this
    have h2 : Filter.Tendsto (fun n : ℕ => 2 * (ENNReal.ofReal T * ((n : ℝ≥0∞) + 1)⁻¹))
        Filter.atTop (nhds 0) := by
      have ha : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal T * ((n : ℝ≥0∞) + 1)⁻¹)
          Filter.atTop (nhds (ENNReal.ofReal T * 0)) :=
        ENNReal.Tendsto.const_mul hinv (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_zero] at ha
      have hb := ENNReal.Tendsto.const_mul ha (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      rwa [mul_zero] at hb
    have := h1.add h2
    rwa [add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun _ => zero_le) hbound
end LevyStochCalc.Poisson.Compensated


