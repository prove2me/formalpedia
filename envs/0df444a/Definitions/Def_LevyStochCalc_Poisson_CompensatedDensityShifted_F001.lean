-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityShifted_F001
-- name    : LevyStochCalc_Poisson_CompensatedDensityShifted_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:53:42.566121+00:00
-- url     : https://prove2.me/theorems/94473ed6-efa1-4b1d-98e6-ff72a20ca490
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityShifted
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityShifted. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityShifted_F000
import Definitions.Def_SourceProof_87c80dd19e10f095cc23ff69

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

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- If `φ(ω, ·, e)` vanishes identically in time, so does its shifted dyadic eval. -/
lemma dyadicEvalShifted_eq_zero {T : ℝ} (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (ω : Ω) (e : E)
    (h0 : ∀ u, φ ω u e = 0) : dyadicEvalShifted T φ n s ω e = 0 := by
  unfold dyadicEvalShifted
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have havg : dyadicAvg_shifted T φ n i ω e = 0 := by
    unfold dyadicAvg_shifted
    split_ifs with h
    · rfl
    · unfold dyadicAvg; simp [h0]
  split_ifs with h
  · exact havg
  · rfl
/-- Joint `(s, e)`-measurability of the shifted eval (with `ω` fixed). -/
lemma dyadicEvalShifted_measurable_prod
    {T : ℝ} (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)) (n : ℕ) (ω : Ω) :
    Measurable (fun q : ℝ × E => dyadicEvalShifted T φ n q.1 ω q.2) := by
  unfold dyadicEvalShifted
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.ite (measurable_fst measurableSet_Ioc) ?_ measurable_const
  unfold dyadicAvg_shifted
  by_cases h : i.val = 0
  · simp only [h, ↓reduceDIte]; exact measurable_const
  · simp only [h, ↓reduceDIte]
    exact (dyadicAvg_measurable T φ h_meas n _).comp
      (by fun_prop : Measurable fun q : ℝ × E => ((ω, q.2) : Ω × E))
/-- **Per-`(ω,e)` time-`L²` convergence of the shifted eval.** -/
lemma dyadicEvalShifted_inner_L2_tendsto
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (ω : Ω) (e : E) :
    Filter.Tendsto
      (fun n => ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      Filter.atTop (nhds 0) := by
  have hM'_nn : 0 ≤ max M 0 := le_max_right _ _
  have hsq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm x).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume.restrict (Set.Icc (0 : ℝ) T)) from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun _ => ENNReal.ofReal ((2 * max M 0) ^ 2)) ?_ ?_ ?_ ?_
  · intro n
    exact ((ENNReal.continuous_coe.measurable.comp
      ((h_meas.comp (by fun_prop : Measurable fun s : ℝ => ((ω, s, e) : Ω × ℝ × E))).sub
        ((dyadicEvalShifted_measurable_prod φ h_meas n ω).comp
          (by fun_prop : Measurable fun s : ℝ => ((s, e) : ℝ × E)))).nnnorm).pow_const
            2).aemeasurable
  · intro n
    refine Filter.Eventually.of_forall (fun s => ?_)
    simp only []
    rw [hsq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb : ‖φ ω s e - dyadicEvalShifted T φ n s ω e‖ ≤ 2 * max M 0 := by
      rw [Real.norm_eq_abs]
      calc |φ ω s e - dyadicEvalShifted T φ n s ω e|
          ≤ |φ ω s e| + |dyadicEvalShifted T φ n s ω e| := abs_sub _ _
        _ ≤ max M 0 + max M 0 :=
            add_le_add ((hM ω s e).trans (le_max_left _ _))
              (dyadicEvalShifted_bounded hT φ hM n s ω e)
        _ = 2 * max M 0 := by ring
    nlinarith [norm_nonneg (φ ω s e - dyadicEvalShifted T φ n s ω e), hb, hM'_nn]
  · rw [MeasureTheory.lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _)
  · filter_upwards [_root_.Prove2MeSourceProof.h_87c80dd19e10f095cc23ff69 hT φ h_meas hM ω e] with s hs
    have hdiff : Filter.Tendsto (fun n => φ ω s e - dyadicEvalShifted T φ n s ω e)
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := φ ω s e)).sub hs
    have hg : Continuous (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 2) :=
      (ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp continuous_nnnorm)
    simpa [Function.comp_def] using (hg.tendsto 0).comp hdiff
end LevyStochCalc.Poisson.Compensated


