-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityLimit_F001
-- name    : LevyStochCalc_Poisson_CompensatedDensityLimit_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:27:59.911341+00:00
-- url     : https://prove2.me/theorems/dae142fd-f882-4165-ac72-29af12298597
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F003
import Definitions.Def_SourceProof_4f6673f9096f52fcbaa7b357
import Definitions.Def_SourceProof_ef4425841966055a7a42ee8d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cross-resolution Cauchy estimate and the `L²` limit

The isometry for the difference of two step integrals at different dyadic resolutions, the
resulting Cauchy estimate for the Euler sums of a bounded predictable integrand, and the limit
in `L²(P)` it produces. Closing bricks on the regularity of monotone `ℝ≥0∞`-valued functions of
time and the right-continuity of the intensity of shrinking time-mark boxes support the path
regularity of that limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The mark-step eval is uniformly bounded (finite sum of bounded-coeff × indicators). -/
lemma markEval_bounded {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) {Ki : Fin N₀ → ℕ}
    (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (hcib : ∀ i k, ∃ M, ∀ ω, |ci i k ω| ≤ M) :
    ∃ C, ∀ ω s e, |∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator
        (fun _ => (1 : ℝ)) s * ∑ k, ci i k ω * (Bi i k).indicator (fun _ => (1 : ℝ)) e| ≤ C := by
  classical
  refine ⟨∑ i : Fin N₀, ∑ k, (hcib i k).choose, fun ω s e => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul]
  refine (mul_le_of_le_one_left (abs_nonneg _) (by rw [Set.indicator_apply]; split_ifs <;>
    simp)).trans ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_)))
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (by rw [Set.indicator_apply]; split_ifs <;>
    simp)).trans ((hcib i k).choose_spec ω)
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The mark-step eval vanishes for marks outside the (shared) support set `S`. -/
lemma markEval_supp {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) {Ki : Fin N₀ → ℕ}
    (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    {S : Set E} (hBiS : ∀ i k, Bi i k ⊆ S) (ω : Ω) (s : ℝ) (e : E) (he : e ∉ S) :
    (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
      * ∑ k, ci i k ω * (Bi i k).indicator (fun _ => (1 : ℝ)) e) = 0 := by
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Finset.sum_eq_zero (fun k _ => ?_), mul_zero]
  rw [Set.indicator_of_notMem (fun h => he (hBiS i k h)), mul_zero]
/-- Joint `(ω,s,e)`-measurability of the mark-step eval. -/
lemma markEval_measurable {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) {Ki : Fin N₀ → ℕ}
    (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (hBim : ∀ i k, MeasurableSet (Bi i k)) (hcim : ∀ i k, Measurable (ci i k)) :
    Measurable (fun q : Ω × ℝ × E => ∑ i : Fin N₀,
      (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) q.2.1
      * ∑ k, ci i k q.1 * (Bi i k).indicator (fun _ => (1 : ℝ)) q.2.2) := by
  refine Finset.measurable_sum _ (fun i _ => Measurable.mul ?_ ?_)
  · exact (measurable_const.indicator measurableSet_Ioc).comp (measurable_fst.comp measurable_snd)
  · refine Finset.measurable_sum _ (fun k _ => Measurable.mul ?_ ?_)
    · exact (hcim i k).comp measurable_fst
    · exact (measurable_const.indicator (hBim i k)).comp (measurable_snd.comp measurable_snd)
/-- **Cross-resolution difference isometry.** For two step approximants at dyadic
levels `n ≤ m`, the `L²(P)` distance of the integrals equals the `L²(P⊗vol⊗ν)`
distance of the integrands. The level-`n` integral/eval are re-expressed on the
level-`m` partition (`stepIntegral_dyadic_refine_integral`/`_eval`), reducing to the
same-partition `markStepIntegral_diff_isometry`. -/
lemma stepIntegral_crossres_diff_isometry
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {n
      m : ℕ}
    (hnm : n ≤ m)
    {Ki1 : Fin (2 ^ n) → ℕ} {Ki2 : Fin (2 ^ m) → ℕ}
    (Bi1 : ∀ i, Fin (Ki1 i) → Set E) (Bi2 : ∀ i, Fin (Ki2 i) → Set E)
    (ci1 : ∀ i, Fin (Ki1 i) → Ω → ℝ) (ci2 : ∀ i, Fin (Ki2 i) → Ω → ℝ)
    (hBi1m : ∀ i k, MeasurableSet (Bi1 i k)) (hBi2m : ∀ i k, MeasurableSet (Bi2 i k))
    (hBi1f : ∀ i k, ν (Bi1 i k) ≠ ⊤) (hBi2f : ∀ i k, ν (Bi2 i k) ≠ ⊤)
    (hci1b : ∀ i k, ∃ M, ∀ ω, |ci1 i k ω| ≤ M) (hci2b : ∀ i k, ∃ M, ∀ ω, |ci2 i k ω| ≤ M)
    (hci1m : ∀ i k, Measurable (ci1 i k)) (hci2m : ∀ i k, Measurable (ci2 i k))
    (hci1a : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (dyadicPartition T n i.castSucc)) (ci1 i k))
    (hci2a : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (dyadicPartition T m i.castSucc)) (ci2 i k)) :
    ∫ ω, ((∑ i : Fin (2 ^ n), ∑ k₀, ci1 i k₀ ω
          * N.compensated (Set.Ioc (dyadicPartition T n i.castSucc)
              (dyadicPartition T n i.succ) ×ˢ Bi1 i k₀) ω)
        - ∑ i : Fin (2 ^ m), ∑ k₀, ci2 i k₀ ω
          * N.compensated (Set.Ioc (dyadicPartition T m i.castSucc)
              (dyadicPartition T m i.succ) ×ˢ Bi2 i k₀) ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        ((∑ i : Fin (2 ^ n), (Set.Ioc (dyadicPartition T n i.castSucc)
              (dyadicPartition T n i.succ)).indicator (fun _ => (1 : ℝ)) s
            * ∑ k₀, ci1 i k₀ ω * (Bi1 i k₀).indicator (fun _ => (1 : ℝ)) e)
          - ∑ i : Fin (2 ^ m), (Set.Ioc (dyadicPartition T m i.castSucc)
              (dyadicPartition T m i.succ)).indicator (fun _ => (1 : ℝ)) s
            * ∑ k₀, ci2 i k₀ ω * (Bi2 i k₀).indicator (fun _ => (1 : ℝ)) e) ^ 2
        ∂volume ∂ν) ∂P := by
  -- diff isometry on (refined level-n family, level-m family) over the level-m partition.
  have hdiff := _root_.Prove2MeSourceProof.h_4f6673f9096f52fcbaa7b357 N ℱ hℱ (dyadicPartition T m)
    (dyadicPartition_zero T m) (dyadicPartition_strictMono hT m) (dyadicPartition_le_T hT m)
    (fun i' => Bi1 (dyadicCoarse n m hnm i')) Bi2
    (fun i' => ci1 (dyadicCoarse n m hnm i')) ci2
    (fun i' k => hBi1m _ k) hBi2m (fun i' k => hBi1f _ k) hBi2f
    (fun i' k => hci1b _ k) hci2b (fun i' k => hci1m _ k) hci2m
    (fun i' k => dyadic_refine_adapted N ℱ hT hnm ci1 hci1a i' k) hci2a
  have hrefI := _root_.Prove2MeSourceProof.h_ef4425841966055a7a42ee8d N hT hnm Bi1 ci1 hBi1m hBi1f
  have hrefE := stepIntegral_dyadic_refine_eval (E := E) hT hnm Bi1 ci1
  rw [show ∫ ω, ((∑ i : Fin (2 ^ n), ∑ k₀, ci1 i k₀ ω
          * N.compensated (Set.Ioc (dyadicPartition T n i.castSucc)
              (dyadicPartition T n i.succ) ×ˢ Bi1 i k₀) ω)
        - ∑ i : Fin (2 ^ m), ∑ k₀, ci2 i k₀ ω
          * N.compensated (Set.Ioc (dyadicPartition T m i.castSucc)
              (dyadicPartition T m i.succ) ×ˢ Bi2 i k₀) ω) ^ 2 ∂P
      = ∫ ω, ((∑ i' : Fin (2 ^ m), ∑ k₀, ci1 (dyadicCoarse n m hnm i') k₀ ω
          * N.compensated (Set.Ioc (dyadicPartition T m i'.castSucc)
              (dyadicPartition T m i'.succ) ×ˢ Bi1 (dyadicCoarse n m hnm i') k₀) ω)
        - ∑ i : Fin (2 ^ m), ∑ k₀, ci2 i k₀ ω
          * N.compensated (Set.Ioc (dyadicPartition T m i.castSucc)
              (dyadicPartition T m i.succ) ×ˢ Bi2 i k₀) ω) ^ 2 ∂P from by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hrefI] with ω h
    rw [h]]
  rw [hdiff]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  refine congrArg _ (funext (fun e => ?_))
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
  rw [hrefE s ω e]
/-! ### Path regularity bricks (toward the càdlàg conjunct of #6)

The compensated step integral is càdlàg in `t`: the compensator part is continuous,
and the count part is a Stieltjes function of `t` (monotone, right-continuous with
left limits via measure continuity). These bricks give the right-continuity and
left-limit existence of monotone `ℝ≥0∞`-valued functions, the substrate for the
Doob `L²` càdlàg modification. -/

end LevyStochCalc.Poisson.Compensated


