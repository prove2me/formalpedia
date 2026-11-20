-- Prove2me | Definitions.Def_SourceProof_95164fb14a286c888ca62b65
-- name    : SourceProof_95164fb14a286c888ca62b65
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T23:47:03.486218+00:00
-- url     : https://prove2.me/theorems/e7b77233-101e-4469-a0bb-e3125ab8a58d
-- title:
--   LevyStochCalc source module: SourceProof_95164fb14a286c888ca62b65
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.exists_markEval_close_dyadic` comes from the `LevyStochCalc.Poisson.CompensatedDensityMarkApprox` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F000
import Definitions.Def_SourceProof_70fcd50878719934569bf3db

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


theorem _root_.Prove2MeSourceProof.h_95164fb14a286c888ca62b65
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ} (hT : 0 < T)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M)
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hSupp : ∀ ω e, e ∉ S → ∀ u, φ ω u e = 0)
    (n : ℕ) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ (Ki : Fin (2 ^ n) → ℕ) (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ),
      (∀ i k, MeasurableSet (Bi i k)) ∧ (∀ i k, Bi i k ⊆ S) ∧
      (∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (dyadicPartition T n i.castSucc))
        (ci i k)) ∧
      (∀ i k, ∃ C, ∀ ω, |ci i k ω| ≤ C) ∧
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖dyadicEvalShifted T φ n s ω e
          - ∑ i : Fin (2 ^ n),
              (Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ)).indicator
                (fun _ => (1 : ℝ)) s
              * ∑ k, ci i k ω * (Bi i k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P ≤ ENNReal.ofReal T * δ := by
  classical
  -- per-piece mark approximation of each shifted dyadic average.
  have hpiece : ∀ i : Fin (2 ^ n), ∃ (K : ℕ) (B : Fin K → Set E) (c : Fin K → Ω → ℝ),
      (∀ k, MeasurableSet (B k)) ∧ (∀ k, B k ⊆ S) ∧
      (∀ k, @Measurable Ω ℝ
        (ℱ (LevyStochCalc.Poisson.Compensated.dyadicPartition T n i.castSucc)) _ (c k)) ∧
      (∀ k, ∃ C, ∀ ω, |c k ω| ≤ C) ∧
      ∫⁻ ω, ∫⁻ e, (‖LevyStochCalc.Poisson.Compensated.dyadicAvg_shifted T φ n i ω e
          - ∑ k, c k ω * (B k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P ≤ δ := by
    intro i
    have hsupp_i : ∀ ω e, e ∉ S → LevyStochCalc.Poisson.Compensated.dyadicAvg_shifted T φ n i ω e = 0 := by
      intro ω e he
      unfold LevyStochCalc.Poisson.Compensated.dyadicAvg_shifted
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · simp only [hi0, ↓reduceDIte, LevyStochCalc.Poisson.Compensated.dyadicAvg]
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
          (fun s _ => hSupp ω e he s)]
        simp
    exact _root_.Prove2MeSourceProof.h_70fcd50878719934569bf3db (ℱ.le _)
      (LevyStochCalc.Poisson.Compensated.dyadicAvg_shifted T φ n i) (LevyStochCalc.Poisson.Compensated.dyadicAvg_shifted_adapted_prod N ℱ T φ h_progMeas n i)
      (LevyStochCalc.Poisson.Compensated.dyadicAvg_shifted_bounded hT φ hM n i) hS hSfin hsupp_i hδ
  choose Ki Bi ci hBim hBiS hcim hcib hci_err using hpiece
  refine ⟨Ki, Bi, ci, hBim, hBiS, fun i k => (hcim i k).stronglyMeasurable, hcib, ?_⟩
  -- abbreviations.
  set p := LevyStochCalc.Poisson.Compensated.dyadicPartition T n with hp
  set d : Fin (2 ^ n) → Ω → E → ℝ := fun i ω e => LevyStochCalc.Poisson.Compensated.dyadicAvg_shifted T φ n i ω e with hd
  set mk : Fin (2 ^ n) → Ω → E → ℝ :=
    fun i ω e => ∑ k, ci i k ω * (Bi i k).indicator (fun _ => (1 : ℝ)) e with hmk
  set W : Fin (2 ^ n) → Ω → ℝ≥0∞ :=
    fun i ω => ∫⁻ e, (‖d i ω e - mk i ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν with hW
  -- joint `(ω,e)`-measurability of each piece's squared difference.
  have hd2 : ∀ i, Measurable (fun q : Ω × E => d i q.1 q.2) :=
    fun i => LevyStochCalc.Poisson.Compensated.dyadicAvg_shifted_measurable T φ h_meas n i
  have hmk2 : ∀ i, Measurable (fun q : Ω × E => mk i q.1 q.2) := by
    intro i
    refine Finset.measurable_sum _ (fun k _ => ?_)
    exact (((hcim i k).mono (ℱ.le _) le_rfl).comp
      measurable_fst).mul ((measurable_const.indicator (hBim i k)).comp measurable_snd)
  have hjoint : ∀ i, Measurable (fun q : Ω × E => (‖d i q.1 q.2 - mk i q.1 q.2‖₊ : ℝ≥0∞) ^ 2) :=
    fun i => (ENNReal.continuous_coe.measurable.comp ((hd2 i).sub (hmk2 i)).nnnorm).pow_const 2
  have hW_meas : ∀ i, Measurable (W i) := fun i => (hjoint i).lintegral_prod_right'
  -- pointwise collapse of the squared difference.
  have hcollapse : ∀ s ω e,
      (‖LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e
        - ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
            * mk i ω e‖₊ : ℝ≥0∞) ^ 2
        = ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator
            (fun _ => (‖d i ω e - mk i ω e‖₊ : ℝ≥0∞) ^ 2) s := by
    intro s ω e
    have hDES : LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e
        = ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
            * d i ω e := by
      unfold LevyStochCalc.Poisson.Compensated.dyadicEvalShifted
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Set.indicator_apply]
      by_cases hsi : s ∈ Set.Ioc (p i.castSucc) (p i.succ)
      · rw [if_pos (Set.mem_Ioc.mp hsi), if_pos hsi, one_mul]
      · rw [if_neg (fun hc => hsi (Set.mem_Ioc.mpr hc)), if_neg hsi, zero_mul]
    rw [hDES, ← Finset.sum_sub_distrib]
    rw [show (∑ i : Fin (2 ^ n), ((Set.Ioc (p i.castSucc) (p i.succ)).indicator
            (fun _ => (1 : ℝ)) s * d i ω e
          - (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s * mk i ω e))
        = ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
            * (d i ω e - mk i ω e) from by
      refine Finset.sum_congr rfl (fun i _ => by ring)]
    exact LevyStochCalc.Poisson.Compensated.sq_nnnorm_disjoint_indicator_sum p (LevyStochCalc.Poisson.Compensated.dyadicPartition_strictMono hT n)
      (fun i => d i ω e - mk i ω e) s
  -- measurability of each per-piece integrand in `e`.
  have hmk_meas : ∀ i ω, Measurable (fun e => mk i ω e) := by
    intro i ω
    exact Finset.measurable_sum _ (fun k _ => (measurable_const.mul
      (measurable_const.indicator (hBim i k))))
  have hd_meas : ∀ i ω, Measurable (fun e => d i ω e) :=
    fun i ω => (hd2 i).comp measurable_prodMk_left
  have hgi_meas : ∀ i ω, Measurable (fun e => (‖d i ω e - mk i ω e‖₊ : ℝ≥0∞) ^ 2) := by
    intro i ω
    exact (ENNReal.continuous_coe.measurable.comp
      ((hd_meas i ω).sub (hmk_meas i ω)).nnnorm).pow_const 2
  -- collapse the `e`-integral to `∑ᵢ 𝟙_{Iᵢ}(s)·Wᵢ(ω)`.
  have h_e : ∀ s ω, ∫⁻ e,
      (‖LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e
        - ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
            * mk i ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      = ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator
          (fun _ => W i ω) s := by
    intro s ω
    rw [show (fun e => (‖LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e
          - ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
              * mk i ω e‖₊ : ℝ≥0∞) ^ 2)
        = fun e => ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator
            (fun _ => (‖d i ω e - mk i ω e‖₊ : ℝ≥0∞) ^ 2) s
        from funext (fun e => hcollapse s ω e)]
    rw [MeasureTheory.lintegral_finsetSum _ (fun i _ => by
      by_cases hsi : s ∈ Set.Ioc (p i.castSucc) (p i.succ)
      · simp only [Set.indicator_of_mem hsi]; exact hgi_meas i ω
      · simp only [Set.indicator_of_notMem hsi]; exact measurable_const)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hsi : s ∈ Set.Ioc (p i.castSucc) (p i.succ)
    · simp only [Set.indicator_of_mem hsi]; rfl
    · simp only [Set.indicator_of_notMem hsi, lintegral_zero]
  -- collapse the `s`-integral to `∑ᵢ vol(Iᵢ)·Wᵢ(ω)`.
  have h_s : ∀ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => W i ω) s)
      ∂volume
      = ∑ i : Fin (2 ^ n),
          volume (Set.Ioc (p i.castSucc) (p i.succ) ∩ Set.Icc (0 : ℝ) T) * W i ω := by
    intro ω
    rw [MeasureTheory.lintegral_finsetSum _ (fun i _ =>
      (measurable_const.indicator measurableSet_Ioc))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.lintegral_indicator measurableSet_Ioc,
      MeasureTheory.setLIntegral_const, Measure.restrict_apply measurableSet_Ioc, mul_comm]
  -- assemble: integrate `ω`, factor the volumes, bound by `δ`.
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖LevyStochCalc.Poisson.Compensated.dyadicEvalShifted T φ n s ω e
            - ∑ i : Fin (2 ^ n), (Set.Ioc (p i.castSucc) (p i.succ)).indicator
                (fun _ => (1 : ℝ)) s * mk i ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      = ∫⁻ ω, ∑ i : Fin (2 ^ n),
          volume (Set.Ioc (p i.castSucc) (p i.succ) ∩ Set.Icc (0 : ℝ) T) * W i ω ∂P := by
        refine lintegral_congr (fun ω => ?_)
        rw [← h_s ω]
        refine lintegral_congr (fun s => ?_)
        exact h_e s ω
    _ = ∑ i : Fin (2 ^ n),
          volume (Set.Ioc (p i.castSucc) (p i.succ) ∩ Set.Icc (0 : ℝ) T) * ∫⁻ ω, W i ω ∂P := by
        rw [MeasureTheory.lintegral_finsetSum _
          (fun i _ => (hW_meas i).const_mul _)]
        exact Finset.sum_congr rfl (fun i _ => by
          rw [MeasureTheory.lintegral_const_mul _ (hW_meas i)])
    _ ≤ ∑ i : Fin (2 ^ n),
          volume (Set.Ioc (p i.castSucc) (p i.succ) ∩ Set.Icc (0 : ℝ) T) * δ := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact mul_le_mul_right (hci_err i) _
    _ = (∑ i : Fin (2 ^ n),
          volume (Set.Ioc (p i.castSucc) (p i.succ) ∩ Set.Icc (0 : ℝ) T)) * δ := by
        rw [Finset.sum_mul]
    _ ≤ ENNReal.ofReal T * δ := by
        refine mul_le_mul_left ?_ δ
        calc ∑ i : Fin (2 ^ n),
              volume (Set.Ioc (p i.castSucc) (p i.succ) ∩ Set.Icc (0 : ℝ) T)
            ≤ ∑ i : Fin (2 ^ n), volume (Set.Ioc (p i.castSucc) (p i.succ)) :=
              Finset.sum_le_sum (fun i _ => measure_mono Set.inter_subset_left)
          _ = ∑ _i : Fin (2 ^ n), ENNReal.ofReal (T / (2 ^ n : ℕ)) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [hp, Real.volume_Ioc, LevyStochCalc.Poisson.Compensated.dyadicPartition_diff]
          _ = ENNReal.ofReal T := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              have h2 : (2 ^ n : ℝ) ≠ 0 := by positivity
              push_cast
              field_simp
end LevyStochCalc.Poisson.Compensated


