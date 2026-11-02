-- Prove2me | solution 1 for AuctionDuration.ClearingError.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T19:24:24.392341+00:00
-- url     : https://prove2.me/submissions/c7e8d595-66ef-416c-86f6-395c7960c26a

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Model
import Theorems.Thm_QueueingFundamentals_Foundations_poisson_count_cdf
import Theorems.Thm_AuctionDuration_ClearingError_eq_8
import Theorems.Thm_AuctionDuration_ClearingError_eq_8_mid
import Theorems.Thm_AuctionDuration_ClearingError_eq_9
import Theorems.Thm_AuctionDuration_ClearingError_lemma_A_1
import Theorems.Thm_AuctionDuration_ClearingError_lemma_A_2_eq_11
import Theorems.Thm_AuctionDuration_ClearingError_lemma_A_2_eq_12

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations
open scoped NNReal ENNReal

namespace ADPoisson

theorem countingProcess_measurable {Ω : Type*} [MeasurableSpace Ω] (T : ℕ → Ω → ℝ)
    (hT : ∀ i, Measurable (T i)) (t : ℝ) : Measurable (countingProcess T t) := by
  set A : Ω → Set ℕ := fun ω => {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t} with hA
  set F : Ω → ℝ≥0∞ := fun ω => ∑' n : ℕ, (A ω).indicator (fun _ => (1 : ℝ≥0∞)) n with hF
  have hFm : Measurable F := by
    refine Measurable.ennreal_tsum (fun n => ?_)
    have hS : Measurable (arrivalTime T n) := by
      unfold arrivalTime
      exact Finset.measurable_sum _ (fun i _ => hT i)
    have hset : MeasurableSet {ω | n ∈ A ω} := by
      by_cases hn : 1 ≤ n
      · simp only [hA, Set.mem_setOf_eq, hn, true_and]
        exact measurableSet_le hS measurable_const
      · simp [hA, hn]
    have : (fun ω => (A ω).indicator (fun _ => (1 : ℝ≥0∞)) n) =
        {ω | n ∈ A ω}.indicator (fun _ => 1) := by
      ext ω; simp [Set.indicator]
    rw [this]
    exact measurable_const.indicator hset
  have hFenc : ∀ ω, F ω = ((A ω).encard : ℝ≥0∞) := by
    intro ω
    rw [← ENNReal.tsum_set_one]
    show ∑' n : ℕ, (A ω).indicator (fun _ => (1 : ℝ≥0∞)) n = _
    rw [← tsum_subtype (A ω) (fun _ => (1 : ℝ≥0∞))]
  apply measurable_to_countable'
  intro k
  have : countingProcess T t ⁻¹' {k} =
      F ⁻¹' ({((k : ℕ∞) : ℝ≥0∞)} ∪ (if k = 0 then {⊤} else ∅)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, hFenc]
    unfold countingProcess
    rw [Set.ncard_def]
    change ENat.toNat (A ω).encard = k ↔ _
    generalize (A ω).encard = e
    induction e using ENat.recTopCoe with
    | top =>
      by_cases hk : k = 0
      · simp [hk]
      · simp [hk, eq_comm (a := 0)]
    | coe m =>
      by_cases hk : k = 0
      · simp [hk]
      · simp [hk]
  rw [this]
  exact hFm ((measurableSet_singleton _).union (by split_ifs <;> simp))

theorem Nmm_law {Ω : Type*} [MeasurableSpace Ω] (p : AuctionDuration.ClearingError.Params)
    (hmu : 0 < p.mu) (P : Measure Ω) (X : AuctionDuration.ClearingError.Auction Ω)
    (hX : AuctionDuration.ClearingError.IsModel p P X) (t : ℝ) (ht : 0 ≤ t) :
    Measurable (AuctionDuration.ClearingError.Nmm X t) ∧
    P.map (AuctionDuration.ClearingError.Nmm X t) =
      poissonMeasure ((⟨p.mu * t, mul_nonneg hmu.le ht⟩ : ℝ≥0)) := by
  obtain ⟨hPr, -, -, -, hA, -⟩ := hX
  have hm : Measurable (AuctionDuration.ClearingError.Nmm X t) :=
    countingProcess_measurable X.A hA.measurable t
  refine ⟨hm, ?_⟩
  rw [Measure.ext_iff_singleton]
  intro n
  rw [Measure.map_apply hm (measurableSet_singleton n)]
  erw [poissonMeasure_singleton]
  have h3 := (poisson_count_cdf P p.mu hmu X.A hA n t ht).2.2
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  congr 1
  change (P {ω | countingProcess X.A t ω = n}).toReal = _
  rw [h3]
  change _ = Real.exp (-(p.mu * t)) * (p.mu * t) ^ n / _
  ring

end ADPoisson

open AuctionDuration.ClearingError in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (p : Params) (hp : p.Standing)
    (P : Measure Ω) (X : Auction Ω) (hX : IsModel p P X) (h : ℝ) (hh : 0 ≤ h) :
    let c : ℝ := (1 - Real.exp (-(p.mu * h)) * (p.nu / (p.nu + p.mu)))⁻¹ * Real.exp (p.nu * h)
    Integrable (fun ω => (Pcl p X h ω - Peff p X (tauCl X h ω) ω) ^ 2) (P[|OmegaT X h]) ∧
    Integrable (fun ω => (Pmid p X h ω - Peff p X (tauCl X h ω) ω) ^ 2) (P[|OmegaT X h]) ∧
    Emid p P X h = c * ∫ t in Set.Ioi h, p.nu * Real.exp (-(p.nu * t)) *
        ((p.sigmaF ^ 2 * (t / 6) + p.sigma ^ 2) * Real.exp (-(p.mu * t)) *
            (∫ s in (0 : ℝ)..(p.mu * t), (Real.exp s - 1) / s) +
          p.sigmaF ^ 2 * (t / 3) * (1 - Real.exp (-(p.mu * t)))) ∧
    E p P X h = Emid p P X h + (∫ ω, X.J ω ^ 2 ∂P) / p.K ^ 2 * c *
        ∫ t in Set.Ioi h, p.nu * Real.exp (-(p.nu * t)) * Real.exp (-(p.mu * t)) *
          ∫ s in (0 : ℝ)..(p.mu * t), (1 / s) * ∫ u in (0 : ℝ)..s, (Real.exp u - 1) / u := by
  intro c
  have hp' := hp
  obtain ⟨hnu, hmu, hsf, hs, hK⟩ := hp'
  have hPr : IsProbabilityMeasure P := hX.1
  obtain ⟨hint8, hion8, hE8⟩ := eq_8 p hp P X hX h hh
  obtain ⟨hintm, hionm, hEm⟩ := eq_8_mid p hp P X hX h hh
  have h9 := eq_9 p hp P X hX h hh
  have hc : ((P (OmegaT X h)).toReal)⁻¹ * Real.exp (p.nu * h) = c := by rw [h9]
  -- pointwise identities at deterministic times `t > 0`
  have key : ∀ t ∈ Set.Ioi h,
      p.nu * Real.exp (-(p.nu * t)) * (gFun p P X t + p.sigma ^ 2 * fFun P X t) =
        p.nu * Real.exp (-(p.nu * t)) *
        ((p.sigmaF ^ 2 * (t / 6) + p.sigma ^ 2) * Real.exp (-(p.mu * t)) *
            (∫ s in (0 : ℝ)..(p.mu * t), (Real.exp s - 1) / s) +
          p.sigmaF ^ 2 * (t / 3) * (1 - Real.exp (-(p.mu * t)))) ∧
      p.nu * Real.exp (-(p.nu * t)) * (ellFun P X t / p.K ^ 2) =
        (∫ ω, X.J ω ^ 2 ∂P) / p.K ^ 2 *
          (p.nu * Real.exp (-(p.nu * t)) * Real.exp (-(p.mu * t)) *
          ∫ s in (0 : ℝ)..(p.mu * t), (1 / s) * ∫ u in (0 : ℝ)..s, (Real.exp u - 1) / u) := by
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt hh ht
    have hmt : 0 < p.mu * t := mul_pos hmu ht0
    obtain ⟨hNm, hlaw⟩ := ADPoisson.Nmm_law p hmu P X hX t ht0.le
    set m : ℝ≥0 := ⟨p.mu * t, mul_nonneg hmu.le ht0.le⟩ with hm
    have hmr : (m : ℝ) = p.mu * t := rfl
    have hmpos : 0 < m := by
      change (0 : ℝ) < p.mu * t
      exact hmt
    have e11 := lemma_A_2_eq_11 P (Nmm X t) hNm m hlaw
    have e12 := lemma_A_2_eq_12 P (Nmm X t) hNm m hmpos hlaw
    have a1 := (lemma_A_1 p hp P X hX t ht0).2
    rw [hmr] at e11 e12
    have r1 : ∫ ω, 1 / ((Nmm X t ω : ℝ) + 1) ^ 2 ∂P = ∫ ω, 1 / (1 + (Nmm X t ω : ℝ)) ^ 2 ∂P := by
      congr 1; ext ω; rw [add_comm]
    have r2 : ∫ ω, 1 / ((Nmm X t ω : ℝ) + 2) ^ 2 ∂P = ∫ ω, 1 / (2 + (Nmm X t ω : ℝ)) ^ 2 ∂P := by
      congr 1; ext ω; rw [add_comm]
    rw [r1, r2, e12.1, e12.2] at a1
    constructor
    · have hf : fFun P X t = Real.exp (-(p.mu * t)) *
          ∫ s in (0 : ℝ)..(p.mu * t), (Real.exp s - 1) / s := e11.1
      rw [a1, hf]
      generalize (∫ s in (0 : ℝ)..(p.mu * t), (Real.exp s - 1) / s) = I
      have hmu0 : p.mu ≠ 0 := hmu.ne'
      have ht00 : t ≠ 0 := ht0.ne'
      field_simp
      ring
    · have hl : ellFun P X t = (∫ ω, X.J ω ^ 2 ∂P) * (Real.exp (-(p.mu * t)) *
          ∫ s in (0 : ℝ)..(p.mu * t), (1 / s) * ∫ u in (0 : ℝ)..s, (Real.exp u - 1) / u) := by
        unfold ellFun
        rw [e11.2]
      rw [hl]
      ring
  refine ⟨hint8, hintm, ?_, ?_⟩
  · rw [hEm, hc]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => (key t ht).1)
  · have hsplit : ∀ t, p.nu * Real.exp (-(p.nu * t)) *
        (gFun p P X t + p.sigma ^ 2 * fFun P X t + ellFun P X t / p.K ^ 2) =
        p.nu * Real.exp (-(p.nu * t)) * (gFun p P X t + p.sigma ^ 2 * fFun P X t) +
        p.nu * Real.exp (-(p.nu * t)) * (ellFun P X t / p.K ^ 2) := fun t => by ring
    have hionl : IntegrableOn (fun t => p.nu * Real.exp (-(p.nu * t)) * (ellFun P X t / p.K ^ 2))
        (Set.Ioi h) := by
      have := hion8.sub hionm
      refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply]
      rw [hsplit t]
      ring
    rw [hE8, hc]
    simp_rw [hsplit]
    rw [integral_add hionm hionl, mul_add, hEm, hc]
    congr 1
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => (key t ht).2),
      integral_const_mul]
    ring
