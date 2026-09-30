-- Prove2me | solution 1 for AllocationIndices.interchange_portions
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T22:08:43.797866+00:00
-- url     : https://prove2.me/submissions/7095b285-b6cf-4ecf-bd6e-6953a5729003

import Mathlib
import Definitions.Def_AllocationIndices_Index

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m48_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m48_meas_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) (t : ℕ) : MeasurableSet {ω : ℕ → S | (t : ℕ∞) < τ ω} := by
  have h1 : MeasurableSet {ω : ℕ → S | τ ω ≤ (t : ℕ∞)} := by
    obtain ⟨s, hs, hse⟩ := hτ t
    rw [← hse]
    exact (measurable_pi_lambda _ (fun i ↦ measurable_pi_apply _)) hs
  have : {ω : ℕ → S | (t : ℕ∞) < τ ω} = {ω | τ ω ≤ (t : ℕ∞)}ᶜ := by
    ext ω; simp [not_le]
  rw [this]
  exact h1.compl

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m48_int_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m48_abs_int_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → ℝ) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    |∫ x, F x ∂μ| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := B)
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m48_term_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (f : S → ℝ) (Bf : ℝ)
    (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (t : ℕ) :
    ‖(if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)‖ ≤ Bf * a ^ t := by
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hf _) (pow_nonneg ha0 t)
  · simp only [norm_zero]; positivity

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m48_summable {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_left Bf)
    (p2m48_term_bound a ha0 f Bf hBf hf τ ω)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m48_dss_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    |discountedStoppedSum a f τ ω| ≤ Bf / (1 - a) := by
  unfold discountedStoppedSum
  have hg : HasSum (fun t : ℕ ↦ Bf * a ^ t) (Bf * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0 ha1).mul_left Bf
  have := tsum_of_norm_bounded hg (p2m48_term_bound a ha0 f Bf hBf hf τ ω)
  rw [Real.norm_eq_abs] at this
  rwa [div_eq_mul_inv]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m48_dss_meas {S : Type*} [MeasurableSpace S] (a : ℝ) (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum a f τ) := by
  unfold discountedStoppedSum
  exact Measurable.tsum fun t ↦ Measurable.ite (p2m48_meas_lt τ hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t))) measurable_const

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m48_dss_int {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : S → ℝ) (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) :
    Integrable (discountedStoppedSum a f τ) (markovChainMeasure P x) := by
  have := p2m48_prob P x
  exact p2m48_int_of_bound _ _ (p2m48_dss_meas a f Measurable.of_discrete τ hτ) (Bf / (1 - a))
    (p2m48_dss_bound a ha0 ha1 f Bf hBf hf τ)
open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m48_W1 {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsPositiveStoppingTime τ) (y : S) :
    1 ≤ stoppedTime P a τ y := by
  have := p2m48_prob P y
  have hr1 : ∀ y, |(fun _ : S ↦ (1 : ℝ)) y| ≤ 1 := fun y ↦ by simp
  have hint := p2m48_dss_int P y a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ hτ.1
  have hmono := integral_mono (integrable_const (1 : ℝ)) hint (fun ω ↦ by
    have hsum : Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * 1 else 0) :=
      p2m48_summable a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ ω
    have h0 : ((0 : ℕ) : ℕ∞) < τ ω := lt_of_lt_of_le (by norm_num) (hτ.2 ω)
    show (1 : ℝ) ≤ ∑' t : ℕ, (if (t : ℕ∞) < τ ω then a ^ t * 1 else 0)
    calc (1 : ℝ) = (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * 1 else 0) 0 := by
          simp only [if_pos h0]; simp
      _ ≤ _ := hsum.le_tsum 0 (fun j _ ↦ by
          split_ifs
          · positivity
          · exact le_rfl))
  rw [integral_const, probReal_univ, one_smul] at hmono
  exact hmono

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m48_ratio_le {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (hr : BoundedReward r) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (τ : (ℕ → S) → ℕ∞) (hτ : IsPositiveStoppingTime τ) (y : S) :
    stoppedReward P r a τ y ≤ gittinsIndex P r a y * stoppedTime P a τ y := by
  obtain ⟨M, hM⟩ := hr
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM y)
  have hbdd : BddAbove {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧
      (∀ ω, 1 ≤ τ ω) ∧ g = (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)} := by
    refine ⟨M / (1 - a), ?_⟩
    rintro g ⟨τ, hτ1, hτ2, rfl⟩
    have := p2m48_prob P y
    have hR := p2m48_abs_int_le (markovChainMeasure P y) _ _
      (p2m48_dss_bound a ha0 ha1 r M hM0 hM τ)
    have hW : 1 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y :=
      p2m48_W1 P a ha0 ha1 τ ⟨hτ1, hτ2⟩ y
    calc (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)
        ≤ |∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y| /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y) :=
          div_le_div_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y| :=
          div_le_self (abs_nonneg _) hW
      _ ≤ M / (1 - a) := hR
  have hWpos : 0 < stoppedTime P a τ y :=
    lt_of_lt_of_le zero_lt_one (p2m48_W1 P a ha0 ha1 τ hτ y)
  have hle : stoppedReward P r a τ y / stoppedTime P a τ y ≤ gittinsIndex P r a y := by
    unfold gittinsIndex
    exact le_csSup hbdd ⟨τ, hτ.1, hτ.2, rfl⟩
  exact (div_le_iff₀ hWpos).1 hle

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m48_disc_pt {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    (match τ ω with
      | (n : ℕ) => a ^ n
      | ⊤ => 0) = 1 - (1 - a) * discountedStoppedSum a (fun _ ↦ (1 : ℝ)) τ ω := by
  unfold discountedStoppedSum
  generalize τ ω = e
  induction e using ENat.recTopCoe with
  | top =>
    have h1 : (∑' t : ℕ, if (t : ℕ∞) < ⊤ then a ^ t * (1 : ℝ) else 0) = ∑' t : ℕ, a ^ t := by
      refine tsum_congr fun t ↦ ?_
      rw [if_pos (ENat.natCast_lt_top t), mul_one]
    have : (1 - a) ≠ 0 := by linarith
    rw [h1, tsum_geometric_of_lt_one ha0 ha1, mul_inv_cancel₀ this, sub_self]
    rfl
  | coe n =>
    have h1 : (∑' t : ℕ, if (t : ℕ∞) < (n : ℕ∞) then a ^ t * (1 : ℝ) else 0) =
        ∑ t ∈ Finset.range n, a ^ t := by
      rw [tsum_eq_sum (s := Finset.range n)]
      · refine Finset.sum_congr rfl fun t ht ↦ ?_
        rw [if_pos (by exact_mod_cast Finset.mem_range.1 ht), mul_one]
      · intro t ht
        rw [if_neg (by exact_mod_cast fun h ↦ ht (Finset.mem_range.2 h))]
    rw [h1]
    have hg := geom_sum_mul a n
    simp only
    linarith

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m48_disc {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (x : S) :
    discountAtStop P a τ x = 1 - (1 - a) * stoppedTime P a τ x := by
  have := p2m48_prob P x
  have hr1 : ∀ y, |(fun _ : S ↦ (1 : ℝ)) y| ≤ 1 := fun y ↦ by simp
  have hint := p2m48_dss_int P x a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ hτ
  have h2 : (1 : ℝ) - (1 - a) * stoppedTime P a τ x =
      ∫ ω, (1 - (1 - a) * discountedStoppedSum a (fun _ ↦ (1 : ℝ)) τ ω)
        ∂markovChainMeasure P x := by
    unfold stoppedTime
    rw [integral_sub (integrable_const (1 : ℝ)) (hint.const_mul (1 - a)), integral_const_mul,
      integral_const, probReal_univ, one_smul]
  rw [h2]
  unfold discountAtStop
  congr 1
  funext ω
  rw [← p2m48_disc_pt a ha0 ha1 τ ω]
  generalize τ ω = e
  induction e using ENat.recTopCoe with
  | top => rfl
  | coe n => rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
theorem solution {S₁ S₂ : Type*} [MeasurableSpace S₁] [Countable S₁]
    [MeasurableSingletonClass S₁] [MeasurableSpace S₂] [Countable S₂] [MeasurableSingletonClass S₂]
    (P₁ : Kernel S₁ S₁) [IsMarkovKernel P₁] {r₁ : S₁ → ℝ} (hr₁ : BoundedReward r₁)
    (P₂ : Kernel S₂ S₂) [IsMarkovKernel P₂] {r₂ : S₂ → ℝ} (hr₂ : BoundedReward r₂)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {x₁ : S₁} {x₂ : S₂}
    (hν : gittinsIndex P₂ r₂ a x₂ < gittinsIndex P₁ r₁ a x₁)
    {τ : (ℕ → S₁) → ℕ∞} (hτ : IsPositiveStoppingTime τ)
    (hτν : stoppedRatio P₁ r₁ a τ x₁ = gittinsIndex P₁ r₁ a x₁)
    {σ : (ℕ → S₂) → ℕ∞} (hσ : IsPositiveStoppingTime σ) :
    interchangeValue P₂ r₂ P₁ r₁ a σ τ x₂ x₁ < interchangeValue P₁ r₁ P₂ r₂ a τ σ x₁ x₂ := by
  have ha0' : 0 ≤ a := ha0.le
  have h1a : 0 < 1 - a := by linarith
  have hW₁ := p2m48_W1 P₁ a ha0' ha1 τ hτ x₁
  have hW₂ := p2m48_W1 P₂ a ha0' ha1 σ hσ x₂
  have hA₁ := p2m48_disc P₁ a ha0' ha1 τ hτ.1 x₁
  have hA₂ := p2m48_disc P₂ a ha0' ha1 σ hσ.1 x₂
  have hR₂ := p2m48_ratio_le P₂ r₂ hr₂ a ha0' ha1 σ hσ x₂
  have hR₁ : stoppedReward P₁ r₁ a τ x₁ = gittinsIndex P₁ r₁ a x₁ * stoppedTime P₁ a τ x₁ := by
    unfold stoppedRatio at hτν
    rw [← hτν, div_mul_cancel₀ _ (by linarith)]
  unfold interchangeValue
  rw [hA₁, hA₂, hR₁]
  set W₁ := stoppedTime P₁ a τ x₁
  set W₂ := stoppedTime P₂ a σ x₂
  set R₂ := stoppedReward P₂ r₂ a σ x₂
  set ν₁ := gittinsIndex P₁ r₁ a x₁
  set ν₂ := gittinsIndex P₂ r₂ a x₂
  have hWW : 0 < W₁ * W₂ := by positivity
  have key : W₁ * R₂ < ν₁ * W₁ * W₂ := by
    calc W₁ * R₂ ≤ W₁ * (ν₂ * W₂) := mul_le_mul_of_nonneg_left hR₂ (by linarith)
      _ = ν₂ * (W₁ * W₂) := by ring
      _ < ν₁ * (W₁ * W₂) := mul_lt_mul_of_pos_right hν hWW
      _ = ν₁ * W₁ * W₂ := by ring
  have key2 : (1 - a) * (W₁ * R₂) < (1 - a) * (ν₁ * W₁ * W₂) := mul_lt_mul_of_pos_left key h1a
  nlinarith [key2]
