-- Prove2me | solution 1 for AllocationIndices.fair_charge_characterization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T12:04:04.657837+00:00
-- url     : https://prove2.me/submissions/571edea4-558b-446b-8fc2-91366e9d49c4

import Mathlib
import Definitions.Def_AllocationIndices_Index

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2me1_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2me1_meas_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
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
private lemma p2me1_int_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2me1_abs_int_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → ℝ) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    |∫ x, F x ∂μ| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := B)
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2me1_term_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (f : S → ℝ) (Bf : ℝ)
    (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (t : ℕ) :
    ‖(if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)‖ ≤ Bf * a ^ t := by
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hf _) (pow_nonneg ha0 t)
  · simp only [norm_zero]; positivity

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2me1_summable {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_left Bf)
    (p2me1_term_bound a ha0 f Bf hBf hf τ ω)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2me1_dss_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    |discountedStoppedSum a f τ ω| ≤ Bf / (1 - a) := by
  unfold discountedStoppedSum
  have hg : HasSum (fun t : ℕ ↦ Bf * a ^ t) (Bf * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0 ha1).mul_left Bf
  have := tsum_of_norm_bounded hg (p2me1_term_bound a ha0 f Bf hBf hf τ ω)
  rw [Real.norm_eq_abs] at this
  rwa [div_eq_mul_inv]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2me1_dss_meas {S : Type*} [MeasurableSpace S] (a : ℝ) (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum a f τ) := by
  unfold discountedStoppedSum
  exact Measurable.tsum fun t ↦ Measurable.ite (p2me1_meas_lt τ hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t))) measurable_const

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2me1_dss_int {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : S → ℝ) (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) :
    Integrable (discountedStoppedSum a f τ) (markovChainMeasure P x) := by
  have := p2me1_prob P x
  exact p2me1_int_of_bound _ _ (p2me1_dss_meas a f Measurable.of_discrete τ hτ) (Bf / (1 - a))
    (p2me1_dss_bound a ha0 ha1 f Bf hBf hf τ)
open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2me1_W1 {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsPositiveStoppingTime τ) (y : S) :
    1 ≤ stoppedTime P a τ y := by
  have := p2me1_prob P y
  have hr1 : ∀ y, |(fun _ : S ↦ (1 : ℝ)) y| ≤ 1 := fun y ↦ by simp
  have hint := p2me1_dss_int P y a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ hτ.1
  have hmono := integral_mono (integrable_const (1 : ℝ)) hint (fun ω ↦ by
    have hsum : Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * 1 else 0) :=
      p2me1_summable a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ ω
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
private lemma p2me1_ratio_le {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
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
    have := p2me1_prob P y
    have hR := p2me1_abs_int_le (markovChainMeasure P y) _ _
      (p2me1_dss_bound a ha0 ha1 r M hM0 hM τ)
    have hW : 1 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y :=
      p2me1_W1 P a ha0 ha1 τ ⟨hτ1, hτ2⟩ y
    calc (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)
        ≤ |∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y| /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y) :=
          div_le_div_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y| :=
          div_le_self (abs_nonneg _) hW
      _ ≤ M / (1 - a) := hR
  have hWpos : 0 < stoppedTime P a τ y :=
    lt_of_lt_of_le zero_lt_one (p2me1_W1 P a ha0 ha1 τ hτ y)
  have hle : stoppedReward P r a τ y / stoppedTime P a τ y ≤ gittinsIndex P r a y := by
    unfold gittinsIndex
    exact le_csSup hbdd ⟨τ, hτ.1, hτ.2, rfl⟩
  exact (div_le_iff₀ hWpos).1 hle


open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2me1_bdd {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (hr : BoundedReward r) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (y : S) :
    BddAbove {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧
      (∀ ω, 1 ≤ τ ω) ∧ g = (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)} := by
  obtain ⟨M, hM⟩ := hr
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM y)
  refine ⟨M / (1 - a), ?_⟩
  rintro g ⟨τ, hτ1, hτ2, rfl⟩
  have := p2me1_prob P y
  have hR := p2me1_abs_int_le (markovChainMeasure P y) _ _
    (p2me1_dss_bound a ha0 ha1 r M hM0 hM τ)
  have hW : 1 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y :=
    p2me1_W1 P a ha0 ha1 τ ⟨hτ1, hτ2⟩ y
  calc (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)
      ≤ |∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y| /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y) :=
        div_le_div_of_nonneg_right (le_abs_self _) (by linarith)
    _ ≤ |∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y| :=
        div_le_self (abs_nonneg _) hW
    _ ≤ M / (1 - a) := hR

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2me1_one {S : Type*} [MeasurableSpace S] :
    IsPositiveStoppingTime (fun _ : ℕ → S ↦ (1 : ℕ∞)) := by
  refine ⟨fun n ↦ ?_, fun _ ↦ le_rfl⟩
  by_cases h : (1 : ℕ∞) ≤ (n : ℕ∞)
  · simp only [h, Set.ofPred_true]; exact @MeasurableSet.univ _ (trajectoryFiltration S n)
  · simp only [h, Set.ofPred_false]; exact @MeasurableSet.empty _ (trajectoryFiltration S n)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2me1_fam_bdd {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (hr : BoundedReward r) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (y : S) (lam : ℝ) :
    BddAbove (Set.range fun τ : {τ : (ℕ → S) → ℕ∞ // IsPositiveStoppingTime τ} ↦
      stoppedReward P r a τ y - lam * stoppedTime P a τ y) := by
  obtain ⟨M, hM⟩ := hr
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM y)
  refine ⟨M / (1 - a) + |lam| * (1 / (1 - a)), ?_⟩
  rintro _ ⟨τ, rfl⟩
  have := p2me1_prob P y
  have hR := p2me1_abs_int_le (markovChainMeasure P y) _ _
    (p2me1_dss_bound a ha0 ha1 r M hM0 hM τ.1)
  have hr1 : ∀ y, |(fun _ : S ↦ (1 : ℝ)) y| ≤ 1 := fun y ↦ by simp
  have hW := p2me1_abs_int_le (markovChainMeasure P y) _ _
    (p2me1_dss_bound a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ.1)
  have hR' : stoppedReward P r a τ y ≤ M / (1 - a) := le_trans (le_abs_self _) hR
  have hW' : |stoppedTime P a τ y| ≤ 1 / (1 - a) := hW
  have : -(lam * stoppedTime P a τ y) ≤ |lam| * (1 / (1 - a)) := by
    calc -(lam * stoppedTime P a τ y) ≤ |lam * stoppedTime P a τ y| := neg_le_abs _
      _ = |lam| * |stoppedTime P a τ y| := abs_mul _ _
      _ ≤ |lam| * (1 / (1 - a)) := mul_le_mul_of_nonneg_left hW' (abs_nonneg _)
  show stoppedReward P r a τ y - lam * stoppedTime P a τ y ≤ _
  linarith

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
theorem solution {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (x : S) :
    gittinsIndex P r a x = sSup {lam : ℝ | 0 ≤ fairChargeProfit P r a x lam} := by
  have ha0' : 0 ≤ a := ha0.le
  have : Nonempty {τ : (ℕ → S) → ℕ∞ // IsPositiveStoppingTime τ} := ⟨⟨_, p2me1_one⟩⟩
  -- every ratio lies in the fair-charge set
  have step1 : ∀ τ : (ℕ → S) → ℕ∞, IsPositiveStoppingTime τ →
      0 ≤ fairChargeProfit P r a x (stoppedReward P r a τ x / stoppedTime P a τ x) := by
    intro τ hτ
    have hW : 1 ≤ stoppedTime P a τ x := p2me1_W1 P a ha0' ha1 τ hτ x
    have hle := le_ciSup (p2me1_fam_bdd P r hr a ha0' ha1 x
      (stoppedReward P r a τ x / stoppedTime P a τ x)) ⟨τ, hτ⟩
    unfold fairChargeProfit
    refine le_trans (le_of_eq ?_) hle
    show (0 : ℝ) = stoppedReward P r a τ x -
      stoppedReward P r a τ x / stoppedTime P a τ x * stoppedTime P a τ x
    rw [div_mul_cancel₀ _ (by linarith)]; ring
  -- every element of the fair-charge set is at most the index
  have step2 : ∀ lam, 0 ≤ fairChargeProfit P r a x lam → lam ≤ gittinsIndex P r a x := by
    intro lam hlam
    by_contra hcon
    rw [not_le] at hcon
    have hF : fairChargeProfit P r a x lam ≤ gittinsIndex P r a x - lam := by
      unfold fairChargeProfit
      refine ciSup_le fun τ ↦ ?_
      have hW : 1 ≤ stoppedTime P a τ.1 x := p2me1_W1 P a ha0' ha1 τ.1 τ.2 x
      have hR := p2me1_ratio_le P r hr a ha0' ha1 τ.1 τ.2 x
      have : (gittinsIndex P r a x - lam) * stoppedTime P a τ.1 x ≤
          (gittinsIndex P r a x - lam) * 1 :=
        mul_le_mul_of_nonpos_left hW (by linarith)
      nlinarith
    linarith
  have hbddA : BddAbove {lam : ℝ | 0 ≤ fairChargeProfit P r a x lam} :=
    ⟨gittinsIndex P r a x, fun lam h ↦ step2 lam h⟩
  have hneA : ({lam : ℝ | 0 ≤ fairChargeProfit P r a x lam}).Nonempty :=
    ⟨_, step1 _ p2me1_one⟩
  apply le_antisymm
  · unfold gittinsIndex
    refine csSup_le ⟨_, _, p2me1_one.1, p2me1_one.2, rfl⟩ ?_
    rintro g ⟨τ, h1, h2, rfl⟩
    exact le_csSup hbddA (step1 τ ⟨h1, h2⟩)
  · exact csSup_le hneA fun lam h ↦ step2 lam h
