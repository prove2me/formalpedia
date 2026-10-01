-- Prove2me | solution 1 for AllocationIndices.index_eq_reward_of_reward_nonincreasing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T15:02:16.10702+00:00
-- url     : https://prove2.me/submissions/6c2f58e4-ec1f-4e6e-ad41-0b5a917b2833

import Mathlib
import Definitions.Def_AllocationIndices_Index

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_marg0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : (markovChainMeasure P x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_int0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) (F : S → ℝ) (hF : Measurable F) :
    ∫ ω, F (ω 0) ∂markovChainMeasure P x = F x := by
  have hFm : Measurable (fun h : (Π _i : Finset.Iic 0, S) ↦ F (h ⟨0, Finset.mem_Iic.2 le_rfl⟩)) :=
    hF.comp (measurable_pi_apply _)
  have h1 := integral_map (μ := markovChainMeasure P x) (Preorder.measurable_frestrictLe 0).aemeasurable
    hFm.aestronglyMeasurable
  rw [p2m60_marg0, integral_dirac' _ _ hFm.stronglyMeasurable] at h1
  exact h1.symm

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_meas_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
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
private lemma p2m60_filt_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) (t : ℕ) :
    MeasurableSet[trajectoryFiltration S t] {ω : ℕ → S | (t : ℕ∞) < τ ω} := by
  have : {ω : ℕ → S | (t : ℕ∞) < τ ω} = {ω | τ ω ≤ (t : ℕ∞)}ᶜ := by
    ext ω; simp [not_le]
  rw [this]
  exact (hτ t).compl

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_int_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_abs_int_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → ℝ) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    |∫ x, F x ∂μ| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := B)
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_term_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (f : S → ℝ) (Bf : ℝ)
    (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (t : ℕ) :
    ‖(if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)‖ ≤ Bf * a ^ t := by
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hf _) (pow_nonneg ha0 t)
  · simp only [norm_zero]; positivity

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_summable {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_left Bf)
    (p2m60_term_bound a ha0 f Bf hBf hf τ ω)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_dss_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    |discountedStoppedSum a f τ ω| ≤ Bf / (1 - a) := by
  unfold discountedStoppedSum
  have hg : HasSum (fun t : ℕ ↦ Bf * a ^ t) (Bf * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0 ha1).mul_left Bf
  have := tsum_of_norm_bounded hg (p2m60_term_bound a ha0 f Bf hBf hf τ ω)
  rw [Real.norm_eq_abs] at this
  rwa [div_eq_mul_inv]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_tail {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (N : ℕ) :
    |discountedStoppedSum a f τ ω -
        ∑ t ∈ Finset.range N, (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)| ≤
      Bf * a ^ N / (1 - a) := by
  unfold discountedStoppedSum
  have hs := p2m60_summable a ha0 ha1 f Bf hBf hf τ ω
  rw [← hs.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have hg : HasSum (fun t : ℕ ↦ Bf * a ^ N * a ^ t) (Bf * a ^ N * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0 ha1).mul_left (Bf * a ^ N)
  have := tsum_of_norm_bounded hg (fun t ↦ by
    have h := p2m60_term_bound a ha0 f Bf hBf hf τ ω (t + N)
    calc _ ≤ Bf * a ^ (t + N) := h
      _ = Bf * a ^ N * a ^ t := by ring)
  rw [Real.norm_eq_abs] at this
  rwa [div_eq_mul_inv]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_dss_meas {S : Type*} [MeasurableSpace S] (a : ℝ) (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum a f τ) := by
  unfold discountedStoppedSum
  exact Measurable.tsum fun t ↦ Measurable.ite (p2m60_meas_lt τ hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t))) measurable_const

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_dss_int {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : S → ℝ) (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) :
    Integrable (discountedStoppedSum a f τ) (markovChainMeasure P x) := by
  haveI := p2m60_prob P x
  exact p2m60_int_of_bound _ _ (p2m60_dss_meas a f Measurable.of_discrete τ hτ) (Bf / (1 - a))
    (p2m60_dss_bound a ha0 ha1 f Bf hBf hf τ)


open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m60_dss_one {S : Type*} (a : ℝ) (f : S → ℝ) (ω : ℕ → S) :
    discountedStoppedSum a f (fun _ ↦ 1) ω = f (ω 0) := by
  unfold discountedStoppedSum
  rw [tsum_eq_single 0]
  · simp
  · intro t ht
    have : ¬ ((t : ℕ∞) < 1) := by
      intro h
      apply ht
      have : t < 1 := by exact_mod_cast h
      omega
    rw [if_neg this]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_ae0 {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    ∀ᵐ ω ∂markovChainMeasure P x, ω 0 = x := by
  have hm : Measurable (fun h : (Π _i : Finset.Iic 0, S) ↦ h ⟨0, Finset.mem_Iic.2 le_rfl⟩) :=
    measurable_pi_apply _
  have h1 : ∀ᵐ h ∂(markovChainMeasure P x).map (Preorder.frestrictLe 0),
      h ⟨0, Finset.mem_Iic.2 le_rfl⟩ = x := by
    rw [p2m60_marg0]
    exact (ae_dirac_iff (p := fun h : (Π _i : Finset.Iic 0, S) ↦ h ⟨0, Finset.mem_Iic.2 le_rfl⟩ = x)
      (hm (measurableSet_singleton x))).2 rfl
  exact ae_of_ae_map (Preorder.measurable_frestrictLe 0).aemeasurable h1

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_pt {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (r : S → ℝ)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ y, |r y| ≤ M) (x : S) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S)
    (h0 : ω 0 = x) (h1 : ∀ t : ℕ, 1 ≤ t → r (ω t) ≤ r x) :
    discountedStoppedSum a r τ ω ≤ r x * discountedStoppedSum a (fun _ ↦ 1) τ ω := by
  unfold discountedStoppedSum
  rw [← tsum_mul_left]
  refine (p2m60_summable a ha0 ha1 r M hM0 hM τ ω).tsum_le_tsum (fun t ↦ ?_)
    ((p2m60_summable a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one
      (fun _ ↦ by simp) τ ω).mul_left (r x))
  split_ifs with ht
  · rcases Nat.eq_zero_or_pos t with h | h
    · subst h; rw [h0]; simp
    · have := h1 t h
      have hp : 0 ≤ a ^ t := pow_nonneg ha0 t
      nlinarith
  · simp

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m60_W1 {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (τ : (ℕ → S) → ℕ∞) (hτ1 : ∀ ω, 1 ≤ τ ω) (ω : ℕ → S) :
    1 ≤ discountedStoppedSum a (fun _ ↦ 1) τ ω := by
  unfold discountedStoppedSum
  have hs := p2m60_summable a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one (fun _ ↦ by simp) τ ω
  rw [hs.tsum_eq_zero_add]
  have h0 : ((0 : ℕ) : ℕ∞) < τ ω := lt_of_lt_of_le (by norm_num) (hτ1 ω)
  rw [if_pos h0]
  have : 0 ≤ ∑' t : ℕ, (if ((t + 1 : ℕ) : ℕ∞) < τ ω then a ^ (t + 1) * (1 : ℝ) else 0) :=
    tsum_nonneg fun t ↦ by split_ifs <;> positivity
  simp only [pow_zero, mul_one] at this ⊢
  linarith

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
theorem solution {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (x : S)
    (h : markovChainMeasure P x {ω | ∀ t : ℕ, 1 ≤ t → r (ω t) ≤ r x} = 1) :
    stoppedRatio P r a (fun _ ↦ 1) x = gittinsIndex P r a x ∧ gittinsIndex P r a x = r x := by
  obtain ⟨M, hM⟩ := hr
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM x)
  haveI := p2m60_prob P x
  have hOne : stoppedRatio P r a (fun _ ↦ 1) x = r x := by
    unfold stoppedRatio stoppedReward stoppedTime
    simp_rw [p2m60_dss_one]
    rw [p2m60_int0 P x r Measurable.of_discrete]
    simp
  have hmeas : MeasurableSet {ω : ℕ → S | ∀ t : ℕ, 1 ≤ t → r (ω t) ≤ r x} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun t ↦ MeasurableSet.iInter fun _ ↦
      measurableSet_le ((Measurable.of_discrete (f := r)).comp (measurable_pi_apply t))
        measurable_const
  have hs : ∀ᵐ ω ∂markovChainMeasure P x, ∀ t : ℕ, 1 ≤ t → r (ω t) ≤ r x := by
    have h0 : markovChainMeasure P x {ω : ℕ → S | ∀ t : ℕ, 1 ≤ t → r (ω t) ≤ r x}ᶜ = 0 := by
      rw [measure_compl hmeas (measure_ne_top _ _), h, measure_univ]
      simp
    exact mem_ae_iff.2 h0
  have hup : ∀ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ → (∀ ω, 1 ≤ τ ω) →
      (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P x) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x) ≤ r x := by
    intro τ hτ hτ1
    have hW : 1 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x := by
      have := integral_mono (μ := markovChainMeasure P x) (integrable_const (1 : ℝ))
        (p2m60_dss_int P x a ha0.le ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one (fun _ ↦ by simp) τ hτ)
        (fun ω ↦ p2m60_W1 a ha0.le ha1 τ hτ1 ω)
      simpa using this
    rw [div_le_iff₀ (by linarith)]
    rw [← integral_const_mul]
    refine integral_mono_ae (p2m60_dss_int P x a ha0.le ha1 r M hM0 hM τ hτ)
      ((p2m60_dss_int P x a ha0.le ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one
        (fun _ ↦ by simp) τ hτ).const_mul (r x)) ?_
    filter_upwards [hs, p2m60_ae0 P x] with ω hω h0
    exact p2m60_pt a ha0.le ha1 r M hM0 hM x τ ω h0 hω
  have hG : gittinsIndex P r a x = r x := by
    unfold gittinsIndex
    apply IsGreatest.csSup_eq
    refine ⟨⟨fun _ ↦ 1, fun n ↦ MeasurableSet.const _, fun _ ↦ le_rfl, ?_⟩, ?_⟩
    · have := hOne
      unfold stoppedRatio stoppedReward stoppedTime at this
      exact this.symm
    · rintro g ⟨τ, hτ, hτ1, rfl⟩
      exact hup τ hτ hτ1
  exact ⟨hOne.trans hG.symm, hG⟩
