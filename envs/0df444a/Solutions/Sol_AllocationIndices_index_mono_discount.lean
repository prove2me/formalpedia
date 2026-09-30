-- Prove2me | solution 1 for AllocationIndices.index_mono_discount
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T10:56:55.323966+00:00
-- url     : https://prove2.me/submissions/65774024-ca34-43fe-8f05-0cc4f662a379

import Mathlib
import Definitions.Def_AllocationIndices_Index

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mfc_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mfc_meas_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
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
private lemma p2mfc_meas_term {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ)
    (α : ℝ) (f : S → ℝ) (t : ℕ) :
    Measurable (fun ω : ℕ → S ↦ if (t : ℕ∞) < τ ω then α ^ t * f (ω t) else 0) := by
  refine Measurable.ite (p2mfc_meas_lt τ hτ t) ?_ measurable_const
  exact measurable_const.mul ((measurable_of_countable f).comp (measurable_pi_apply t))

private lemma p2mfc_norm_term {S : Type*} (τ : (ℕ → S) → ℕ∞) {α C : ℝ} (hα : 0 ≤ α)
    (f : S → ℝ) (hf : ∀ y, |f y| ≤ C) (t : ℕ) (ω : ℕ → S) :
    ‖(if (t : ℕ∞) < τ ω then α ^ t * f (ω t) else 0)‖ ≤ α ^ t * C := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hf (ω 0))
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hα t)]
    exact mul_le_mul_of_nonneg_left (hf _) (pow_nonneg hα t)
  · simp only [norm_zero]; exact mul_nonneg (pow_nonneg hα t) hC

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mfc_int_term {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] (x : S)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) {α C : ℝ} (hα : 0 ≤ α)
    (f : S → ℝ) (hf : ∀ y, |f y| ≤ C) (t : ℕ) :
    Integrable (fun ω : ℕ → S ↦ if (t : ℕ∞) < τ ω then α ^ t * f (ω t) else 0)
      (markovChainMeasure P x) := by
  haveI := p2mfc_prob P x
  exact (integrable_const (α ^ t * C)).mono' (p2mfc_meas_term τ hτ α f t).aestronglyMeasurable
    (ae_of_all _ (p2mfc_norm_term τ hα f hf t))

open MeasureTheory ProbabilityTheory BanditAlgorithm in
/-- The expected value of the `t`-th term of the stopped discounted sum. -/
private noncomputable def p2mfc_U {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (x : S) (α : ℝ) (f : S → ℝ) (τ : (ℕ → S) → ℕ∞) (t : ℕ) : ℝ :=
  ∫ ω, (if (t : ℕ∞) < τ ω then α ^ t * f (ω t) else 0) ∂markovChainMeasure P x

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mfc_U_norm {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (x : S) (τ : (ℕ → S) → ℕ∞) {α C : ℝ} (hα : 0 ≤ α)
    (f : S → ℝ) (hf : ∀ y, |f y| ≤ C) (t : ℕ) :
    ‖p2mfc_U P x α f τ t‖ ≤ α ^ t * C := by
  haveI := p2mfc_prob P x
  unfold p2mfc_U
  have := norm_integral_le_of_norm_le_const (μ := markovChainMeasure P x)
    (ae_of_all _ (p2mfc_norm_term τ hα f hf t))
  simpa using this

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mfc_U_summable {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (x : S) (τ : (ℕ → S) → ℕ∞) {α C : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (f : S → ℝ) (hf : ∀ y, |f y| ≤ C) :
    Summable (fun t ↦ p2mfc_U P x α f τ t) := by
  refine Summable.of_norm ?_
  exact Summable.of_nonneg_of_le (fun t ↦ norm_nonneg _)
    (fun t ↦ p2mfc_U_norm P x τ hα f hf t) ((summable_geometric_of_lt_one hα hα1).mul_right C)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mfc_integral_dss {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] (x : S)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) {α C : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (f : S → ℝ) (hf : ∀ y, |f y| ≤ C) :
    ∫ ω, discountedStoppedSum α f τ ω ∂markovChainMeasure P x
      = ∑' t, p2mfc_U P x α f τ t := by
  haveI := p2mfc_prob P x
  unfold discountedStoppedSum p2mfc_U
  refine (integral_tsum_of_summable_integral_norm
    (fun t ↦ p2mfc_int_term P x τ hτ hα f hf t) ?_).symm
  refine Summable.of_nonneg_of_le (fun t ↦ integral_nonneg (fun ω ↦ norm_nonneg _))
    (fun t ↦ ?_) ((summable_geometric_of_lt_one hα hα1).mul_right C)
  calc ∫ ω, ‖(if (t : ℕ∞) < τ ω then α ^ t * f (ω t) else 0)‖ ∂markovChainMeasure P x
      ≤ ∫ _ω, α ^ t * C ∂markovChainMeasure P x :=
        integral_mono (p2mfc_int_term P x τ hτ hα f hf t).norm (integrable_const _)
          (fun ω ↦ p2mfc_norm_term τ hα f hf t ω)
    _ = α ^ t * C := by simp

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mfc_U_one_zero {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (x : S) (τ : (ℕ → S) → ℕ∞) (h1 : ∀ ω, 1 ≤ τ ω) (α : ℝ) :
    p2mfc_U P x α (fun _ ↦ 1) τ 0 = 1 := by
  haveI := p2mfc_prob P x
  unfold p2mfc_U
  have : (fun ω : ℕ → S ↦ if ((0 : ℕ) : ℕ∞) < τ ω then α ^ 0 * (fun _ : S ↦ (1 : ℝ)) (ω 0)
      else 0) = fun _ ↦ (1 : ℝ) := by
    funext ω
    have h0 : ¬ τ ω = 0 := by
      intro h; have := h1 ω; rw [h] at this; exact absurd this (by norm_num)
    simp [h0]
  rw [this]; simp

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mfc_U_one_nonneg {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (x : S) (τ : (ℕ → S) → ℕ∞) {α : ℝ} (hα : 0 ≤ α) (t : ℕ) :
    0 ≤ p2mfc_U P x α (fun _ ↦ 1) τ t := by
  unfold p2mfc_U
  refine integral_nonneg (fun ω ↦ ?_)
  dsimp only
  split_ifs
  · simpa using pow_nonneg hα t
  · exact le_rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mfc_D_ge_one {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (x : S) (τ : (ℕ → S) → ℕ∞) (h1 : ∀ ω, 1 ≤ τ ω) {α : ℝ} (hα : 0 ≤ α)
    (hα1 : α < 1) :
    1 ≤ ∑' t, p2mfc_U P x α (fun _ ↦ 1) τ t := by
  have hs := p2mfc_U_summable P x τ hα hα1 (C := 1) (fun _ ↦ (1 : ℝ)) (fun _ ↦ by simp)
  have h0 := p2mfc_U_one_zero P x τ h1 α
  have h2 := hs.le_tsum 0 (fun j _ ↦ p2mfc_U_one_nonneg P x τ hα j)
  linarith

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mfc_U_le {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] (x : S)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) {α M : ℝ} (hα : 0 ≤ α)
    (r : S → ℝ) (hM : ∀ y, |r y| ≤ M) (t : ℕ) :
    p2mfc_U P x α r τ t ≤ M * p2mfc_U P x α (fun _ ↦ 1) τ t := by
  unfold p2mfc_U
  rw [← integral_const_mul]
  refine integral_mono (p2mfc_int_term P x τ hτ hα r hM t)
    ((p2mfc_int_term P x τ hτ hα (C := 1) (fun _ ↦ (1 : ℝ)) (fun _ ↦ by simp) t).const_mul M)
    (fun ω ↦ ?_)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (ω 0))
  have hr : r (ω t) ≤ M := le_trans (le_abs_self _) (hM _)
  have hp : 0 ≤ α ^ t := pow_nonneg hα t
  dsimp only
  split_ifs
  · nlinarith
  · simp

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mfc_U_scale {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (x : S) (τ : (ℕ → S) → ℕ∞) {a b : ℝ} (ha : a ≠ 0)
    (f : S → ℝ) (t : ℕ) :
    p2mfc_U P x b f τ t = (b / a) ^ t * p2mfc_U P x a f τ t := by
  unfold p2mfc_U
  rw [← integral_const_mul]
  congr 1
  funext ω
  split_ifs
  · rw [div_pow]
    field_simp
  · simp

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mfc_U_trunc {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (x : S) (τ : (ℕ → S) → ℕ∞) (α : ℝ) (f : S → ℝ) (k : ℕ) :
    ∑' t, p2mfc_U P x α f (fun ω ↦ min (τ ω) (((k + 1 : ℕ)) : ℕ∞)) t
      = ∑ t ∈ Finset.range (k + 1), p2mfc_U P x α f τ t := by
  have hpt : ∀ t, p2mfc_U P x α f (fun ω ↦ min (τ ω) (((k + 1 : ℕ)) : ℕ∞)) t
      = if t ∈ Finset.range (k + 1) then p2mfc_U P x α f τ t else 0 := by
    intro t
    unfold p2mfc_U
    by_cases ht : t < k + 1
    · have ht' : ((t : ℕ) : ℕ∞) < ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast ht
      simp only [Finset.mem_range, ht, if_true, lt_min_iff, ht', and_true]
    · have ht' : ¬ ((t : ℕ) : ℕ∞) < ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast ht
      simp only [Finset.mem_range, ht, if_false, lt_min_iff, ht', and_false, integral_zero]
  simp_rw [hpt]
  rw [tsum_eq_sum (s := Finset.range (k + 1))]
  · exact Finset.sum_congr rfl (fun t ht ↦ by rw [if_pos ht])
  · intro t ht; rw [if_neg ht]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mfc_trunc_stop {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) (h1 : ∀ ω, 1 ≤ τ ω) (k : ℕ) :
    IsTrajStoppingTime (fun ω ↦ min (τ ω) (((k + 1 : ℕ)) : ℕ∞)) ∧
      ∀ ω, 1 ≤ min (τ ω) (((k + 1 : ℕ)) : ℕ∞) := by
  refine ⟨fun n ↦ ?_, fun ω ↦ le_min (h1 ω) (by exact_mod_cast Nat.le_add_left 1 k)⟩
  have : {ω : ℕ → S | min (τ ω) (((k + 1 : ℕ)) : ℕ∞) ≤ (n : ℕ∞)}
      = {ω | τ ω ≤ (n : ℕ∞)} ∪ {_ω | (((k + 1 : ℕ)) : ℕ∞) ≤ (n : ℕ∞)} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_union, min_le_iff]
  rw [this]
  exact (hτ n).union (MeasurableSet.const _)

/-- Summation by parts: `∑_{t≤K} q^t c_t = ∑_{k<K} (q^k - q^{k+1}) F_k + q^K F_K`. -/
private lemma p2mfc_abel (q : ℝ) (c : ℕ → ℝ) (K : ℕ) :
    ∑ t ∈ Finset.range (K + 1), q ^ t * c t
      = ∑ k ∈ Finset.range K, (q ^ k - q ^ (k + 1)) * (∑ t ∈ Finset.range (k + 1), c t)
        + q ^ K * (∑ t ∈ Finset.range (K + 1), c t) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ (fun t ↦ q ^ t * c t) (K + 1), ih,
      Finset.sum_range_succ (fun k ↦ (q ^ k - q ^ (k + 1)) * ∑ t ∈ Finset.range (k + 1), c t) K,
      Finset.sum_range_succ c (K + 1)]
    ring

open MeasureTheory ProbabilityTheory BanditAlgorithm in
theorem solution {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : AllocationIndices.BoundedReward r) {a b : ℝ} (hb0 : 0 < b) (hba : b ≤ a) (ha1 : a < 1)
    (x : S) :
    gittinsIndex P r b x ≤ gittinsIndex P r a x := by
  classical
  obtain ⟨M, hM⟩ := hr
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM x)
  have h1f : ∀ y : S, |(fun _ : S ↦ (1 : ℝ)) y| ≤ 1 := fun _ ↦ by simp
  have ha0 : 0 < a := lt_of_lt_of_le hb0 hba
  have hb1 : b < 1 := lt_of_le_of_lt hba ha1
  rcases hba.lt_or_eq with hlt | heq
  swap
  · subst heq; exact le_rfl
  unfold gittinsIndex
  set A : Set ℝ := {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
    g = (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P x) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x)} with hA
  have hbdd : BddAbove A := by
    refine ⟨M, ?_⟩
    rintro g ⟨τ, hτ, h1, rfl⟩
    rw [p2mfc_integral_dss P x τ hτ ha0.le ha1 r hM,
      p2mfc_integral_dss P x τ hτ ha0.le ha1 _ h1f]
    have hD := p2mfc_D_ge_one P x τ h1 ha0.le ha1
    have hN : ∑' t, p2mfc_U P x a r τ t ≤ M * ∑' t, p2mfc_U P x a (fun _ ↦ 1) τ t := by
      rw [← tsum_mul_left]
      exact Summable.tsum_le_tsum (fun t ↦ p2mfc_U_le P x τ hτ ha0.le r hM t)
        (p2mfc_U_summable P x τ ha0.le ha1 r hM)
        ((p2mfc_U_summable P x τ ha0.le ha1 _ h1f).mul_left M)
    rw [div_le_iff₀ (by linarith)]; linarith
  have hstop1 : IsTrajStoppingTime (fun _ : ℕ → S ↦ (1 : ℕ∞)) := fun n ↦ MeasurableSet.const _
  apply csSup_le
  · exact ⟨_, fun _ ↦ 1, hstop1, fun _ ↦ le_rfl, rfl⟩
  rintro g ⟨τ, hτ, h1, hg⟩
  rw [p2mfc_integral_dss P x τ hτ hb0.le hb1 r hM,
    p2mfc_integral_dss P x τ hτ hb0.le hb1 _ h1f] at hg
  by_contra hcon
  push Not at hcon
  set q : ℝ := b / a with hq
  have hq0 : 0 < q := div_pos hb0 ha0
  have hq1 : q < 1 := (div_lt_one ha0).2 hlt
  set c : ℕ → ℝ := fun t ↦ p2mfc_U P x a r τ t - g * p2mfc_U P x a (fun _ ↦ 1) τ t with hc
  -- every truncation has a-ratio below g
  have hF : ∀ k, ∑ t ∈ Finset.range (k + 1), c t < 0 := by
    intro k
    obtain ⟨hτk, h1k⟩ := p2mfc_trunc_stop τ hτ h1 k
    have hmem := le_csSup hbdd ⟨_, hτk, h1k, rfl⟩
    rw [p2mfc_integral_dss P x _ hτk ha0.le ha1 r hM,
      p2mfc_integral_dss P x _ hτk ha0.le ha1 _ h1f] at hmem
    have hD := p2mfc_D_ge_one P x _ h1k ha0.le ha1
    simp only [p2mfc_U_trunc] at hmem hD
    have hlt2 := lt_of_le_of_lt hmem hcon
    rw [div_lt_iff₀ (by linarith)] at hlt2
    have hce : ∑ t ∈ Finset.range (k + 1), c t = ∑ t ∈ Finset.range (k + 1), p2mfc_U P x a r τ t
        - g * ∑ t ∈ Finset.range (k + 1), p2mfc_U P x a (fun _ ↦ 1) τ t := by
      rw [hc]; simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hce]
    linarith
  -- the b-profit of τ at charge g vanishes
  have hsr := p2mfc_U_summable P x τ hb0.le hb1 r hM
  have hs1 := p2mfc_U_summable P x τ hb0.le hb1 _ h1f
  have hDb := p2mfc_D_ge_one P x τ h1 hb0.le hb1
  have hzero : ∑' t, (p2mfc_U P x b r τ t - g * p2mfc_U P x b (fun _ ↦ 1) τ t) = 0 := by
    rw [hsr.tsum_sub (hs1.mul_left g), tsum_mul_left, hg, div_mul_cancel₀]
    · ring
    · linarith
  have he : ∀ t, p2mfc_U P x b r τ t - g * p2mfc_U P x b (fun _ ↦ 1) τ t = q ^ t * c t := by
    intro t
    show _ = (b / a) ^ t * c t
    rw [p2mfc_U_scale P x τ (a := a) (b := b) ha0.ne' r t,
      p2mfc_U_scale P x τ (a := a) (b := b) ha0.ne' (fun _ ↦ 1) t, hc]
    ring
  have hsum : Summable (fun t ↦ q ^ t * c t) := by
    have := hsr.sub (hs1.mul_left g)
    simpa only [he] using this
  simp_rw [he] at hzero
  -- partial sums are bounded by (1 - q) F_0 < 0
  have hF0 := hF 0
  have hpart : ∀ K, ∑ t ∈ Finset.range (K + 1), q ^ t * c t
      ≤ (1 - q) * ∑ t ∈ Finset.range (0 + 1), c t := by
    intro K
    rw [p2mfc_abel]
    have hlast : q ^ K * (∑ t ∈ Finset.range (K + 1), c t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hq0.le K) (hF K).le
    cases K with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, one_mul]
      simp only [zero_add] at hF0
      nlinarith
    | succ K =>
      rw [Finset.sum_range_succ']
      have hrest : ∑ k ∈ Finset.range K, (q ^ (k + 1) - q ^ (k + 1 + 1)) *
          (∑ t ∈ Finset.range (k + 1 + 1), c t) ≤ 0 := by
        refine Finset.sum_nonpos (fun k _ ↦ mul_nonpos_of_nonneg_of_nonpos ?_ (hF (k + 1)).le)
        have : q ^ (k + 1 + 1) ≤ q ^ (k + 1) :=
          pow_le_pow_of_le_one hq0.le hq1.le (Nat.le_succ _)
        linarith
      simp only [pow_zero, zero_add, pow_one] at hrest ⊢
      linarith
  have hlim : ∑' t, q ^ t * c t ≤ (1 - q) * ∑ t ∈ Finset.range (0 + 1), c t := by
    refine le_of_tendsto hsum.hasSum.tendsto_sum_nat ?_
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn ↦ ?_⟩
    obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact hpart K
  have : (1 - q) * ∑ t ∈ Finset.range (0 + 1), c t < 0 :=
    mul_neg_of_pos_of_neg (by linarith) hF0
  linarith
