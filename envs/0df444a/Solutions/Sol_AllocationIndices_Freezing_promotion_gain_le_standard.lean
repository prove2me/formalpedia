-- Prove2me | solution 1 for AllocationIndices.Freezing.promotion_gain_le_standard
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:33:04.561037+00:00
-- url     : https://prove2.me/submissions/77b1b86d-1ace-4b4f-91b5-7368fe43a31d

import Definitions.Def_AllocationIndices_Freezing_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm
open AllocationIndices AllocationIndices.Freezing

section G70ALF
variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

lemma g70al_filt_le (t : ℕ) :
    trajectoryFiltration S t ≤ (inferInstance : MeasurableSpace (ℕ → S)) :=
  Measurable.comap_le (measurable_pi_lambda _ fun i => measurable_pi_apply _)

lemma g70al_term_meas (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (a : ℝ) (g : S → ℝ) (t : ℕ) :
    Measurable (fun ω : ℕ → S => if (t : ℕ∞) < τ ω then a ^ t * g (ω t) else 0) := by
  have hs : MeasurableSet {ω : ℕ → S | (t : ℕ∞) < τ ω} := by
    have : {ω : ℕ → S | (t : ℕ∞) < τ ω} = {ω | τ ω ≤ (t : ℕ∞)}ᶜ := by ext ω; simp
    rw [this]; exact (g70al_filt_le t _ (hτ t)).compl
  refine Measurable.ite hs ?_ measurable_const
  exact measurable_const.mul ((measurable_of_countable g).comp (measurable_pi_apply t))

lemma g70al_term_bd (τ : (ℕ → S) → ℕ∞) {a : ℝ} (ha0 : 0 < a) (g : S → ℝ) {K : ℝ}
    (hK : ∀ s, |g s| ≤ K) (ω : ℕ → S) (t : ℕ) :
    ‖(if (t : ℕ∞) < τ ω then a ^ t * g (ω t) else 0)‖ ≤ K * a ^ t := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK (ω 0))
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos ha0 t), mul_comm]
    exact mul_le_mul_of_nonneg_right (hK _) (pow_pos ha0 t).le
  · simp; positivity

lemma g70al_summ (τ : (ℕ → S) → ℕ∞) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (g : S → ℝ) {K : ℝ}
    (hK : ∀ s, |g s| ≤ K) (ω : ℕ → S) :
    Summable (fun t : ℕ => if (t : ℕ∞) < τ ω then a ^ t * g (ω t) else 0) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0.le ha1).mul_left K)
    (g70al_term_bd τ ha0 g hK ω)

lemma g70al_dss_meas (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1) (g : S → ℝ) {K : ℝ} (hK : ∀ s, |g s| ≤ K) :
    Measurable (discountedStoppedSum a g τ) := by
  refine measurable_of_tendsto_metrizable (f := fun n ω => ∑ t ∈ Finset.range n,
      (if (t : ℕ∞) < τ ω then a ^ t * g (ω t) else 0))
    (fun n => Finset.measurable_sum _ fun t _ => g70al_term_meas τ hτ a g t) ?_
  exact tendsto_pi_nhds.2 fun ω => (g70al_summ τ ha0 ha1 g hK ω).hasSum.tendsto_sum_nat

lemma g70al_dss_bd (τ : (ℕ → S) → ℕ∞) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (g : S → ℝ) {K : ℝ}
    (hK : ∀ s, |g s| ≤ K) (ω : ℕ → S) :
    ‖discountedStoppedSum a g τ ω‖ ≤ K * (1 - a)⁻¹ := by
  unfold discountedStoppedSum
  rw [← tsum_geometric_of_lt_one ha0.le ha1, ← tsum_mul_left]
  exact tsum_of_norm_bounded ((summable_geometric_of_lt_one ha0.le ha1).mul_left K).hasSum
    (g70al_term_bd τ ha0 g hK ω)

lemma g70al_dss_int (P : Kernel S S) [IsMarkovKernel P] (x : S) (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1) (g : S → ℝ) {K : ℝ} (hK : ∀ s, |g s| ≤ K) :
    Integrable (discountedStoppedSum a g τ) (markovChainMeasure P x) := by
  haveI : IsProbabilityMeasure (markovChainMeasure P x) := by
    unfold markovChainMeasure; infer_instance
  exact Integrable.of_bound (C := K * (1 - a)⁻¹) (g70al_dss_meas τ hτ ha0 ha1 g hK).aestronglyMeasurable
    (Filter.Eventually.of_forall (g70al_dss_bd τ ha0 ha1 g hK))

lemma g70al_dss_ge_one (τ : (ℕ → S) → ℕ∞) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ω : ℕ → S)
    (h1 : 1 ≤ τ ω) : 1 ≤ discountedStoppedSum a (fun _ => (1:ℝ)) τ ω := by
  unfold discountedStoppedSum
  have hK : ∀ s : S, |(fun _ => (1:ℝ)) s| ≤ 1 := by simp
  have hnn : ∀ t : ℕ, 0 ≤ (if (t : ℕ∞) < τ ω then a ^ t * (fun _ => (1:ℝ)) (ω t) else 0) := by
    intro t; split_ifs <;> simp [pow_nonneg ha0.le]
  have := (g70al_summ τ ha0 ha1 _ hK ω).le_tsum 0 (fun t _ => hnn t)
  have h0 : ((0 : ℕ) : ℕ∞) < τ ω := lt_of_lt_of_le (by norm_num) h1
  simp only [h0, if_true, pow_zero, mul_one] at this
  simpa using this

lemma g70al_dss_sub (τ : (ℕ → S) → ℕ∞) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (g : S → ℝ) {K : ℝ}
    (hK : ∀ s, |g s| ≤ K) (ν : ℝ) (ω : ℕ → S) :
    discountedStoppedSum a (fun s => g s - ν) τ ω =
      discountedStoppedSum a g τ ω - ν * discountedStoppedSum a (fun _ => (1:ℝ)) τ ω := by
  have hK1 : ∀ s : S, |(fun _ => (1:ℝ)) s| ≤ 1 := by simp
  unfold discountedStoppedSum
  rw [← tsum_mul_left, ← Summable.tsum_sub (g70al_summ τ ha0 ha1 g hK ω)
    ((g70al_summ τ ha0 ha1 _ hK1 ω).mul_left ν)]
  congr 1; ext t; split_ifs <;> ring

/-- (F1) every positive stopping time has `R - ν W ≤ 0`. -/
lemma g70al_F1 (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : BoundedReward r) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (x : S) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ)
    (h1 : ∀ ω, 1 ≤ τ ω) :
    ∫ ω, discountedStoppedSum a (fun s => r s - gittinsIndex P r a x) τ ω ∂markovChainMeasure P x
      ≤ 0 := by
  haveI : IsProbabilityMeasure (markovChainMeasure P x) := by
    unfold markovChainMeasure; infer_instance
  obtain ⟨K, hK⟩ := hr
  have hK1 : ∀ s : S, |(fun _ => (1:ℝ)) s| ≤ 1 := by simp
  set ν := gittinsIndex P r a x
  simp_rw [g70al_dss_sub τ ha0 ha1 r hK ν]
  rw [integral_sub (g70al_dss_int P x τ hτ ha0 ha1 r hK)
    ((g70al_dss_int P x τ hτ ha0 ha1 _ hK1).const_mul ν), integral_const_mul]
  set R := ∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P x
  set W := ∫ ω, discountedStoppedSum a (fun _ => (1:ℝ)) τ ω ∂markovChainMeasure P x
  have hW : 1 ≤ W := by
    calc (1:ℝ) = ∫ _ω, (1:ℝ) ∂markovChainMeasure P x := by simp
      _ ≤ W := integral_mono (integrable_const 1) (g70al_dss_int P x τ hτ ha0 ha1 _ hK1)
          (fun ω => g70al_dss_ge_one τ ha0 ha1 ω (h1 ω))
  -- every ratio is ≤ K
  have hbdd : BddAbove {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      g = (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P x) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x)} := by
    refine ⟨K, ?_⟩
    rintro _ ⟨σ, hσ, hσ1, rfl⟩
    have hW' : 1 ≤ ∫ ω, discountedStoppedSum a (fun _ => (1:ℝ)) σ ω ∂markovChainMeasure P x := by
      calc (1:ℝ) = ∫ _ω, (1:ℝ) ∂markovChainMeasure P x := by simp
        _ ≤ _ := integral_mono (integrable_const 1) (g70al_dss_int P x σ hσ ha0 ha1 _ hK1)
            (fun ω => g70al_dss_ge_one σ ha0 ha1 ω (hσ1 ω))
    rw [div_le_iff₀ (by linarith)]
    have hpt : ∀ ω, discountedStoppedSum a r σ ω ≤ K * discountedStoppedSum a (fun _ => (1:ℝ)) σ ω := by
      intro ω
      have hsub := g70al_dss_sub σ ha0 ha1 r hK K ω
      have hle : discountedStoppedSum a (fun s => r s - K) σ ω ≤ 0 := by
        unfold discountedStoppedSum
        refine tsum_nonpos fun t => ?_
        split_ifs
        · exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ha0.le _)
            (by have := (abs_le.1 (hK (ω t))).2; linarith)
        · exact le_rfl
      linarith
    calc _ ≤ ∫ ω, K * discountedStoppedSum a (fun _ => (1:ℝ)) σ ω ∂markovChainMeasure P x :=
          integral_mono (g70al_dss_int P x σ hσ ha0 ha1 r hK)
            ((g70al_dss_int P x σ hσ ha0 ha1 _ hK1).const_mul K) hpt
      _ = _ := by rw [integral_const_mul]
  have hmem : R / W ≤ ν := le_csSup hbdd ⟨τ, hτ, h1, rfl⟩
  rw [div_le_iff₀ (by linarith)] at hmem
  linarith


lemma g70al_ae_zero (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    ∀ᵐ ω ∂markovChainMeasure P x, ω 0 = x := by
  unfold markovChainMeasure Kernel.trajMeasure
  have hm : MeasurableSet {ω : ℕ → S | ω 0 = x} :=
    measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
  apply Measure.ae_comp_of_ae_ae hm
  rw [ae_map_iff (MeasurableEquiv.measurable _).aemeasurable MeasurableSet.of_discrete,
    ae_dirac_iff MeasurableSet.of_discrete]
  set x0 := (MeasurableEquiv.piUnique fun i : Finset.Iic 0 => (fun _ : ℕ => S) ↑i).symm x
  have h1 := Kernel.traj_map_frestrictLe_apply (X := fun _ : ℕ => S) (κ := markovChainStep P) 0 0 x0
  rw [Kernel.partialTraj_self, Kernel.id_apply] at h1
  have h2 : ∀ᵐ z ∂(Kernel.traj (markovChainStep P) 0 x0).map
      (Preorder.frestrictLe (π := fun _ : ℕ => S) 0),
      z ⟨0, Finset.mem_Iic.2 le_rfl⟩ = x := by
    rw [h1, ae_dirac_iff MeasurableSet.of_discrete]; rfl
  exact ae_of_ae_map (by fun_prop) h2


lemma g70al_fmono (f : FreezingRule S) (ω : ℕ → S) {i j : ℕ} (h : i ≤ j) :
    f.freeze i ω ≤ f.freeze j ω :=
  monotone_nat_of_le_succ (fun i => f.mono i ω) h

lemma g70al_dep0 (f : FreezingRule S) (n : ℕ) (ω ω' : ℕ → S) (h : ω 0 = ω' 0) :
    f.freeze 0 ω ≤ (n : ℕ∞) ↔ f.freeze 0 ω' ≤ (n : ℕ∞) := by
  obtain ⟨s', _, he⟩ := f.adapted 0 n
  have hg : (fun i : Finset.Iic 0 => ω i.1) = (fun i : Finset.Iic 0 => ω' i.1) := by
    funext i
    have : i.1 = 0 := Nat.le_zero.1 (Finset.mem_Iic.1 i.2)
    rw [this, h]
  change ω ∈ {ω | f.freeze 0 ω ≤ (n : ℕ∞)} ↔ ω' ∈ {ω | f.freeze 0 ω ≤ (n : ℕ∞)}
  rw [← he]
  simp only [Set.mem_preimage]
  rw [hg]

noncomputable def g70al_sig (f : FreezingRule S) (n : ℕ) (ω : ℕ → S) : ℕ∞ :=
  ⨅ i : {i : ℕ // 1 ≤ i ∧ ¬ f.freeze i ω ≤ (n : ℕ∞)}, ((i : ℕ) : ℕ∞)

lemma g70al_sig_le (f : FreezingRule S) (n : ℕ) (ω : ℕ → S) (m : ℕ) :
    g70al_sig f n ω ≤ (m : ℕ∞) ↔ 1 ≤ m ∧ ¬ f.freeze m ω ≤ (n : ℕ∞) := by
  constructor
  · intro hle
    by_contra hc
    have hc' : 1 ≤ m → f.freeze m ω ≤ (n : ℕ∞) := fun h1 => by
      by_contra h2; exact hc ⟨h1, h2⟩
    have : ((m + 1 : ℕ) : ℕ∞) ≤ g70al_sig f n ω := by
      unfold g70al_sig
      refine le_iInf fun i => ?_
      rw [Nat.cast_le]
      by_contra hlt
      push Not at hlt
      have him : i.1 ≤ m := by omega
      exact i.2.2 ((g70al_fmono f ω him).trans (hc' (le_trans i.2.1 him)))
    have := this.trans hle
    rw [Nat.cast_le] at this; omega
  · intro h
    exact iInf_le_of_le ⟨m, h⟩ le_rfl

lemma g70al_sig_ge (f : FreezingRule S) (n : ℕ) (ω : ℕ → S) : 1 ≤ g70al_sig f n ω := by
  unfold g70al_sig
  refine le_iInf fun i => ?_
  exact_mod_cast i.2.1

lemma g70al_sig_lt (f : FreezingRule S) (n : ℕ) (ω : ℕ → S) (h0 : f.freeze 0 ω ≤ (n : ℕ∞))
    (t : ℕ) : (t : ℕ∞) < g70al_sig f n ω ↔ f.freeze t ω ≤ (n : ℕ∞) := by
  rw [← not_le, g70al_sig_le]
  by_cases ht : t = 0
  · subst ht; simp [h0]
  · constructor
    · intro h; by_contra h2; exact h ⟨by omega, h2⟩
    · intro h h2; exact h2.2 h

lemma g70al_sig_stop (f : FreezingRule S) (n : ℕ) : IsTrajStoppingTime (g70al_sig f n) := by
  intro m
  have : {ω | g70al_sig f n ω ≤ (m : ℕ∞)} = {ω | 1 ≤ m ∧ ¬ f.freeze m ω ≤ (n : ℕ∞)} := by
    ext ω; exact g70al_sig_le f n ω m
  rw [this]
  by_cases hm : 1 ≤ m
  · simp only [hm, true_and]
    exact (f.adapted m n).compl
  · simp [hm]

/-- Core lemma: the level-`n` truncation has nonpositive expected `r - ν` reward. -/
lemma g70al_L (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : BoundedReward r) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (f : FreezingRule S) (x : S) (n : ℕ) :
    ∫ ω, ∑' i : ℕ, (if f.freeze i ω ≤ (n : ℕ∞) then a ^ i * (r (ω i) - gittinsIndex P r a x)
      else 0) ∂markovChainMeasure P x ≤ 0 := by
  by_cases hc : ∃ ω0 : ℕ → S, ω0 0 = x ∧ f.freeze 0 ω0 ≤ (n : ℕ∞)
  · obtain ⟨ω0, h0x, h0n⟩ := hc
    have hae : ∀ᵐ ω ∂markovChainMeasure P x,
        (∑' i : ℕ, (if f.freeze i ω ≤ (n : ℕ∞) then a ^ i * (r (ω i) - gittinsIndex P r a x)
          else 0)) = discountedStoppedSum a (fun s => r s - gittinsIndex P r a x)
            (g70al_sig f n) ω := by
      filter_upwards [g70al_ae_zero P x] with ω hω
      have h0 : f.freeze 0 ω ≤ (n : ℕ∞) := (g70al_dep0 f n ω ω0 (hω.trans h0x.symm)).2 h0n
      unfold discountedStoppedSum
      congr 1; ext t
      simp only [g70al_sig_lt f n ω h0 t]
    rw [integral_congr_ae hae]
    exact g70al_F1 P hr ha0 ha1 x _ (g70al_sig_stop f n) (g70al_sig_ge f n)
  · push Not at hc
    have hae : ∀ᵐ ω ∂markovChainMeasure P x,
        (∑' i : ℕ, (if f.freeze i ω ≤ (n : ℕ∞) then a ^ i * (r (ω i) - gittinsIndex P r a x)
          else 0)) = 0 := by
      filter_upwards [g70al_ae_zero P x] with ω hω
      have h0 := hc ω hω
      refine (tsum_congr fun i => ?_).trans tsum_zero
      rw [if_neg]
      intro hi
      exact absurd (lt_of_lt_of_le h0 ((g70al_fmono f ω (Nat.zero_le i)).trans hi)) (lt_irrefl _)
    rw [integral_congr_ae hae, integral_zero]


lemma g70al_freeze_meas (f : FreezingRule S) (i : ℕ) : Measurable (f.freeze i) := by
  have hle : ∀ k : ℕ, MeasurableSet {ω | f.freeze i ω ≤ (k : ℕ∞)} :=
    fun k => g70al_filt_le i _ (f.adapted i k)
  refine measurable_to_countable' fun m => ?_
  induction m using ENat.recTopCoe with
  | top =>
    have : f.freeze i ⁻¹' {⊤} = ⋂ k : ℕ, {ω | f.freeze i ω ≤ (k : ℕ∞)}ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff,
        Set.mem_setOf_eq]
      induction f.freeze i ω using ENat.recTopCoe with
      | top => simp
      | coe l => simp only [ENat.coe_ne_top, false_iff, not_forall, not_not]; exact ⟨l, le_rfl⟩
    rw [this]; exact MeasurableSet.iInter fun k => (hle k).compl
  | coe k =>
    have : f.freeze i ⁻¹' {(k : ℕ∞)} = {ω | f.freeze i ω ≤ (k : ℕ∞)} ∩
        ⋂ j ∈ Finset.range k, {ω | f.freeze i ω ≤ (j : ℕ∞)}ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Set.mem_setOf_eq, Finset.mem_range]
      induction f.freeze i ω using ENat.recTopCoe with
      | top => simp
      | coe l =>
        simp only [Nat.cast_inj, Nat.cast_le]
        constructor
        · rintro rfl; exact ⟨le_rfl, fun j hj => by omega⟩
        · rintro ⟨h1, h2⟩; by_contra hne; exact h2 l (by omega) le_rfl
    rw [this]
    exact (hle k).inter (Finset.measurableSet_biInter _ fun j _ => (hle j).compl)

lemma g70al_dp_coe (a : ℝ) (k : ℕ) : discountPow a (k : ℕ∞) = a ^ k := rfl

lemma g70al_dp_top (a : ℝ) : discountPow a ⊤ = 0 := rfl

lemma g70al_dp_add (a : ℝ) (i : ℕ) (m : ℕ∞) :
    discountPow a ((i : ℕ∞) + m) = a ^ i * discountPow a m := by
  induction m using ENat.recTopCoe with
  | top => simp [g70al_dp_top]
  | coe k => rw [← Nat.cast_add, g70al_dp_coe, g70al_dp_coe, pow_add]

lemma g70al_dp_bd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ∞) :
    0 ≤ discountPow a m ∧ discountPow a m ≤ 1 := by
  induction m using ENat.recTopCoe with
  | top => simp [g70al_dp_top]
  | coe k => rw [g70al_dp_coe]; exact ⟨pow_nonneg ha0.le _, pow_le_one₀ ha0.le ha1.le⟩

lemma g70al_dp_fin (a : ℝ) (m : ℕ∞) (τ : ℕ) (h : m ≤ (τ : ℕ∞)) :
    ∑ n ∈ Finset.range τ, (if m ≤ (n : ℕ∞) then a ^ n - a ^ (n + 1) else 0) =
      discountPow a m - a ^ τ := by
  induction τ with
  | zero =>
    have : m = 0 := by simpa using h
    subst this
    rw [show (0:ℕ∞) = ((0:ℕ):ℕ∞) from rfl, g70al_dp_coe]; simp
  | succ τ ih =>
    rw [Finset.sum_range_succ]
    by_cases hm : m ≤ (τ : ℕ∞)
    · rw [ih hm, if_pos hm]; ring
    · have hm' : m = ((τ + 1 : ℕ) : ℕ∞) := by
        induction m using ENat.recTopCoe with
        | top => simp at h
        | coe l =>
          simp only [Nat.cast_le, Nat.cast_inj] at hm h ⊢; omega
      rw [if_neg hm, add_zero, hm', g70al_dp_coe]
      have : ∀ n ∈ Finset.range τ, (if ((τ + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) then a ^ n - a ^ (n + 1)
          else 0) = 0 := by
        intro n hn
        rw [if_neg]; simp only [Nat.cast_le]; simp at hn; omega
      rw [Finset.sum_eq_zero this]; ring

lemma g70al_dp_hasSum {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (m : ℕ∞) :
    HasSum (fun n : ℕ => if m ≤ (n : ℕ∞) then a ^ n - a ^ (n + 1) else 0) (discountPow a m) := by
  have hnn : ∀ n : ℕ, 0 ≤ (if m ≤ (n : ℕ∞) then a ^ n - a ^ (n + 1) else 0) := by
    intro n; split_ifs
    · have : a ^ (n + 1) ≤ a ^ n := pow_le_pow_of_le_one ha0.le ha1.le (by omega)
      linarith
    · exact le_rfl
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  induction m using ENat.recTopCoe with
  | top => simp [g70al_dp_top]
  | coe k =>
    have hev : (fun N => discountPow a (k : ℕ∞) - a ^ N) =ᶠ[Filter.atTop]
        (fun N => ∑ n ∈ Finset.range N, (if (k : ℕ∞) ≤ (n : ℕ∞) then a ^ n - a ^ (n + 1) else 0)) := by
      filter_upwards [Filter.eventually_ge_atTop k] with N hN
      rw [g70al_dp_fin a k N (by exact_mod_cast hN)]
    refine Filter.Tendsto.congr' hev ?_
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).const_sub (discountPow a (k : ℕ∞))
    simpa using this


noncomputable def g70al_G (f : FreezingRule S) (a : ℝ) (c : S → ℝ) (n : ℕ) (ω : ℕ → S) : ℝ :=
  ∑' i : ℕ, if f.freeze i ω ≤ (n : ℕ∞) then a ^ i * c (ω i) else 0

lemma g70al_G_term_bd (f : FreezingRule S) {a : ℝ} (ha0 : 0 < a) (c : S → ℝ) {K : ℝ}
    (hK : ∀ s, |c s| ≤ K) (n : ℕ) (ω : ℕ → S) (i : ℕ) :
    ‖(if f.freeze i ω ≤ (n : ℕ∞) then a ^ i * c (ω i) else 0)‖ ≤ K * a ^ i := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK (ω 0))
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos ha0 i), mul_comm]
    exact mul_le_mul_of_nonneg_right (hK _) (pow_pos ha0 i).le
  · simp; positivity

lemma g70al_G_summ (f : FreezingRule S) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (c : S → ℝ) {K : ℝ}
    (hK : ∀ s, |c s| ≤ K) (n : ℕ) (ω : ℕ → S) :
    Summable (fun i : ℕ => if f.freeze i ω ≤ (n : ℕ∞) then a ^ i * c (ω i) else 0) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0.le ha1).mul_left K)
    (g70al_G_term_bd f ha0 c hK n ω)

lemma g70al_G_meas (f : FreezingRule S) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (c : S → ℝ) {K : ℝ}
    (hK : ∀ s, |c s| ≤ K) (n : ℕ) : Measurable (g70al_G f a c n) := by
  refine measurable_of_tendsto_metrizable (f := fun N ω => ∑ i ∈ Finset.range N,
      (if f.freeze i ω ≤ (n : ℕ∞) then a ^ i * c (ω i) else 0))
    (fun N => Finset.measurable_sum _ fun i _ => ?_) ?_
  · exact Measurable.ite (g70al_filt_le i _ (f.adapted i n))
      (measurable_const.mul ((measurable_of_countable c).comp (measurable_pi_apply i)))
      measurable_const
  · exact tendsto_pi_nhds.2 fun ω => (g70al_G_summ f ha0 ha1 c hK n ω).hasSum.tendsto_sum_nat

lemma g70al_G_bd (f : FreezingRule S) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (c : S → ℝ) {K : ℝ}
    (hK : ∀ s, |c s| ≤ K) (n : ℕ) (ω : ℕ → S) : ‖g70al_G f a c n ω‖ ≤ K * (1 - a)⁻¹ := by
  unfold g70al_G
  rw [← tsum_geometric_of_lt_one ha0.le ha1, ← tsum_mul_left]
  exact tsum_of_norm_bounded ((summable_geometric_of_lt_one ha0.le ha1).mul_left K).hasSum
    (g70al_G_term_bd f ha0 c hK n ω)

lemma g70al_G_int (P : Kernel S S) [IsMarkovKernel P] (x : S) (f : FreezingRule S) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (c : S → ℝ) {K : ℝ} (hK : ∀ s, |c s| ≤ K) (n : ℕ) :
    Integrable (g70al_G f a c n) (markovChainMeasure P x) := by
  haveI : IsProbabilityMeasure (markovChainMeasure P x) := by
    unfold markovChainMeasure; infer_instance
  exact Integrable.of_bound (C := K * (1 - a)⁻¹) (g70al_G_meas f ha0 ha1 c hK n).aestronglyMeasurable
    (Filter.Eventually.of_forall (g70al_G_bd f ha0 ha1 c hK n))

lemma g70al_FR_term_bd (f : FreezingRule S) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (c : S → ℝ)
    {K : ℝ} (hK : ∀ s, |c s| ≤ K) (ω : ℕ → S) (i : ℕ) :
    ‖discountPow a ((i : ℕ∞) + f.freeze i ω) * c (ω i)‖ ≤ K * a ^ i := by
  rw [g70al_dp_add, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (pow_pos ha0 i)]
  have h1 := g70al_dp_bd ha0 ha1 (f.freeze i ω)
  rw [abs_of_nonneg h1.1]
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK (ω 0))
  calc a ^ i * discountPow a (f.freeze i ω) * |c (ω i)| ≤ a ^ i * 1 * K := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1.2 (pow_pos ha0 i).le) (hK _)
          (abs_nonneg _) (by positivity)
    _ = K * a ^ i := by ring

lemma g70al_FR_summ (f : FreezingRule S) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (c : S → ℝ)
    {K : ℝ} (hK : ∀ s, |c s| ≤ K) (ω : ℕ → S) :
    Summable (fun i : ℕ => discountPow a ((i : ℕ∞) + f.freeze i ω) * c (ω i)) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0.le ha1).mul_left K)
    (g70al_FR_term_bd f ha0 ha1 c hK ω)

lemma g70al_FR_int (P : Kernel S S) [IsMarkovKernel P] (x : S) (f : FreezingRule S) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (c : S → ℝ) {K : ℝ} (hK : ∀ s, |c s| ≤ K) :
    Integrable (fun ω => ∑' i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω) * c (ω i))
      (markovChainMeasure P x) := by
  haveI : IsProbabilityMeasure (markovChainMeasure P x) := by
    unfold markovChainMeasure; infer_instance
  have hmeas : Measurable (fun ω => ∑' i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω) * c (ω i)) := by
    refine measurable_of_tendsto_metrizable (f := fun N ω => ∑ i ∈ Finset.range N,
        discountPow a ((i : ℕ∞) + f.freeze i ω) * c (ω i))
      (fun N => Finset.measurable_sum _ fun i _ => ?_) ?_
    · simp_rw [g70al_dp_add]
      exact (measurable_const.mul ((measurable_of_countable (discountPow a)).comp
        (g70al_freeze_meas f i))).mul ((measurable_of_countable c).comp (measurable_pi_apply i))
    · exact tendsto_pi_nhds.2 fun ω => (g70al_FR_summ f ha0 ha1 c hK ω).hasSum.tendsto_sum_nat
  refine Integrable.of_bound (C := K * (1 - a)⁻¹) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [← tsum_geometric_of_lt_one ha0.le ha1, ← tsum_mul_left]
  exact tsum_of_norm_bounded ((summable_geometric_of_lt_one ha0.le ha1).mul_left K).hasSum
    (g70al_FR_term_bd f ha0 ha1 c hK ω)

lemma g70al_decomp (f : FreezingRule S) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (c : S → ℝ) {K : ℝ}
    (hK : ∀ s, |c s| ≤ K) (ω : ℕ → S) :
    ∑' i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω) * c (ω i) =
      ∑' n : ℕ, (a ^ n - a ^ (n + 1)) * g70al_G f a c n ω := by
  set F : ℕ → ℕ → ℝ := fun i n =>
    if f.freeze i ω ≤ (n : ℕ∞) then (a ^ n - a ^ (n + 1)) * (a ^ i * c (ω i)) else 0 with hF
  have h1 : ∀ i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω) * c (ω i) = ∑' n, F i n := by
    intro i
    rw [g70al_dp_add, ← (g70al_dp_hasSum ha0 ha1 (f.freeze i ω)).tsum_eq,
      show ∀ A B : ℝ, A * B * c (ω i) = B * (A * c (ω i)) from fun A B => by ring,
      ← tsum_mul_right]
    congr 1; ext n; simp only [hF]; split_ifs <;> simp
  have h2 : ∀ n, (a ^ n - a ^ (n + 1)) * g70al_G f a c n ω = ∑' i, F i n := by
    intro n
    unfold g70al_G
    rw [← tsum_mul_left]
    congr 1; ext i; simp only [hF]; split_ifs <;> simp
  rw [tsum_congr h1, tsum_congr h2]
  have hw : ∀ n : ℕ, a ^ n - a ^ (n + 1) = (1 - a) * a ^ n := fun n => by ring
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK (ω 0))
  have hsum : Summable (Function.uncurry F) := by
    have hprod := Summable.mul_of_nonneg ((summable_geometric_of_lt_one ha0.le ha1).mul_left K)
      ((summable_geometric_of_lt_one ha0.le ha1).mul_left (1 - a))
      (fun i => by simp only [Pi.zero_apply]; positivity)
      (fun n => by simp only [Pi.zero_apply]; have : 0 ≤ 1 - a := by linarith
                   positivity)
    refine Summable.of_norm_bounded hprod fun p => ?_
    simp only [Function.uncurry, hF]
    split_ifs
    · have hw0 : 0 ≤ a ^ p.2 - a ^ (p.2 + 1) := by
        have : a ^ (p.2 + 1) ≤ a ^ p.2 := pow_le_pow_of_le_one ha0.le ha1.le (by omega)
        linarith
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_pos (pow_pos ha0 p.1), hw]
      have := hK (ω p.1)
      have h3 : 0 ≤ (1 - a) * a ^ p.2 := by
        have : 0 ≤ 1 - a := by linarith
        positivity
      calc (1 - a) * a ^ p.2 * (a ^ p.1 * |c (ω p.1)|) ≤ (1 - a) * a ^ p.2 * (a ^ p.1 * K) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this (pow_pos ha0 _).le) h3
        _ = K * a ^ p.1 * ((1 - a) * a ^ p.2) := by ring
    · simp only [norm_zero]
      have : 0 ≤ 1 - a := by linarith
      positivity
  exact (hsum.tsum_comm).symm

theorem g70al_T1 (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (f : FreezingRule S) (x : S) :
    freezingReward P r a f x ≤ freezingTime P a f x * gittinsIndex P r a x := by
  obtain ⟨K, hK⟩ := hr
  set ν := gittinsIndex P r a x
  set c : S → ℝ := fun s => r s - ν with hc
  have hKc : ∀ s, |c s| ≤ K + |ν| := fun s => by
    simp only [hc]; exact (abs_sub _ _).trans (by linarith [hK s])
  have hK1 : ∀ s : S, |(fun _ => (1:ℝ)) s| ≤ 1 := by simp
  have htime : (fun ω : ℕ → S => ∑' i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω)) =
      (fun ω => ∑' i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω) * (fun _ => (1:ℝ)) (ω i)) := by
    ext ω; simp
  have key : freezingReward P r a f x - freezingTime P a f x * ν =
      ∫ ω, ∑' i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω) * c (ω i) ∂markovChainMeasure P x := by
    unfold freezingReward freezingTime
    rw [htime, mul_comm, ← integral_const_mul, ← integral_sub (g70al_FR_int P x f ha0 ha1 r hK)
      ((g70al_FR_int P x f ha0 ha1 _ hK1).const_mul ν)]
    congr 1; ext ω
    rw [← tsum_mul_left, ← Summable.tsum_sub (g70al_FR_summ f ha0 ha1 r hK ω)
      ((g70al_FR_summ f ha0 ha1 _ hK1 ω).mul_left ν)]
    congr 1; ext i; simp only [hc]; ring
  have hw0 : ∀ n : ℕ, 0 ≤ a ^ n - a ^ (n + 1) := fun n => by
    have : a ^ (n + 1) ≤ a ^ n := pow_le_pow_of_le_one ha0.le ha1.le (by omega)
    linarith
  have hint : ∫ ω, ∑' i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω) * c (ω i)
      ∂markovChainMeasure P x =
      ∑' n : ℕ, ∫ ω, (a ^ n - a ^ (n + 1)) * g70al_G f a c n ω ∂markovChainMeasure P x := by
    haveI : IsProbabilityMeasure (markovChainMeasure P x) := by
      unfold markovChainMeasure; infer_instance
    simp_rw [g70al_decomp f ha0 ha1 c hKc]
    refine (integral_tsum_of_summable_integral_norm
      (fun n => (g70al_G_int P x f ha0 ha1 c hKc n).const_mul _) ?_).symm
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) (((summable_geometric_of_lt_one ha0.le ha1).mul_left (1 - a)).mul_right
        ((K + |ν|) * (1 - a)⁻¹))
    calc ∫ ω, ‖(a ^ n - a ^ (n + 1)) * g70al_G f a c n ω‖ ∂markovChainMeasure P x
        ≤ ∫ _ω, (a ^ n - a ^ (n + 1)) * ((K + |ν|) * (1 - a)⁻¹) ∂markovChainMeasure P x := by
          refine integral_mono ((g70al_G_int P x f ha0 ha1 c hKc n).const_mul _).norm
            (integrable_const _) fun ω => ?_
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hw0 n)]
          exact mul_le_mul_of_nonneg_left (g70al_G_bd f ha0 ha1 c hKc n ω) (hw0 n)
      _ = (1 - a) * a ^ n * ((K + |ν|) * (1 - a)⁻¹) := by
          rw [integral_const]; simp only [smul_eq_mul, probReal_univ, one_mul]; ring
  have hle : ∑' n : ℕ, ∫ ω, (a ^ n - a ^ (n + 1)) * g70al_G f a c n ω ∂markovChainMeasure P x ≤ 0 := by
    refine tsum_nonpos fun n => ?_
    rw [integral_const_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (hw0 n) (g70al_L P ⟨K, hK⟩ ha0 ha1 f x n)
  linarith


lemma g70al_top_stop : IsTrajStoppingTime (fun _ : ℕ → S => (⊤ : ℕ∞)) := by
  intro n; simp

lemma g70al_dss_top (a : ℝ) (g : S → ℝ) (ω : ℕ → S) :
    discountedStoppedSum a g (fun _ => ⊤) ω = ∑' i : ℕ, a ^ i * g (ω i) := by
  unfold discountedStoppedSum; simp

lemma g70al_fin_decomp (f : FreezingRule S) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (c : S → ℝ)
    {K : ℝ} (hK : ∀ s, |c s| ≤ K) (τ : ℕ) (hf : ∀ i ω, f.freeze i ω ≤ (τ : ℕ∞)) (ω : ℕ → S) :
    ∑' i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω) * c (ω i) -
      a ^ τ * discountedStoppedSum a c (fun _ => ⊤) ω =
      ∑ n ∈ Finset.range τ, (a ^ n - a ^ (n + 1)) * g70al_G f a c n ω := by
  have hK1 := g70al_summ (fun _ => (⊤ : ℕ∞)) ha0 ha1 c hK ω
  simp only [ENat.coe_lt_top, if_true] at hK1
  rw [g70al_dss_top, ← tsum_mul_left, ← Summable.tsum_sub (g70al_FR_summ f ha0 ha1 c hK ω)
    (hK1.mul_left _)]
  have hpt : ∀ i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω) * c (ω i) - a ^ τ * (a ^ i * c (ω i)) =
      ∑ n ∈ Finset.range τ, (if f.freeze i ω ≤ (n : ℕ∞) then
        (a ^ n - a ^ (n + 1)) * (a ^ i * c (ω i)) else 0) := by
    intro i
    have := g70al_dp_fin a (f.freeze i ω) τ (hf i ω)
    rw [g70al_dp_add]
    have e2 : ∑ n ∈ Finset.range τ, (if f.freeze i ω ≤ (n : ℕ∞) then
        (a ^ n - a ^ (n + 1)) * (a ^ i * c (ω i)) else 0) =
        (∑ n ∈ Finset.range τ, (if f.freeze i ω ≤ (n : ℕ∞) then a ^ n - a ^ (n + 1) else 0)) *
          (a ^ i * c (ω i)) := by
      rw [Finset.sum_mul]; congr 1; ext n; split_ifs <;> simp
    rw [e2, this]; ring
  rw [tsum_congr hpt, Summable.tsum_finsetSum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    unfold g70al_G
    rw [← tsum_mul_left]
    congr 1; ext i; split_ifs <;> simp
  · intro n _
    refine Summable.of_norm_bounded
      (((summable_geometric_of_lt_one ha0.le ha1).mul_left K).mul_left |a ^ n - a ^ (n + 1)|)
      fun i => ?_
    split_ifs
    · rw [norm_mul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := g70al_G_term_bd f ha0 c hK n ω i
      rwa [if_pos ‹_›] at this
    · simp only [norm_zero]
      have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK (ω 0))
      positivity

theorem g70al_T3 (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (τ : ℕ) (f : FreezingRule S)
    (hf : ∀ i ω, f.freeze i ω ≤ (τ : ℕ∞)) (x : S) :
    freezingReward P r a f x - a ^ τ * stoppedReward P r a (fun _ ↦ ⊤) x ≤
      gittinsIndex P r a x *
        (freezingTime P a f x - a ^ τ * stoppedTime P a (fun _ ↦ ⊤) x) := by
  haveI : IsProbabilityMeasure (markovChainMeasure P x) := by
    unfold markovChainMeasure; infer_instance
  obtain ⟨K, hK⟩ := hr
  set ν := gittinsIndex P r a x
  set c : S → ℝ := fun s => r s - ν with hc
  have hKc : ∀ s, |c s| ≤ K + |ν| := fun s => by
    simp only [hc]; exact (abs_sub _ _).trans (by linarith [hK s])
  have hK1 : ∀ s : S, |(fun _ => (1:ℝ)) s| ≤ 1 := by simp
  have htime : (fun ω : ℕ → S => ∑' i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω)) =
      (fun ω => ∑' i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω) * (fun _ => (1:ℝ)) (ω i)) := by
    ext ω; simp
  have key : freezingReward P r a f x - freezingTime P a f x * ν =
      ∫ ω, ∑' i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω) * c (ω i) ∂markovChainMeasure P x := by
    unfold freezingReward freezingTime
    rw [htime, mul_comm, ← integral_const_mul, ← integral_sub (g70al_FR_int P x f ha0 ha1 r hK)
      ((g70al_FR_int P x f ha0 ha1 _ hK1).const_mul ν)]
    congr 1; ext ω
    rw [← tsum_mul_left, ← Summable.tsum_sub (g70al_FR_summ f ha0 ha1 r hK ω)
      ((g70al_FR_summ f ha0 ha1 _ hK1 ω).mul_left ν)]
    congr 1; ext i; simp only [hc]; ring
  have key2 : stoppedReward P r a (fun _ ↦ ⊤) x - stoppedTime P a (fun _ ↦ ⊤) x * ν =
      ∫ ω, discountedStoppedSum a c (fun _ => ⊤) ω ∂markovChainMeasure P x := by
    unfold stoppedReward stoppedTime
    simp_rw [hc, g70al_dss_sub (fun _ => ⊤) ha0 ha1 r hK ν]
    rw [integral_sub (g70al_dss_int P x _ g70al_top_stop ha0 ha1 r hK)
      ((g70al_dss_int P x _ g70al_top_stop ha0 ha1 _ hK1).const_mul ν), integral_const_mul]
    ring
  have hw0 : ∀ n : ℕ, 0 ≤ a ^ n - a ^ (n + 1) := fun n => by
    have : a ^ (n + 1) ≤ a ^ n := pow_le_pow_of_le_one ha0.le ha1.le (by omega)
    linarith
  have hcomb : (∫ ω, ∑' i : ℕ, discountPow a ((i : ℕ∞) + f.freeze i ω) * c (ω i)
      ∂markovChainMeasure P x) - a ^ τ * ∫ ω, discountedStoppedSum a c (fun _ => ⊤) ω
        ∂markovChainMeasure P x =
      ∑ n ∈ Finset.range τ, (a ^ n - a ^ (n + 1)) *
        ∫ ω, g70al_G f a c n ω ∂markovChainMeasure P x := by
    rw [← integral_const_mul, ← integral_sub (g70al_FR_int P x f ha0 ha1 c hKc)
      ((g70al_dss_int P x _ g70al_top_stop ha0 ha1 c hKc).const_mul _)]
    simp_rw [g70al_fin_decomp f ha0 ha1 c hKc τ hf]
    rw [integral_finset_sum _ fun n _ => (g70al_G_int P x f ha0 ha1 c hKc n).const_mul _]
    simp_rw [integral_const_mul]
  have hle : ∑ n ∈ Finset.range τ, (a ^ n - a ^ (n + 1)) *
      ∫ ω, g70al_G f a c n ω ∂markovChainMeasure P x ≤ 0 :=
    Finset.sum_nonpos fun n _ =>
      mul_nonpos_of_nonneg_of_nonpos (hw0 n) (g70al_L P ⟨K, hK⟩ ha0 ha1 f x n)
  have : freezingReward P r a f x - freezingTime P a f x * ν -
      a ^ τ * (stoppedReward P r a (fun _ ↦ ⊤) x - stoppedTime P a (fun _ ↦ ⊤) x * ν) ≤ 0 := by
    rw [key, key2, hcomb]; exact hle
  nlinarith

end G70ALF

open AllocationIndices.Freezing

theorem solution {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (τ : ℕ) (f : FreezingRule S)
    (hf : ∀ i ω, f.freeze i ω ≤ (τ : ℕ∞)) (x : S) :
    freezingReward P r a f x - a ^ τ * stoppedReward P r a (fun _ ↦ ⊤) x ≤
      gittinsIndex P r a x *
        (freezingTime P a f x - a ^ τ * stoppedTime P a (fun _ ↦ ⊤) x) := by
  exact g70al_T3 P hr ha0 ha1 τ f hf x

