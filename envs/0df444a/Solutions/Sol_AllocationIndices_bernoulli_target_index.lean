-- Prove2me | solution 1 for AllocationIndices.bernoulli_target_index
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T12:34:41.495183+00:00
-- url     : https://prove2.me/submissions/2b96f0b3-6981-46d0-b8ce-7737e2a390b2

import Mathlib
import Definitions.Def_AllocationIndices_Sampling

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pba_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pba_marg0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : (markovChainMeasure P x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pba_int0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) (F : S → ℝ) (hF : Measurable F) :
    ∫ ω, F (ω 0) ∂markovChainMeasure P x = F x := by
  have hFm : Measurable (fun h : (Π _i : Finset.Iic 0, S) ↦ F (h ⟨0, Finset.mem_Iic.2 le_rfl⟩)) :=
    hF.comp (measurable_pi_apply _)
  have h1 := integral_map (μ := markovChainMeasure P x) (Preorder.measurable_frestrictLe 0).aemeasurable
    hFm.aestronglyMeasurable
  rw [pba_marg0, integral_dirac' _ _ hFm.stronglyMeasurable] at h1
  exact h1.symm

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pba_meas_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
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
private lemma pba_int_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pba_term_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (f : S → ℝ) (Bf : ℝ)
    (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (t : ℕ) :
    ‖(if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)‖ ≤ Bf * a ^ t := by
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hf _) (pow_nonneg ha0 t)
  · simp only [norm_zero]; positivity

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pba_summable {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_left Bf)
    (pba_term_bound a ha0 f Bf hBf hf τ ω)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pba_dss_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    |discountedStoppedSum a f τ ω| ≤ Bf / (1 - a) := by
  unfold discountedStoppedSum
  have hg : HasSum (fun t : ℕ ↦ Bf * a ^ t) (Bf * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0 ha1).mul_left Bf
  have := tsum_of_norm_bounded hg (pba_term_bound a ha0 f Bf hBf hf τ ω)
  rw [Real.norm_eq_abs] at this
  rwa [div_eq_mul_inv]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pba_dss_meas {S : Type*} [MeasurableSpace S] (a : ℝ) (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum a f τ) := by
  unfold discountedStoppedSum
  exact Measurable.tsum fun t ↦ Measurable.ite (pba_meas_lt τ hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t))) measurable_const

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pba_inv {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (G : Set S) (hG : MeasurableSet G) (hPG : ∀ y ∈ G, P y Gᶜ = 0) (x : S) (hx : x ∈ G) :
    ∀ t : ℕ, (markovChainMeasure P x) {ω | ω t ∉ G} = 0 := by
  haveI := pba_prob P x
  intro t
  induction t with
  | zero =>
    have hm : MeasurableSet {h : (Π _i : Finset.Iic 0, S) |
        h ⟨0, Finset.mem_Iic.2 le_rfl⟩ ∈ Gᶜ} :=
      (measurable_pi_apply (X := fun _ : Finset.Iic 0 ↦ S) ⟨0, Finset.mem_Iic.2 le_rfl⟩) hG.compl
    have h1 := Measure.map_apply (μ := markovChainMeasure P x)
      (Preorder.measurable_frestrictLe 0) hm
    rw [pba_marg0, Measure.dirac_apply' _ hm] at h1
    have h2 : Set.indicator {h : (Π _i : Finset.Iic 0, S) |
        h ⟨0, Finset.mem_Iic.2 le_rfl⟩ ∈ Gᶜ} (1 : (Π _i : Finset.Iic 0, S) → ENNReal)
        (fun _ ↦ x) = 0 := by
      rw [Set.indicator_of_notMem]
      intro hh; exact hh hx
    rw [h2] at h1
    exact h1.symm
  | succ t ih =>
    have hmap : (markovChainMeasure P x).map (Preorder.frestrictLe t) ⊗ₘ markovChainStep P t =
        (markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe t ω, ω (t + 1))) :=
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (X := fun _ : ℕ ↦ S)
        (μ₀ := Measure.dirac x) (κ := markovChainStep P) (a := t)
    have hΦ : Measurable (fun ω : ℕ → S ↦ (Preorder.frestrictLe t ω, ω (t + 1))) :=
      (Preorder.measurable_frestrictLe t).prodMk (measurable_pi_apply (t + 1))
    have hs : MeasurableSet ((Set.univ : Set (Π _i : Finset.Iic t, S)) ×ˢ Gᶜ) :=
      MeasurableSet.univ.prod hG.compl
    have h1 : (markovChainMeasure P x) {ω | ω (t + 1) ∉ G} =
        ((markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe t ω, ω (t + 1))))
          ((Set.univ : Set (Π _i : Finset.Iic t, S)) ×ˢ Gᶜ) := by
      rw [Measure.map_apply hΦ hs]; congr 1; ext ω; simp
    rw [h1, ← hmap, Measure.compProd_apply hs]
    have hmeasf : Measurable (fun h : (Π _i : Finset.Iic t, S) ↦
        P (h ⟨t, Finset.mem_Iic.2 le_rfl⟩) Gᶜ) :=
      (Kernel.measurable_coe P hG.compl).comp (measurable_pi_apply _)
    have heq : ∀ h : (Π _i : Finset.Iic t, S),
        markovChainStep P t h (Prod.mk h ⁻¹' ((Set.univ : Set (Π _i : Finset.Iic t, S)) ×ˢ Gᶜ)) =
          P (h ⟨t, Finset.mem_Iic.2 le_rfl⟩) Gᶜ := by
      intro h
      rw [markovChainStep, Kernel.comap_apply]
      congr 1
      ext y; simp
    simp_rw [heq]
    rw [lintegral_map hmeasf (Preorder.measurable_frestrictLe t)]
    have hae : ∀ᵐ ω ∂markovChainMeasure P x, P (ω t) Gᶜ = 0 := by
      rw [ae_iff]
      refine measure_mono_null (fun ω hω ↦ ?_) ih
      intro hωG
      exact hω (hPG _ hωG)
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae] with ω hω
    exact hω

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pba_summable_on {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (hf : ∀ t, |f (ω t)| ≤ Bf) :
    Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_left Bf)
    (fun t ↦ ?_)
  have hB : 0 ≤ Bf := le_trans (abs_nonneg _) (hf 0)
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hf t) (pow_nonneg ha0 t)
  · simp only [norm_zero]; positivity

private def pbaG (α β : ℝ) : Set ((ℝ × ℝ) ⊕ Unit) :=
  {s | Sum.elim (fun q : ℝ × ℝ ↦ q.1 = α ∧ β ≤ q.2) (fun _ ↦ True) s}

private lemma pbaG_meas (α β : ℝ) : MeasurableSet (pbaG α β) := by
  rw [measurableSet_sum_iff]
  constructor
  · show MeasurableSet {q : ℝ × ℝ | q.1 = α ∧ β ≤ q.2}
    exact (measurableSet_eq_fun measurable_fst measurable_const).inter
      (measurableSet_le measurable_const measurable_snd)
  · show MeasurableSet {_u : Unit | True}
    exact MeasurableSet.univ

open MeasureTheory ProbabilityTheory AllocationIndices in
private lemma pba_step_closed (α β : ℝ) (q : ℝ × ℝ)
    (hq : q.1 = α ∧ β ≤ q.2) : bernoulliTargetChain (Sum.inl q) (pbaG α β)ᶜ = 0 := by
  have hG := pbaG_meas α β
  show bernoulliTargetStep q (pbaG α β)ᶜ = 0
  rw [bernoulliTargetStep, Kernel.map_apply' _ measurable_bernoulliTargetFun _ hG.compl,
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left (measurable_bernoulliTargetFun hG.compl)]
  convert measure_empty (μ := uniformUnit)
  ext z
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
  split_ifs with h
  · exact trivial
  · show (q.1, q.2 + 1).1 = α ∧ β ≤ (q.1, q.2 + 1).2
    exact ⟨hq.1, by simp only; linarith [hq.2]⟩

open MeasureTheory ProbabilityTheory AllocationIndices in
private lemma pba_closed (α β : ℝ) :
    ∀ y ∈ pbaG α β, bernoulliTargetChain y (pbaG α β)ᶜ = 0 := by
  rintro (q | u) hy
  · exact pba_step_closed α β q hy
  · show Measure.dirac (Sum.inr ()) (pbaG α β)ᶜ = 0
    rw [Measure.dirac_apply' _ (pbaG_meas α β).compl, Set.indicator_of_notMem]
    intro hh; exact hh trivial

open MeasureTheory ProbabilityTheory AllocationIndices in
private lemma pba_rew_bd (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∀ y ∈ pbaG α β, 0 ≤ bernoulliTargetReward y ∧ bernoulliTargetReward y ≤ α / (α + β) := by
  rintro (q | u) hy
  · obtain ⟨h1, h2⟩ := hy
    show 0 ≤ q.1 / (q.1 + q.2) ∧ q.1 / (q.1 + q.2) ≤ α / (α + β)
    rw [h1]
    refine ⟨div_nonneg hα.le (by linarith), ?_⟩
    exact div_le_div_of_nonneg_left hα.le (by linarith) (by linarith)
  · show 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ α / (α + β)
    exact ⟨le_rfl, div_nonneg hα.le (by linarith)⟩

open MeasureTheory ProbabilityTheory AllocationIndices in
private lemma pba_rew_meas : Measurable bernoulliTargetReward := by
  have h : Measurable (fun p : ℝ × ℝ ↦ p.1 / (p.1 + p.2)) := by fun_prop
  exact h.sumElim measurable_const

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
theorem solution {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1) :
    gittinsIndex bernoulliTargetChain bernoulliTargetReward a (Sum.inl (α, β)) =
      α / (α + β) := by
  haveI := pba_prob bernoulliTargetChain (Sum.inl (α, β))
  have hr0 : 0 ≤ α / (α + β) := div_nonneg hα.le (by linarith)
  have hx : (Sum.inl (α, β) : (ℝ × ℝ) ⊕ Unit) ∈ pbaG α β := ⟨rfl, le_rfl⟩
  have hinv := pba_inv bernoulliTargetChain (pbaG α β) (pbaG_meas α β) (pba_closed α β)
    _ hx
  have hall : ∀ᵐ ω ∂markovChainMeasure bernoulliTargetChain (Sum.inl (α, β)),
      ∀ t, ω t ∈ pbaG α β := by
    rw [ae_all_iff]
    intro t
    rw [ae_iff]
    exact hinv t
  unfold gittinsIndex
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun _ ↦ 1, fun k ↦ MeasurableSet.const _, fun _ ↦ le_rfl, ?_⟩
    have hd : ∀ (f : (ℝ × ℝ) ⊕ Unit → ℝ) (ω : ℕ → (ℝ × ℝ) ⊕ Unit),
        discountedStoppedSum a f (fun _ ↦ 1) ω = f (ω 0) := by
      intro f ω
      unfold discountedStoppedSum
      rw [tsum_eq_single 0]
      · simp
      · intro t ht
        have : ¬ ((t : ℕ∞) < 1) := by
          intro h
          have : t < 1 := by exact_mod_cast h
          omega
        simp [this]
    simp only [hd]
    rw [pba_int0 _ _ _ pba_rew_meas, integral_const]
    simp only [probReal_univ, smul_eq_mul, mul_one, div_one]
    rfl
  · rintro g ⟨τ, hτ, hτ1, rfl⟩
    have hW0 : 0 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω
        ∂markovChainMeasure bernoulliTargetChain (Sum.inl (α, β)) := by
      refine integral_nonneg (fun ω ↦ ?_)
      unfold discountedStoppedSum
      refine tsum_nonneg (fun t ↦ ?_)
      split_ifs
      · positivity
      · exact le_rfl
    have hWint : Integrable (discountedStoppedSum a (fun _ ↦ (1 : ℝ)) τ)
        (markovChainMeasure bernoulliTargetChain (Sum.inl (α, β))) :=
      pba_int_of_bound _ _ (pba_dss_meas a _ measurable_const τ hτ) (1 / (1 - a))
        (pba_dss_bound a ha0.le ha1 _ 1 zero_le_one (fun _ ↦ by simp) τ)
    by_cases hR : Integrable (discountedStoppedSum a bernoulliTargetReward τ)
        (markovChainMeasure bernoulliTargetChain (Sum.inl (α, β)))
    · have hle := integral_mono_ae hR (hWint.const_mul (α / (α + β))) (by
          filter_upwards [hall] with ω hω
          have hb : ∀ t, |bernoulliTargetReward (ω t)| ≤ α / (α + β) := by
            intro t
            obtain ⟨h1, h2⟩ := pba_rew_bd α β hα hβ (ω t) (hω t)
            rw [abs_of_nonneg h1]; exact h2
          unfold discountedStoppedSum
          rw [← tsum_mul_left]
          refine Summable.tsum_le_tsum (fun t ↦ ?_)
            (pba_summable_on a ha0.le ha1 _ _ τ ω hb)
            ((pba_summable a ha0.le ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one
              (fun _ ↦ by simp) τ ω).mul_left _)
          split_ifs
          · have := (pba_rew_bd α β hα hβ (ω t) (hω t)).2
            have hat : 0 ≤ a ^ t := pow_nonneg ha0.le t
            nlinarith
          · simp)
      rw [integral_const_mul] at hle
      rcases hW0.eq_or_lt with h | h
      · rw [← h, div_zero]; exact hr0
      · rw [div_le_iff₀ h]; linarith
    · rw [integral_undef hR, zero_div]; exact hr0
