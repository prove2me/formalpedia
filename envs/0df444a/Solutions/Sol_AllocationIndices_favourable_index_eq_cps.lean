-- Prove2me | solution 1 for AllocationIndices.favourable_index_eq_cps
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:32:22.767334+00:00
-- url     : https://prove2.me/submissions/a7eb0312-1581-4adb-b3ee-621475486059

import Mathlib
import Definitions.Def_AllocationIndices_Sampling

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m71_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m71_marg0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : (markovChainMeasure P x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m71_int0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) (F : S → ℝ) (hF : Measurable F) :
    ∫ ω, F (ω 0) ∂markovChainMeasure P x = F x := by
  have hFm : Measurable (fun h : (Π _i : Finset.Iic 0, S) ↦ F (h ⟨0, Finset.mem_Iic.2 le_rfl⟩)) :=
    hF.comp (measurable_pi_apply _)
  have h1 := integral_map (μ := markovChainMeasure P x) (Preorder.measurable_frestrictLe 0).aemeasurable
    hFm.aestronglyMeasurable
  rw [p2m71_marg0, integral_dirac' _ _ hFm.stronglyMeasurable] at h1
  exact h1.symm

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m71_step {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) (s : ℕ) (C : Set S) (hC : MeasurableSet C) :
    markovChainMeasure P x {ω | ω (s + 1) ∈ C} =
      ∫⁻ ω, P (ω s) C ∂markovChainMeasure P x := by
  haveI := p2m71_prob P x
  have hmap : (markovChainMeasure P x).map (Preorder.frestrictLe s) ⊗ₘ markovChainStep P s =
      (markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe s ω, ω (s + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (X := fun _ : ℕ ↦ S)
      (μ₀ := Measure.dirac x) (κ := markovChainStep P) (a := s)
  have hΦ : Measurable (fun ω : ℕ → S ↦ (Preorder.frestrictLe s ω, ω (s + 1))) :=
    (Preorder.measurable_frestrictLe s).prodMk (measurable_pi_apply (s + 1))
  have hmeas : Measurable (fun h : (Π _i : Finset.Iic s, S) ↦
      P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) C) :=
    (Kernel.measurable_coe P hC).comp (measurable_pi_apply _)
  have hset : {ω : ℕ → S | ω (s + 1) ∈ C} =
      (fun ω : ℕ → S ↦ (Preorder.frestrictLe s ω, ω (s + 1))) ⁻¹'
        ((Set.univ : Set (Π _i : Finset.Iic s, S)) ×ˢ C) := by
    ext ω; simp
  rw [hset, ← Measure.map_apply hΦ (MeasurableSet.univ.prod hC), ← hmap,
    Measure.compProd_apply_prod MeasurableSet.univ hC, Measure.restrict_univ]
  have hk : ∀ h : (Π _i : Finset.Iic s, S),
      markovChainStep P s h C = P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) C := by
    intro h
    rw [markovChainStep, Kernel.comap_apply]
  simp_rw [hk]
  exact lintegral_map hmeas (Preorder.measurable_frestrictLe s)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m71_inv {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (G : Set S) (hG : ∀ y ∈ G, ∀ C : Set S, MeasurableSet C → G ⊆ C → P y Cᶜ = 0)
    (x : S) (hx : x ∈ G) (t : ℕ) :
    ∀ C : Set S, MeasurableSet C → G ⊆ C → markovChainMeasure P x {ω | ω t ∉ C} = 0 := by
  induction t with
  | zero =>
    intro C hC hGC
    have hset : MeasurableSet
        {h : (Π _i : Finset.Iic 0, S) | h ⟨0, Finset.mem_Iic.2 le_rfl⟩ ∉ C} :=
      (measurable_pi_apply (X := fun _ : Finset.Iic 0 ↦ S) ⟨0, Finset.mem_Iic.2 le_rfl⟩) hC.compl
    have : {ω : ℕ → S | ω 0 ∉ C} = Preorder.frestrictLe 0 ⁻¹'
        {h : (Π _i : Finset.Iic 0, S) | h ⟨0, Finset.mem_Iic.2 le_rfl⟩ ∉ C} := rfl
    rw [this, ← Measure.map_apply (Preorder.measurable_frestrictLe 0) hset, p2m71_marg0,
      Measure.dirac_apply' _ hset, Set.indicator_of_notMem]
    simp only [Set.mem_setOf_eq, not_not]
    exact hGC hx
  | succ t ih =>
    intro C hC hGC
    have hC' : MeasurableSet {y | P y Cᶜ = 0} :=
      Kernel.measurable_coe P hC.compl (measurableSet_singleton 0)
    have hGC' : G ⊆ {y | P y Cᶜ = 0} := fun y hy ↦ hG y hy C hC hGC
    have h0 := ih _ hC' hGC'
    have : {ω : ℕ → S | ω (t + 1) ∉ C} = {ω | ω (t + 1) ∈ Cᶜ} := rfl
    rw [this, p2m71_step P x t Cᶜ hC.compl]
    have hae : (fun ω : ℕ → S ↦ P (ω t) Cᶜ) =ᵐ[markovChainMeasure P x] fun _ ↦ 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      exact measure_mono_null (fun ω hω ↦ hω) h0
    rw [lintegral_congr_ae hae, lintegral_zero]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m71_chain_inl {Θ Q : Type*} [MeasurableSpace Θ] [MeasurableSpace Q]
    (F : SamplingModel Θ Q) (T : ℝ) (p : Q) :
    F.targetChain T (Sum.inl p) = (F.predictive p).map
      (fun x ↦ if T ≤ x then (Sum.inr () : Q ⊕ Unit) else Sum.inl (F.update p x)) := by
  show F.targetStep T p = _
  rw [SamplingModel.targetStep, Kernel.map_apply _ (F.measurable_targetStepFun T),
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map (F.measurable_targetStepFun T) measurable_prodMk_left]
  rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m71_summable {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (hf : ∀ y, |f y| ≤ 1) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) := by
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one ha0 ha1) (fun t ↦ ?_)
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0]
    calc a ^ t * |f (ω t)| ≤ a ^ t * 1 := mul_le_mul_of_nonneg_left (hf _) (pow_nonneg ha0 t)
      _ = a ^ t := mul_one _
  · simp only [norm_zero]; exact pow_nonneg ha0 t

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
theorem solution {Θ P : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    [Nonempty Θ] [MeasurableSpace P] (F : SamplingModel Θ P) (hconj : F.IsConjugate) (T : ℝ)
    (p : P) (hfav : F.IsFavourable T p) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    gittinsIndex (F.targetChain T) (F.targetReward T) a (Sum.inl p) =
      F.targetReward T (Sum.inl p) := by
  set c := F.targetReward T (Sum.inl p) with hc
  haveI := p2m71_prob (F.targetChain T) (Sum.inl p)
  have hr : Measurable (F.targetReward T) := by
    unfold SamplingModel.targetReward
    exact Measurable.sumElim
      ((F.predictive.measurable_coe measurableSet_Ici).ennreal_toReal) measurable_const
  have hrb : ∀ s, 0 ≤ F.targetReward T s ∧ F.targetReward T s ≤ 1 := by
    rintro (q | u)
    · refine ⟨ENNReal.toReal_nonneg, ?_⟩
      have := ENNReal.toReal_mono ENNReal.one_ne_top
        (prob_le_one (μ := F.predictive q) (s := Set.Ici T))
      simpa [SamplingModel.targetReward] using this
    · exact ⟨le_rfl, zero_le_one⟩
  have hrabs : ∀ s, |F.targetReward T s| ≤ 1 := fun s ↦ by
    rw [abs_of_nonneg (hrb s).1]; exact (hrb s).2
  have hc0 : 0 ≤ c := (hrb _).1
  -- the reachable set
  have hG : ∀ y ∈ {s : P ⊕ Unit | s = Sum.inr () ∨
      ∃ xs : List ℝ, (∀ x ∈ xs, x < T) ∧ s = Sum.inl (xs.foldl F.update p)},
      ∀ C : Set (P ⊕ Unit), MeasurableSet C → {s : P ⊕ Unit | s = Sum.inr () ∨
        ∃ xs : List ℝ, (∀ x ∈ xs, x < T) ∧ s = Sum.inl (xs.foldl F.update p)} ⊆ C →
        F.targetChain T y Cᶜ = 0 := by
    intro y hy C hC hGC
    rcases hy with rfl | ⟨xs, hxs, rfl⟩
    · show (Measure.dirac (Sum.inr ())) Cᶜ = 0
      rw [Measure.dirac_apply' _ hC.compl, Set.indicator_of_notMem]
      simp only [Set.mem_compl_iff, not_not]
      exact hGC (Or.inl rfl)
    · rw [p2m71_chain_inl]
      have hgm : Measurable (fun x ↦ if T ≤ x then (Sum.inr () : P ⊕ Unit)
          else Sum.inl (F.update (xs.foldl F.update p) x)) :=
        (F.measurable_targetStepFun T).comp measurable_prodMk_left
      rw [Measure.map_apply hgm hC.compl]
      refine measure_mono_null (fun x hx ↦ ?_) measure_empty
      exfalso
      apply hx
      apply hGC
      by_cases hT : T ≤ x
      · left; simp [hT]
      · right
        refine ⟨xs ++ [x], fun y hy ↦ ?_, by simp [hT, List.foldl_append]⟩
        rcases List.mem_append.1 hy with h | h
        · exact hxs y h
        · rw [List.mem_singleton] at h; subst h; exact lt_of_not_ge hT
  have hGC : {s : P ⊕ Unit | s = Sum.inr () ∨
      ∃ xs : List ℝ, (∀ x ∈ xs, x < T) ∧ s = Sum.inl (xs.foldl F.update p)} ⊆
      {s | F.targetReward T s ≤ c} := by
    rintro s (rfl | ⟨xs, hxs, rfl⟩)
    · show (0 : ℝ) ≤ c
      exact hc0
    · exact hfav xs hxs
  have hae : ∀ t : ℕ, ∀ᵐ ω ∂markovChainMeasure (F.targetChain T) (Sum.inl p),
      F.targetReward T (ω t) ≤ c := by
    intro t
    rw [ae_iff]
    exact p2m71_inv (F.targetChain T) _ hG (Sum.inl p) (Or.inr ⟨[], by simp, rfl⟩) t
      {s | F.targetReward T s ≤ c} (measurableSet_le hr measurable_const) hGC
  have hall := ae_all_iff.2 hae
  unfold gittinsIndex
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun _ ↦ 1, fun n ↦ MeasurableSet.const _, fun _ ↦ le_rfl, ?_⟩
    have h1 : ∀ f : (P ⊕ Unit) → ℝ, ∀ ω : ℕ → P ⊕ Unit,
        discountedStoppedSum a f (fun _ ↦ 1) ω = f (ω 0) := by
      intro f ω
      unfold discountedStoppedSum
      rw [tsum_eq_single 0]
      · simp
      · intro t ht
        have : ¬ ((t : ℕ∞) < 1) := by
          intro h
          apply ht
          exact_mod_cast ENat.lt_one_iff_eq_zero.1 h
        rw [if_neg this]
    simp only [h1]
    rw [p2m71_int0 _ _ (F.targetReward T) hr,
      p2m71_int0 _ _ (fun _ ↦ (1 : ℝ)) measurable_const, div_one]
  · rintro g ⟨τ, hτ, hτ1, rfl⟩
    have hdss0 : ∀ ω, 0 ≤ discountedStoppedSum a (fun _ ↦ (1 : ℝ)) τ ω := by
      intro ω
      unfold discountedStoppedSum
      refine tsum_nonneg fun t ↦ ?_
      split_ifs
      · exact mul_nonneg (pow_nonneg ha0.le t) zero_le_one
      · exact le_rfl
    have hW0 : 0 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ (1 : ℝ)) τ ω
        ∂markovChainMeasure (F.targetChain T) (Sum.inl p) :=
      integral_nonneg hdss0
    rcases hW0.eq_or_lt with hW | hW
    · rw [← hW, div_zero]; exact hc0
    · rw [div_le_iff₀ hW]
      have hWint : Integrable (discountedStoppedSum a (fun _ ↦ (1 : ℝ)) τ)
          (markovChainMeasure (F.targetChain T) (Sum.inl p)) := by
        by_contra h
        rw [integral_undef h] at hW
        exact lt_irrefl _ hW
      by_cases hRint : Integrable (discountedStoppedSum a (F.targetReward T) τ)
          (markovChainMeasure (F.targetChain T) (Sum.inl p))
      · rw [← integral_const_mul]
        refine integral_mono_ae hRint (hWint.const_mul c) ?_
        filter_upwards [hall] with ω hω
        unfold discountedStoppedSum
        rw [← tsum_mul_left]
        refine Summable.tsum_le_tsum (fun t ↦ ?_)
          (p2m71_summable a ha0.le ha1 _ hrabs τ ω)
          ((p2m71_summable a ha0.le ha1 (fun _ ↦ (1 : ℝ))
            (fun _ ↦ by simp) τ ω).mul_left c)
        dsimp only
        split_ifs
        · calc a ^ t * F.targetReward T (ω t) ≤ a ^ t * c :=
                mul_le_mul_of_nonneg_left (hω t) (pow_nonneg ha0.le t)
            _ = c * (a ^ t * 1) := by ring
        · simp
      · rw [integral_undef hRint]
        exact mul_nonneg hc0 hW.le
