-- Prove2me | solution 1 for AllocationIndices.adaptive_greedy_indices_eq_gittins
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T14:37:47.659595+00:00
-- url     : https://prove2.me/submissions/b15038cf-b5b6-4fc3-9ea4-7e71aa7dd147

import Mathlib
import Definitions.Def_AllocationIndices_Achievable

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_marg0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : (markovChainMeasure P x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_int0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) (F : S → ℝ) (hF : Measurable F) :
    ∫ ω, F (ω 0) ∂markovChainMeasure P x = F x := by
  have hFm : Measurable (fun h : (Π _i : Finset.Iic 0, S) ↦ F (h ⟨0, Finset.mem_Iic.2 le_rfl⟩)) :=
    hF.comp (measurable_pi_apply _)
  have h1 := integral_map (μ := markovChainMeasure P x) (Preorder.measurable_frestrictLe 0).aemeasurable
    hFm.aestronglyMeasurable
  rw [p2mbf_marg0, integral_dirac' _ _ hFm.stronglyMeasurable] at h1
  exact h1.symm

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_meas_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
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
private lemma p2mbf_filt_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) (t : ℕ) :
    MeasurableSet[trajectoryFiltration S t] {ω : ℕ → S | (t : ℕ∞) < τ ω} := by
  have : {ω : ℕ → S | (t : ℕ∞) < τ ω} = {ω | τ ω ≤ (t : ℕ∞)}ᶜ := by
    ext ω; simp [not_le]
  rw [this]
  exact (hτ t).compl

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_int_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_abs_int_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → ℝ) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    |∫ x, F x ∂μ| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := B)
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_term_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (f : S → ℝ) (Bf : ℝ)
    (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (t : ℕ) :
    ‖(if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)‖ ≤ Bf * a ^ t := by
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hf _) (pow_nonneg ha0 t)
  · simp only [norm_zero]; positivity

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_summable {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_left Bf)
    (p2mbf_term_bound a ha0 f Bf hBf hf τ ω)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_dss_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    |discountedStoppedSum a f τ ω| ≤ Bf / (1 - a) := by
  unfold discountedStoppedSum
  have hg : HasSum (fun t : ℕ ↦ Bf * a ^ t) (Bf * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0 ha1).mul_left Bf
  have := tsum_of_norm_bounded hg (p2mbf_term_bound a ha0 f Bf hBf hf τ ω)
  rw [Real.norm_eq_abs] at this
  rwa [div_eq_mul_inv]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_tail {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (N : ℕ) :
    |discountedStoppedSum a f τ ω -
        ∑ t ∈ Finset.range N, (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)| ≤
      Bf * a ^ N / (1 - a) := by
  unfold discountedStoppedSum
  have hs := p2mbf_summable a ha0 ha1 f Bf hBf hf τ ω
  rw [← hs.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have hg : HasSum (fun t : ℕ ↦ Bf * a ^ N * a ^ t) (Bf * a ^ N * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0 ha1).mul_left (Bf * a ^ N)
  have := tsum_of_norm_bounded hg (fun t ↦ by
    have h := p2mbf_term_bound a ha0 f Bf hBf hf τ ω (t + N)
    calc _ ≤ Bf * a ^ (t + N) := h
      _ = Bf * a ^ N * a ^ t := by ring)
  rw [Real.norm_eq_abs] at this
  rwa [div_eq_mul_inv]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_dss_meas {S : Type*} [MeasurableSpace S] (a : ℝ) (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum a f τ) := by
  unfold discountedStoppedSum
  exact Measurable.tsum fun t ↦ Measurable.ite (p2mbf_meas_lt τ hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t))) measurable_const

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_dss_int {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : S → ℝ) (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) :
    Integrable (discountedStoppedSum a f τ) (markovChainMeasure P x) := by
  haveI := p2mbf_prob P x
  exact p2mbf_int_of_bound _ _ (p2mbf_dss_meas a f Measurable.of_discrete τ hτ) (Bf / (1 - a))
    (p2mbf_dss_bound a ha0 ha1 f Bf hBf hf τ)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_dss_neg {S : Type*} (a : ℝ) (f : S → ℝ) (τ : (ℕ → S) → ℕ∞)
    (ω : ℕ → S) :
    discountedStoppedSum a (fun y ↦ -f y) τ ω = -discountedStoppedSum a f τ ω := by
  unfold discountedStoppedSum
  rw [← tsum_neg]
  refine tsum_congr fun t ↦ ?_
  split_ifs <;> ring

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_markov {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (s : ℕ) (A : Set (ℕ → S))
    (hA : MeasurableSet[trajectoryFiltration S s] A) (g : S → ℝ) (Bg : ℝ)
    (hg : ∀ y, |g y| ≤ Bg) :
    ∫ ω, A.indicator (fun ω ↦ g (ω (s + 1))) ω ∂markovChainMeasure P x =
      ∫ ω, A.indicator (fun ω ↦ ∫ z, g z ∂P (ω s)) ω ∂markovChainMeasure P x := by
  haveI := p2mbf_prob P x
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  have hgm : Measurable g := Measurable.of_discrete
  have hPgm : Measurable (fun y ↦ ∫ z, g z ∂P y) := Measurable.of_discrete
  have hmap : (markovChainMeasure P x).map (Preorder.frestrictLe s) ⊗ₘ markovChainStep P s =
      (markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe s ω, ω (s + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (X := fun _ : ℕ ↦ S)
      (μ₀ := Measure.dirac x) (κ := markovChainStep P) (a := s)
  have hΦ : Measurable (fun ω : ℕ → S ↦ (Preorder.frestrictLe s ω, ω (s + 1))) :=
    (Preorder.measurable_frestrictLe s).prodMk (measurable_pi_apply (s + 1))
  have hFm : Measurable ((B ×ˢ (Set.univ : Set S)).indicator
      (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2)) :=
    (hgm.comp measurable_snd).indicator (hB.prod MeasurableSet.univ)
  have hFint : Integrable ((B ×ˢ (Set.univ : Set S)).indicator
      (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2))
      ((markovChainMeasure P x).map (Preorder.frestrictLe s) ⊗ₘ markovChainStep P s) :=
    p2mbf_int_of_bound _ _ hFm Bg (fun p ↦ by
      by_cases hp : p ∈ B ×ˢ (Set.univ : Set S)
      · rw [Set.indicator_of_mem hp]; exact hg _
      · rw [Set.indicator_of_notMem hp, abs_zero]; exact le_trans (abs_nonneg _) (hg p.2))
  have hGm : Measurable (B.indicator
      (fun h : (Π _i : Finset.Iic s, S) ↦ ∫ z, g z ∂P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩))) :=
    (hPgm.comp (measurable_pi_apply _)).indicator hB
  calc ∫ ω, ((fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B).indicator (fun ω ↦ g (ω (s + 1))) ω
        ∂markovChainMeasure P x
      = ∫ ω, (B ×ˢ (Set.univ : Set S)).indicator
          (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2)
          (Preorder.frestrictLe s ω, ω (s + 1)) ∂markovChainMeasure P x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        dsimp only
        by_cases h : Preorder.frestrictLe s ω ∈ B
        · rw [Set.indicator_of_mem (show ω ∈ (fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B from h),
            Set.indicator_of_mem (show (Preorder.frestrictLe s ω, ω (s + 1)) ∈
              B ×ˢ (Set.univ : Set S) from ⟨h, trivial⟩)]
        · rw [Set.indicator_of_notMem
              (show ω ∉ (fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B from h),
            Set.indicator_of_notMem (show (Preorder.frestrictLe s ω, ω (s + 1)) ∉
              B ×ˢ (Set.univ : Set S) from fun hh ↦ h hh.1)]
    _ = ∫ p, (B ×ˢ (Set.univ : Set S)).indicator
          (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2) p
          ∂((markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe s ω, ω (s + 1)))) :=
        (integral_map hΦ.aemeasurable hFm.aestronglyMeasurable).symm
    _ = ∫ p, (B ×ˢ (Set.univ : Set S)).indicator
          (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2) p
          ∂((markovChainMeasure P x).map (Preorder.frestrictLe s) ⊗ₘ markovChainStep P s) := by
        rw [hmap]
    _ = ∫ h, ∫ y, (B ×ˢ (Set.univ : Set S)).indicator
          (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2) (h, y) ∂(markovChainStep P s h)
          ∂((markovChainMeasure P x).map (Preorder.frestrictLe s)) :=
        Measure.integral_compProd hFint
    _ = ∫ h, B.indicator
          (fun h : (Π _i : Finset.Iic s, S) ↦ ∫ z, g z ∂P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩)) h
          ∂((markovChainMeasure P x).map (Preorder.frestrictLe s)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
        have hk : markovChainStep P s h = P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) := by
          rw [markovChainStep, Kernel.comap_apply]
        simp only
        rw [hk]
        by_cases hh : h ∈ B
        · rw [Set.indicator_of_mem hh]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
          exact Set.indicator_of_mem
            (show (h, y) ∈ B ×ˢ (Set.univ : Set S) from ⟨hh, trivial⟩) _
        · rw [Set.indicator_of_notMem hh]
          exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y ↦
            Set.indicator_of_notMem (fun hh' ↦ hh hh'.1) _)
    _ = ∫ ω, B.indicator
          (fun h : (Π _i : Finset.Iic s, S) ↦ ∫ z, g z ∂P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩))
          (Preorder.frestrictLe s ω) ∂markovChainMeasure P x :=
        integral_map (Preorder.measurable_frestrictLe s).aemeasurable hGm.aestronglyMeasurable
    _ = ∫ ω, ((fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B).indicator
          (fun ω ↦ ∫ z, g z ∂P (ω s)) ω ∂markovChainMeasure P x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        dsimp only
        by_cases h : Preorder.frestrictLe s ω ∈ B
        · rw [Set.indicator_of_mem h,
            Set.indicator_of_mem (show ω ∈ (fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B from h)]
          rfl
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem
            (show ω ∉ (fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B from h)]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mbf_core {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f G : S → ℝ) (Bf BG : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (hG : ∀ y, |G y| ≤ BG)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (hτ1 : ∀ ω, 1 ≤ τ ω)
    (H : ∀ (ω : ℕ → S) (n : ℕ),
      (if ((n + 1 : ℕ) : ℕ∞) < τ ω then f (ω (n + 1)) + a * ∫ z, G z ∂P (ω (n + 1)) else 0) ≤
        (if (n : ℕ∞) < τ ω then G (ω (n + 1)) else 0))
    (x : S) :
    ∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P x ≤
      f x + a * ∫ z, G z ∂P x := by
  haveI hprob := p2mbf_prob P x
  have hBG : 0 ≤ BG := le_trans (abs_nonneg _) (hG x)
  have hPGb : ∀ y, |∫ z, G z ∂P y| ≤ BG := fun y ↦ p2mbf_abs_int_le (P y) G BG hG
  have hfm : Measurable f := Measurable.of_discrete
  have hGm : Measurable G := Measurable.of_discrete
  have hPGm : Measurable (fun y ↦ ∫ z, G z ∂P y) := Measurable.of_discrete
  have htm : ∀ t : ℕ, Measurable
      (fun ω : ℕ → S ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) :=
    fun t ↦ Measurable.ite (p2mbf_meas_lt τ hτ t)
      (measurable_const.mul (hfm.comp (measurable_pi_apply t))) measurable_const
  have htint : ∀ t : ℕ, Integrable
      (fun ω : ℕ → S ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)
      (markovChainMeasure P x) := fun t ↦
    p2mbf_int_of_bound _ _ (htm t) (Bf * a ^ t) (fun ω ↦ by
      have := p2mbf_term_bound a ha0 f Bf hBf hf τ ω t
      rwa [Real.norm_eq_abs] at this)
  have hYint : ∀ N : ℕ, Integrable (fun ω : ℕ → S ↦ ∑ t ∈ Finset.range N,
      (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) (markovChainMeasure P x) :=
    fun N ↦ integrable_finset_sum _ (fun t _ ↦ htint t)
  have hLint : ∀ n : ℕ, Integrable (fun ω : ℕ → S ↦
      if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0)
      (markovChainMeasure P x) := by
    intro n
    refine p2mbf_int_of_bound _ _ ?_ (a ^ (n + 1) * BG) (fun ω ↦ ?_)
    · exact Measurable.ite (p2mbf_meas_lt τ hτ n)
        (measurable_const.mul (hPGm.comp (measurable_pi_apply n))) measurable_const
    · split_ifs
      · rw [abs_mul, abs_pow, abs_of_nonneg ha0]
        exact mul_le_mul_of_nonneg_left (hPGb _) (pow_nonneg ha0 _)
      · simp only [abs_zero]; positivity
  have hM1int : ∀ n : ℕ, Integrable (fun ω : ℕ → S ↦
      {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ G (ω (n + 1))) ω)
      (markovChainMeasure P x) := fun n ↦
    (p2mbf_int_of_bound _ _ (hGm.comp (measurable_pi_apply (n + 1))) BG
      (fun ω ↦ hG _)).indicator (p2mbf_meas_lt τ hτ n)
  have hM2int : ∀ n : ℕ, Integrable (fun ω : ℕ → S ↦
      {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ ∫ z, G z ∂P (ω n)) ω)
      (markovChainMeasure P x) := fun n ↦
    (p2mbf_int_of_bound _ _ (hPGm.comp (measurable_pi_apply n)) BG
      (fun ω ↦ hPGb _)).indicator (p2mbf_meas_lt τ hτ n)
  have hstep : ∀ n : ℕ,
      ∫ ω, ((∑ t ∈ Finset.range (n + 1 + 1),
          (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
          (if ((n + 1 : ℕ) : ℕ∞) < τ ω then a ^ (n + 1 + 1) * ∫ z, G z ∂P (ω (n + 1)) else 0))
          ∂markovChainMeasure P x ≤
      ∫ ω, ((∑ t ∈ Finset.range (n + 1),
          (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
          (if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0))
          ∂markovChainMeasure P x := by
    intro n
    have hmk := p2mbf_markov P x n {ω : ℕ → S | (n : ℕ∞) < τ ω} (p2mbf_filt_lt τ hτ n) G BG hG
    have hpath : ∀ ω : ℕ → S,
        (∑ t ∈ Finset.range (n + 1 + 1), (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
          (if ((n + 1 : ℕ) : ℕ∞) < τ ω then a ^ (n + 1 + 1) * ∫ z, G z ∂P (ω (n + 1))
            else 0) ≤
        ((∑ t ∈ Finset.range (n + 1), (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
          (if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0)) +
          (a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ G (ω (n + 1))) ω -
           a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator
              (fun ω ↦ ∫ z, G z ∂P (ω n)) ω) := by
      intro ω
      have hH := H ω n
      have hp : 0 ≤ a ^ (n + 1) := pow_nonneg ha0 _
      have hmono : ((n + 1 : ℕ) : ℕ∞) < τ ω → (n : ℕ∞) < τ ω :=
        fun h ↦ lt_trans (by exact_mod_cast Nat.lt_succ_self n) h
      rw [Finset.sum_range_succ _ (n + 1)]
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      by_cases h1 : ((n + 1 : ℕ) : ℕ∞) < τ ω
      · have h0 := hmono h1
        simp only [if_pos h1, if_pos h0] at hH ⊢
        have key := mul_le_mul_of_nonneg_left hH hp
        rw [pow_succ a (n + 1)]
        nlinarith [key]
      · by_cases h0 : (n : ℕ∞) < τ ω
        · simp only [if_neg h1, if_pos h0] at hH ⊢
          nlinarith [mul_nonneg hp hH]
        · simp only [if_neg h1, if_neg h0]
          linarith
    calc _ ≤ ∫ ω, (((∑ t ∈ Finset.range (n + 1),
            (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
            (if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0)) +
            (a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ G (ω (n + 1))) ω -
             a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator
                (fun ω ↦ ∫ z, G z ∂P (ω n)) ω)) ∂markovChainMeasure P x :=
          integral_mono (((hYint (n + 1 + 1)).add (hLint (n + 1))))
            (((hYint (n + 1)).add (hLint n)).add
              (((hM1int n).const_mul _).sub ((hM2int n).const_mul _))) hpath
      _ = _ := by
          have hA : Integrable (fun ω : ℕ → S ↦ (∑ t ∈ Finset.range (n + 1),
              (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
              (if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0))
              (markovChainMeasure P x) := (hYint (n + 1)).add (hLint n)
          have hB1 : Integrable (fun ω : ℕ → S ↦
              a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ G (ω (n + 1))) ω)
              (markovChainMeasure P x) := (hM1int n).const_mul _
          have hB2 : Integrable (fun ω : ℕ → S ↦
              a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator
                (fun ω ↦ ∫ z, G z ∂P (ω n)) ω) (markovChainMeasure P x) :=
            (hM2int n).const_mul _
          have hB : Integrable (fun ω : ℕ → S ↦
              a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ G (ω (n + 1))) ω -
              a ^ (n + 1) * {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator
                (fun ω ↦ ∫ z, G z ∂P (ω n)) ω) (markovChainMeasure P x) := hB1.sub hB2
          rw [integral_add hA hB, integral_sub hB1 hB2, integral_const_mul, integral_const_mul, hmk]
          ring
  have h0pos : ∀ ω, ((0 : ℕ) : ℕ∞) < τ ω := fun ω ↦
    lt_of_lt_of_le (by norm_num) (hτ1 ω)
  have hbase : ∫ ω, ((∑ t ∈ Finset.range (0 + 1),
          (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
          (if ((0 : ℕ) : ℕ∞) < τ ω then a ^ (0 + 1) * ∫ z, G z ∂P (ω 0) else 0))
          ∂markovChainMeasure P x = f x + a * ∫ z, G z ∂P x := by
    have : (fun ω : ℕ → S ↦ (∑ t ∈ Finset.range (0 + 1),
          (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
          (if ((0 : ℕ) : ℕ∞) < τ ω then a ^ (0 + 1) * ∫ z, G z ∂P (ω 0) else 0)) =
        fun ω ↦ (fun y ↦ f y + a * ∫ z, G z ∂P y) (ω 0) := by
      funext ω
      simp only [zero_add, Finset.sum_range_one, if_pos (h0pos ω), pow_zero, one_mul, pow_one]
    rw [this]
    exact p2mbf_int0 P x (fun y ↦ f y + a * ∫ z, G z ∂P y) Measurable.of_discrete
  have hinv : ∀ n : ℕ, ∫ ω, ((∑ t ∈ Finset.range (n + 1),
          (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) +
          (if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0))
          ∂markovChainMeasure P x ≤ f x + a * ∫ z, G z ∂P x := by
    intro n
    induction n with
    | zero => exact hbase.le
    | succ n ih => exact (hstep n).trans ih
  have hfinal : ∀ n : ℕ, ∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P x ≤
      (f x + a * ∫ z, G z ∂P x) + a ^ (n + 1) * (BG + Bf / (1 - a)) := by
    intro n
    have h1 := hinv n
    rw [integral_add (hYint (n + 1)) (hLint n)] at h1
    have h2 : |∫ ω, (if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0)
        ∂markovChainMeasure P x| ≤ a ^ (n + 1) * BG := by
      refine p2mbf_abs_int_le _ _ _ (fun ω ↦ ?_)
      split_ifs
      · rw [abs_mul, abs_pow, abs_of_nonneg ha0]
        exact mul_le_mul_of_nonneg_left (hPGb _) (pow_nonneg ha0 _)
      · simp only [abs_zero]; exact mul_nonneg (pow_nonneg ha0 _) hBG
    have h3 : |∫ ω, (discountedStoppedSum a f τ ω - ∑ t ∈ Finset.range (n + 1),
        (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) ∂markovChainMeasure P x| ≤
        Bf * a ^ (n + 1) / (1 - a) :=
      p2mbf_abs_int_le _ _ _ (fun ω ↦ p2mbf_tail a ha0 ha1 f Bf hBf hf τ ω (n + 1))
    rw [integral_sub (p2mbf_dss_int P x a ha0 ha1 f Bf hBf hf τ hτ) (hYint (n + 1))] at h3
    have h2' := (abs_le.1 h2).1
    have h3' := (abs_le.1 h3).2
    have e : Bf * a ^ (n + 1) / (1 - a) = a ^ (n + 1) * (Bf / (1 - a)) := by ring
    rw [e] at h3'
    nlinarith
  have hlim0 : Filter.Tendsto (fun n : ℕ ↦ a ^ (n + 1)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).comp (Filter.tendsto_add_atTop_nat 1)
  have hlim := (hlim0.mul_const (BG + Bf / (1 - a))).const_add (f x + a * ∫ z, G z ∂P x)
  rw [zero_mul, add_zero] at hlim
  exact ge_of_tendsto' hlim hfinal


open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2mbf_hit_le {S : Type*} [MeasurableSpace S] (Z : Set S) (ω : ℕ → S) (n : ℕ) :
    hittingTime Z ω ≤ (n : ℕ∞) ↔ ∃ s : ℕ, 1 ≤ s ∧ s ≤ n ∧ ω s ∈ Z := by
  unfold hittingTime
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have hle : ((n + 1 : ℕ) : ℕ∞) ≤ ⨅ t : {t : ℕ // 1 ≤ t ∧ ω t ∈ Z}, ((t : ℕ) : ℕ∞) := by
      refine le_iInf fun t ↦ ?_
      have : n < t.1 := by
        by_contra h'
        push_neg at h'
        exact hne t.1 t.2.1 h' t.2.2
      exact_mod_cast this
    have := hle.trans h
    norm_cast at this
    omega
  · rintro ⟨s, hs1, hsn, hs⟩
    exact (iInf_le (fun t : {t : ℕ // 1 ≤ t ∧ ω t ∈ Z} ↦ ((t : ℕ) : ℕ∞)) ⟨s, hs1, hs⟩).trans
      (by exact_mod_cast hsn)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2mbf_hit_stop {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (Z : Set S) : IsPositiveStoppingTime (hittingTime Z) := by
  refine ⟨fun n ↦ ?_, fun ω ↦ ?_⟩
  · have : {ω : ℕ → S | hittingTime Z ω ≤ (n : ℕ∞)} =
        (fun ω (i : Finset.Iic n) ↦ ω i.1) ⁻¹'
          ⋃ i : Finset.Iic n, {h : (Π _i : Finset.Iic n, S) | 1 ≤ i.1 ∧ h i ∈ Z} := by
      ext ω
      simp only [Set.mem_setOf_eq, p2mbf_hit_le, Set.mem_preimage, Set.mem_iUnion]
      constructor
      · rintro ⟨s, hs1, hsn, hs⟩
        exact ⟨⟨s, Finset.mem_Iic.2 hsn⟩, hs1, hs⟩
      · rintro ⟨⟨s, hs⟩, hs1, hsZ⟩
        exact ⟨s, hs1, Finset.mem_Iic.1 hs, hsZ⟩
    rw [this]
    refine MeasurableSpace.measurableSet_comap.2 ⟨_, ?_, rfl⟩
    refine MeasurableSet.iUnion fun i ↦ ?_
    by_cases hi : 1 ≤ i.1
    · simp only [hi, true_and]
      exact measurable_pi_apply i MeasurableSet.of_discrete
    · simp only [hi, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  · unfold hittingTime
    refine le_iInf fun t ↦ ?_
    exact_mod_cast t.2.1

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2mbf_W1 {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsPositiveStoppingTime τ) (y : S) :
    1 ≤ stoppedTime P a τ y := by
  have := p2mbf_prob P y
  have hr1 : ∀ y, |(fun _ : S ↦ (1 : ℝ)) y| ≤ 1 := fun y ↦ by simp
  have hint := p2mbf_dss_int P y a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ hτ.1
  have hmono := integral_mono (integrable_const (1 : ℝ)) hint (fun ω ↦ by
    have hsum : Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * 1 else 0) :=
      p2mbf_summable a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ ω
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

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices

namespace P2MFC

variable {N : ℕ}

lemma prob (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (x : Fin N) :
    IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

lemma marg0 (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (x : Fin N) :
    (markovChainMeasure P x).map (Preorder.frestrictLe 0) = Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

lemma ext_marg (μ ν : Measure (ℕ → Fin N)) [IsFiniteMeasure ν]
    (h : ∀ a, μ.map (Preorder.frestrictLe a) = ν.map (Preorder.frestrictLe a)) : μ = ν := by
  have hproj : IsProjectiveMeasureFamily (α := fun _ : ℕ ↦ Fin N)
      (fun I : Finset ℕ ↦ ν.map (fun (f : ℕ → Fin N) (i : I) ↦ f i)) := by
    intro I J hJI
    dsimp only
    rw [Measure.map_map (Finset.measurable_restrict₂ _)
      (measurable_pi_lambda _ (fun i ↦ measurable_pi_apply _))]
    rfl
  have h1 : IsProjectiveLimit (α := fun _ : ℕ ↦ Fin N) μ
      (fun I : Finset ℕ ↦ ν.map (fun (f : ℕ → Fin N) (i : I) ↦ f i)) :=
    (isProjectiveLimit_nat_iff hproj μ).2 h
  have h2 : IsProjectiveLimit (α := fun _ : ℕ ↦ Fin N) ν
      (fun I : Finset ℕ ↦ ν.map (fun (f : ℕ → Fin N) (i : I) ↦ f i)) :=
    fun I ↦ rfl
  exact h1.unique h2

/-- cylinder set -/
def cyl (b : ℕ) (w : ℕ → Fin N) : Set (ℕ → Fin N) := {ω | ∀ i ≤ b, ω i = w i}

lemma cyl_eq (b : ℕ) (w : ℕ → Fin N) :
    cyl b w = Preorder.frestrictLe (π := fun _ : ℕ ↦ Fin N) b ⁻¹' {Preorder.frestrictLe b w} := by
  ext ω
  simp only [cyl, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, funext_iff,
    Preorder.frestrictLe_apply, Subtype.forall, Finset.mem_Iic]

lemma measurableSet_cyl (b : ℕ) (w : ℕ → Fin N) : MeasurableSet (cyl b w) := by
  rw [cyl_eq]
  exact Preorder.measurable_frestrictLe b (measurableSet_singleton _)

lemma cyl_formula (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (x : Fin N) (b : ℕ)
    (w : ℕ → Fin N) :
    markovChainMeasure P x (cyl b w) =
      (if w 0 = x then 1 else 0) * ∏ i ∈ range b, P (w i) {w (i + 1)} := by
  haveI := prob P x
  induction b with
  | zero =>
    have hs : MeasurableSet {h : Finset.Iic 0 → Fin N | h ⟨0, by simp⟩ = w 0} :=
      (Set.toFinite _).measurableSet
    have : cyl 0 w = Preorder.frestrictLe 0 ⁻¹' {h : Finset.Iic 0 → Fin N | h ⟨0, by simp⟩ = w 0} := by
      ext ω
      simp [cyl, Preorder.frestrictLe]
    rw [this, ← Measure.map_apply (Preorder.measurable_frestrictLe 0) hs, marg0,
      Measure.dirac_apply' _ hs]
    by_cases hw : w 0 = x
    · simp [Set.indicator, hw]
    · have : x ≠ w 0 := fun h ↦ hw h.symm
      simp [Set.indicator, hw, this]
  | succ b ih =>
    have hA : MeasurableSet {h : Finset.Iic b → Fin N | ∀ i : Finset.Iic b, h i = w i} :=
      (Set.toFinite _).measurableSet
    have hset : cyl (b + 1) w = (fun ω ↦ (Preorder.frestrictLe b ω, ω (b + 1))) ⁻¹'
        ({h : Finset.Iic b → Fin N | ∀ i : Finset.Iic b, h i = w i} ×ˢ {w (b + 1)}) := by
      ext ω
      simp only [cyl, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
        Preorder.frestrictLe_apply, Subtype.forall, Finset.mem_Iic]
      constructor
      · intro h
        exact ⟨fun i hi ↦ h i (by omega), h (b + 1) le_rfl⟩
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_or_ge i (b + 1) with h | h
        · exact h1 i (by omega)
        · have : i = b + 1 := by omega
          subst this; exact h2
    have hF1 : (markovChainMeasure P x).map (Preorder.frestrictLe b) ⊗ₘ markovChainStep P b =
        (markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe b ω, ω (b + 1))) :=
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    rw [hset, ← Measure.map_apply (by fun_prop) (hA.prod (measurableSet_singleton _)), ← hF1,
      Measure.compProd_apply_prod hA (measurableSet_singleton _)]
    have hc : ∀ h ∈ {h : Finset.Iic b → Fin N | ∀ i : Finset.Iic b, h i = w i},
        markovChainStep P b h {w (b + 1)} = P (w b) {w (b + 1)} := by
      intro h hh
      simp only [markovChainStep, Kernel.comap_apply]
      rw [hh ⟨b, Finset.mem_Iic.2 le_rfl⟩]
    rw [setLIntegral_congr_fun hA hc, setLIntegral_const,
      Measure.map_apply (Preorder.measurable_frestrictLe b) hA]
    have : Preorder.frestrictLe b ⁻¹' {h : Finset.Iic b → Fin N | ∀ i : Finset.Iic b, h i = w i}
        = cyl b w := by
      ext ω
      simp [cyl, Preorder.frestrictLe]
    rw [this, ih, prod_range_succ]
    ring

lemma ae_zero (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (x : Fin N) :
    ∀ᵐ ω ∂markovChainMeasure P x, ω 0 = x := by
  rw [ae_iff]
  have hs : MeasurableSet {h : Finset.Iic 0 → Fin N | ¬ h ⟨0, by simp⟩ = x} :=
    (Set.toFinite _).measurableSet
  have : {ω : ℕ → Fin N | ¬ ω 0 = x} =
      Preorder.frestrictLe 0 ⁻¹' {h : Finset.Iic 0 → Fin N | ¬ h ⟨0, by simp⟩ = x} := by
    ext ω; simp [Preorder.frestrictLe]
  rw [this, ← Measure.map_apply (Preorder.measurable_frestrictLe 0) hs, marg0,
    Measure.dirac_apply' _ hs]
  simp [Set.indicator]

/-- the shift -/
def shift (ω : ℕ → Fin N) : ℕ → Fin N := fun n ↦ ω (n + 1)

lemma measurable_shift : Measurable (shift (N := N)) :=
  measurable_pi_lambda _ (fun n ↦ measurable_pi_apply (n + 1))

lemma shift_law (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (x : Fin N) :
    (markovChainMeasure P x).map shift = ∑ y, P x {y} • markovChainMeasure P y := by
  haveI := prob P x
  refine (ext_marg _ _ (fun b ↦ ?_)).symm
  refine Measure.ext_iff_singleton.2 (fun h ↦ ?_)
  let w : ℕ → Fin N := fun i ↦ if hi : i ≤ b then h ⟨i, Finset.mem_Iic.2 hi⟩ else x
  have hw : Preorder.frestrictLe b w = h := by
    funext i
    simp [w, Preorder.frestrictLe, Finset.mem_Iic.1 i.2]
  have hpre : Preorder.frestrictLe (π := fun _ : ℕ ↦ Fin N) b ⁻¹' {h} = cyl b w := by
    rw [cyl_eq, hw]
  rw [Measure.map_apply (Preorder.measurable_frestrictLe b) (measurableSet_singleton _),
    Measure.map_apply (Preorder.measurable_frestrictLe b) (measurableSet_singleton _), hpre,
    Measure.map_apply measurable_shift (measurableSet_cyl b w)]
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, cyl_formula]
  let w' : ℕ → Fin N := fun i ↦ match i with
    | 0 => x
    | i + 1 => w i
  have hinter : cyl (b + 1) w' = shift ⁻¹' cyl b w ∩ {ω | ω 0 = x} := by
    ext ω
    simp only [cyl, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, shift]
    constructor
    · intro hω
      exact ⟨fun i hi ↦ hω (i + 1) (by omega), hω 0 (by omega)⟩
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | zero => exact h2
      | succ i => exact h1 i (by omega)
  have hnull : markovChainMeasure P x {ω | ω 0 = x}ᶜ = 0 := by
    have := ae_zero P x
    rw [ae_iff] at this
    exact this
  have hL : markovChainMeasure P x (shift ⁻¹' cyl b w) = markovChainMeasure P x (cyl (b + 1) w') := by
    rw [hinter, measure_inter_conull hnull]
  rw [hL, cyl_formula, prod_range_succ']
  simp [w', mul_ite, Finset.sum_ite_eq]
  ring

lemma shift_integral (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (x : Fin N)
    (F : (ℕ → Fin N) → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F (shift ω) ∂markovChainMeasure P x = ∑ y, (P x).real {y} * ∫ ω, F ω ∂markovChainMeasure P y := by
  rw [← integral_map measurable_shift.aemeasurable hF.aestronglyMeasurable, shift_law,
    integral_finsetSum_measure]
  · simp [integral_smul_measure, measureReal_def]
  · intro y _
    haveI := prob P y
    exact (Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ fun ω ↦ by
      simpa [Real.norm_eq_abs] using hC ω)).smul_measure (measure_ne_top _ _)

/-! ### hitting times -/

lemma hit_eq_nat (s : Set (Fin N)) (ω : ℕ → Fin N) (m : ℕ) (hm : 1 ≤ m) (hs : ω m ∈ s)
    (hlt : ∀ t, 1 ≤ t → t < m → ω t ∉ s) : hittingTime s ω = m := by
  unfold hittingTime
  apply le_antisymm
  · exact iInf_le_of_le ⟨m, hm, hs⟩ le_rfl
  · refine le_iInf fun t ↦ ?_
    have : m ≤ (t : ℕ) := by
      by_contra hc
      push_neg at hc
      exact hlt t t.2.1 hc t.2.2
    exact_mod_cast this

lemma hit_eq_top (s : Set (Fin N)) (ω : ℕ → Fin N) (h : ∀ t, 1 ≤ t → ω t ∉ s) :
    hittingTime s ω = ⊤ := by
  unfold hittingTime
  haveI : IsEmpty {t : ℕ // 1 ≤ t ∧ ω t ∈ s} := ⟨fun t ↦ h t t.2.1 t.2.2⟩
  exact iInf_of_empty _

lemma hit_eq_nat_iff (s : Set (Fin N)) (ω : ℕ → Fin N) (m : ℕ) :
    hittingTime s ω = m ↔ (1 ≤ m ∧ ω m ∈ s ∧ ∀ t, 1 ≤ t → t < m → ω t ∉ s) := by
  classical
  constructor
  · intro hT
    by_cases hex : ∃ t, 1 ≤ t ∧ ω t ∈ s
    · have ht0 := Nat.find_spec hex
      have hmin : ∀ t, 1 ≤ t → t < Nat.find hex → ω t ∉ s :=
        fun t h1 h2 hs ↦ Nat.find_min hex h2 ⟨h1, hs⟩
      have h0 := hit_eq_nat s ω (Nat.find hex) ht0.1 ht0.2 hmin
      rw [h0] at hT
      have hm : Nat.find hex = m := by exact_mod_cast hT
      rw [← hm]
      exact ⟨ht0.1, ht0.2, hmin⟩
    · push_neg at hex
      rw [hit_eq_top s ω hex] at hT
      simp at hT
  · rintro ⟨h1, h2, h3⟩
    exact hit_eq_nat s ω m h1 h2 h3

lemma measurable_hit (s : Set (Fin N)) : Measurable (hittingTime s) := by
  rw [ENat.measurable_iff]
  intro m
  have : hittingTime s ⁻¹' {(m : ℕ∞)} =
      {ω | 1 ≤ m ∧ ω m ∈ s ∧ ∀ t, 1 ≤ t → t < m → ω t ∉ s} := by
    ext ω
    exact hit_eq_nat_iff s ω m
  rw [this]
  have hc : ∀ t, Measurable (fun ω : ℕ → Fin N ↦ ω t ∈ s) := fun t ↦
    measurableSet_setOf.1 (measurable_pi_apply t (Set.toFinite s).measurableSet)
  exact measurableSet_setOf.2 (measurable_const.and ((hc m).and
    (Measurable.forall fun t ↦ measurable_const.imp (measurable_const.imp (hc t).not))))

/-- discount function -/
noncomputable def dfun (a : ℝ) (e : ℕ∞) : ℝ := match e with
  | (n : ℕ) => a ^ n
  | ⊤ => 0

lemma dfun_coe (a : ℝ) (n : ℕ) : dfun a n = a ^ n := rfl
lemma dfun_top (a : ℝ) : dfun a ⊤ = 0 := rfl

lemma discountAtStop_eq (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ)
    (τ : (ℕ → Fin N) → ℕ∞) (x : Fin N) :
    AllocationIndices.discountAtStop P a τ x = ∫ ω, dfun a (τ ω) ∂markovChainMeasure P x := rfl

lemma measurable_D (a : ℝ) (s : Set (Fin N)) :
    Measurable (fun ω : ℕ → Fin N ↦ dfun a (hittingTime s ω)) :=
  (measurable_of_countable (dfun a)).comp (measurable_hit s)

lemma D_bounds (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (s : Set (Fin N)) (ω : ℕ → Fin N) :
    0 ≤ dfun a (hittingTime s ω) ∧ dfun a (hittingTime s ω) ≤ a := by
  generalize hT : hittingTime s ω = e
  induction e using ENat.recTopCoe with
  | top => exact ⟨le_rfl, ha0⟩
  | coe m =>
    have hm := ((hit_eq_nat_iff s ω m).1 hT).1
    rw [dfun_coe]
    exact ⟨pow_nonneg ha0 m, pow_le_of_le_one ha0 ha1 (by omega)⟩

lemma D_step (a : ℝ) (S : Finset (Fin N)) (ω : ℕ → Fin N) :
    dfun a (hittingTime (↑S : Set (Fin N)) ω) =
      a * (if shift ω 0 ∈ S then 1 else dfun a (hittingTime (↑S : Set (Fin N)) (shift ω))) := by
  classical
  by_cases h1 : ω 1 ∈ S
  · have : hittingTime (↑S : Set (Fin N)) ω = ((1 : ℕ) : ℕ∞) :=
      hit_eq_nat _ ω 1 le_rfl (Finset.mem_coe.2 h1) (fun t h1 h2 ↦ by omega)
    have h1' : shift ω 0 ∈ S := h1
    rw [this, dfun_coe, if_pos h1']
    ring
  · have hs0 : ¬ shift ω 0 ∈ S := h1
    rw [if_neg hs0]
    by_cases hex : ∃ t, 1 ≤ t ∧ ω (t + 1) ∈ S
    · have hm := Nat.find_spec hex
      have hmin : ∀ t, 1 ≤ t → t < Nat.find hex → ω (t + 1) ∉ S :=
        fun t h1 h2 hs ↦ Nat.find_min hex h2 ⟨h1, hs⟩
      have e1 : hittingTime (↑S : Set (Fin N)) (shift ω) = (Nat.find hex : ℕ) :=
        hit_eq_nat _ _ _ hm.1 (by
            show ω (Nat.find hex + 1) ∈ (↑S : Set (Fin N)); exact Finset.mem_coe.2 hm.2)
          (fun t ht1 ht2 ↦ by
            show ω (t + 1) ∉ (↑S : Set (Fin N))
            exact fun h ↦ hmin t ht1 ht2 (Finset.mem_coe.1 h))
      have e2 : hittingTime (↑S : Set (Fin N)) ω = ((Nat.find hex + 1 : ℕ) : ℕ∞) := by
        refine hit_eq_nat _ ω _ (by omega) (Finset.mem_coe.2 hm.2) (fun t ht1 ht2 ↦ ?_)
        rcases Nat.lt_or_ge t 2 with h | h
        · have : t = 1 := by omega
          subst this
          exact fun h ↦ h1 (Finset.mem_coe.1 h)
        · have := hmin (t - 1) (by omega) (by omega)
          rw [show t - 1 + 1 = t by omega] at this
          exact fun h ↦ this (Finset.mem_coe.1 h)
      rw [e1, e2, dfun_coe, dfun_coe, pow_succ]
      ring
    · push_neg at hex
      have e1 : hittingTime (↑S : Set (Fin N)) (shift ω) = ⊤ :=
        hit_eq_top _ _ (fun t ht h ↦ hex t ht (Finset.mem_coe.1 h))
      have e2 : hittingTime (↑S : Set (Fin N)) ω = ⊤ := by
        refine hit_eq_top _ _ (fun t ht ↦ ?_)
        rcases Nat.lt_or_ge t 2 with h | h
        · have : t = 1 := by omega
          subst this
          exact fun h ↦ h1 (Finset.mem_coe.1 h)
        · have := hex (t - 1) (by omega)
          rw [show t - 1 + 1 = t by omega] at this
          exact fun h ↦ this (Finset.mem_coe.1 h)
      rw [e1, e2, dfun_top, mul_zero]

lemma dss_eq (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (e : ℕ∞) :
    (∑' t : ℕ, if (t : ℕ∞) < e then a ^ t * 1 else 0) = (1 - dfun a e) / (1 - a) := by
  have h1a : (1 - a) ≠ 0 := by linarith
  induction e using ENat.recTopCoe with
  | top =>
    simp only [ENat.natCast_lt_top, if_true, mul_one, dfun_top, sub_zero]
    rw [tsum_geometric_of_lt_one ha0 ha1, one_div]
  | coe m =>
    rw [tsum_eq_sum (s := range m) (fun t ht ↦ by
      have : ¬ t < m := by simpa using ht
      simp [this])]
    rw [Finset.sum_congr rfl (fun t ht ↦ by
      have : t < m := Finset.mem_range.1 ht
      simp [this] : ∀ t ∈ range m, (if (t : ℕ∞) < (m : ℕ∞) then a ^ t * 1 else 0) = a ^ t)]
    have ha1' : a - 1 ≠ 0 := by linarith
    rw [geom_sum_eq (ne_of_lt ha1), dfun_coe, div_eq_div_iff ha1' h1a]
    ring

lemma D_integrable (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (s : Set (Fin N)) (x : Fin N) :
    Integrable (fun ω ↦ dfun a (hittingTime s ω)) (markovChainMeasure P x) := by
  haveI := prob P x
  refine Integrable.of_bound (measurable_D a s).aestronglyMeasurable a (ae_of_all _ fun ω ↦ ?_)
  have := D_bounds a ha0 ha1 s ω
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]
  exact this.2

lemma g_bounds (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (s : Set (Fin N)) (x : Fin N) :
    0 ≤ AllocationIndices.discountAtStop P a (hittingTime s) x ∧
      AllocationIndices.discountAtStop P a (hittingTime s) x ≤ a := by
  haveI := prob P x
  rw [discountAtStop_eq]
  refine ⟨integral_nonneg fun ω ↦ (D_bounds a ha0 ha1 s ω).1, ?_⟩
  calc ∫ ω, dfun a (hittingTime s ω) ∂markovChainMeasure P x
      ≤ ∫ _ω, a ∂markovChainMeasure P x :=
        integral_mono (D_integrable P a ha0 ha1 s x) (integrable_const a)
          (fun ω ↦ (D_bounds a ha0 ha1 s ω).2)
    _ = a := by simp

lemma stoppedTime_eq (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (s : Set (Fin N)) (x : Fin N) :
    AllocationIndices.stoppedTime P a (hittingTime s) x =
      (1 - AllocationIndices.discountAtStop P a (hittingTime s) x) / (1 - a) := by
  haveI := prob P x
  have hpt : ∀ ω, discountedStoppedSum a (fun _ ↦ (1 : ℝ)) (hittingTime s) ω =
      (1 - dfun a (hittingTime s ω)) / (1 - a) := by
    intro ω
    unfold discountedStoppedSum
    exact dss_eq a ha0 ha1 _
  unfold AllocationIndices.stoppedTime
  simp_rw [hpt]
  rw [discountAtStop_eq, integral_div, integral_sub (integrable_const 1)
    (D_integrable P a ha0 ha1.le s x)]
  simp

lemma first_step (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (S : Finset (Fin N)) (x : Fin N) :
    AllocationIndices.discountAtStop P a (hittingTime (↑S : Set (Fin N))) x =
      a * ∑ y, (P x).real {y} * (if y ∈ S then 1 else
        AllocationIndices.discountAtStop P a (hittingTime (↑S : Set (Fin N))) y) := by
  let Φ : (ℕ → Fin N) → ℝ := fun ω ↦
    if ω 0 ∈ S then 1 else dfun a (hittingTime (↑S : Set (Fin N)) ω)
  have hΦm : Measurable Φ :=
    Measurable.ite (measurable_pi_apply 0 (Set.toFinite (↑S : Set (Fin N))).measurableSet)
      measurable_const (measurable_D a _)
  have hΦb : ∀ ω, |Φ ω| ≤ 1 := by
    intro ω
    simp only [Φ]
    split_ifs
    · simp
    · have := D_bounds a ha0 ha1 (↑S : Set (Fin N)) ω
      rw [abs_of_nonneg this.1]
      linarith [this.2]
  rw [discountAtStop_eq]
  have hstep : ∫ ω, dfun a (hittingTime (↑S : Set (Fin N)) ω) ∂markovChainMeasure P x =
      ∫ ω, a * Φ (shift ω) ∂markovChainMeasure P x :=
    integral_congr_ae (ae_of_all _ fun ω ↦ D_step a S ω)
  rw [hstep, integral_const_mul, shift_integral P x Φ hΦm 1 hΦb]
  congr 1
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  congr 1
  haveI := prob P y
  have : ∫ ω, Φ ω ∂markovChainMeasure P y = ∫ ω, (if y ∈ S then 1 else
      dfun a (hittingTime (↑S : Set (Fin N)) ω)) ∂markovChainMeasure P y :=
    integral_congr_ae ((ae_zero P y).mono fun ω hω ↦ by simp only [Φ, hω])
  rw [this]
  split_ifs with hy
  · simp
  · rfl

lemma real_sum_one {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
    (ν : Measure α) [IsProbabilityMeasure ν] : ∑ j, ν.real {j} = 1 := by
  have := integral_fintype (μ := ν) (f := fun _ ↦ (1 : ℝ)) Integrable.of_finite
  simpa using this.symm

end P2MFC

namespace P2M965

variable {N : ℕ}

lemma mem_lowSet (σ : Equiv.Perm (Fin N)) (m : ℕ) (i : Fin N) :
    i ∈ lowSet σ m ↔ ((σ.symm i : Fin N) : ℕ) < m := by
  unfold lowSet
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using hj
  · intro h
    exact ⟨σ.symm i, h, by simp⟩

lemma abs_le_sum (g : Fin N → ℝ) (z : Fin N) : |g z| ≤ ∑ w, |g w| :=
  Finset.single_le_sum (f := fun w ↦ |g w|) (fun w _ ↦ abs_nonneg _) (Finset.mem_univ z)

lemma int_fin (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (z : Fin N) (g : Fin N → ℝ) :
    ∫ w, g w ∂P z = ∑ w, (P z).real {w} * g w := by
  rw [integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul]

noncomputable def Wt (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ)
    (T : Finset (Fin N)) (z : Fin N) : ℝ :=
  stoppedTime P a (hittingTime (↑T : Set (Fin N))) z

noncomputable def hf (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ)
    (T : Finset (Fin N)) (z : Fin N) : ℝ :=
  if z ∈ T then 0 else Wt P a T z

lemma A_eq (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ)
    (T : Finset (Fin N)) (z : Fin N) :
    conservationCoeff P a T z = if z ∈ T then Wt P a T z else 0 := rfl

lemma A_add (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ)
    (T : Finset (Fin N)) (z : Fin N) :
    conservationCoeff P a T z + hf P a T z = Wt P a T z := by
  rw [A_eq]
  unfold hf
  split_ifs <;> simp

lemma Wt_ge (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (T : Finset (Fin N)) (z : Fin N) : 1 ≤ Wt P a T z := by
  unfold Wt
  rw [P2MFC.stoppedTime_eq P a ha0 ha1]
  have hg := P2MFC.g_bounds P a ha0 ha1.le (↑T : Set (Fin N)) z
  rw [le_div_iff₀ (by linarith)]
  linarith [hg.2]

lemma Wt_step (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (T : Finset (Fin N)) (z : Fin N) :
    Wt P a T z = 1 + a * ∫ w, hf P a T w ∂P z := by
  rw [int_fin]
  unfold hf Wt
  simp_rw [P2MFC.stoppedTime_eq P a ha0 ha1]
  rw [P2MFC.first_step P a ha0 ha1.le T z]
  have h1a : (1 - a) ≠ 0 := by linarith
  have hs := P2MFC.real_sum_one (P z)
  have hpt : ∀ w, (P z).real {w} * (if w ∈ T then 0 else
      (1 - discountAtStop P a (hittingTime (↑T : Set (Fin N))) w) / (1 - a)) =
      ((P z).real {w} - (P z).real {w} * (if w ∈ T then 1 else
        discountAtStop P a (hittingTime (↑T : Set (Fin N))) w)) / (1 - a) := by
    intro w
    split_ifs
    · field_simp; ring
    · field_simp
  rw [Finset.sum_congr rfl (fun w _ ↦ hpt w), ← Finset.sum_div, Finset.sum_sub_distrib, hs]
  field_simp
  ring

lemma filter_split (k k' : Fin N) (hk : (k' : ℕ) = k + 1) (g : Fin N → ℝ) :
    ∑ j ∈ univ.filter (fun j : Fin N ↦ k < j), g j =
      g k' + ∑ j ∈ univ.filter (fun j : Fin N ↦ k' < j), g j := by
  have : univ.filter (fun j : Fin N ↦ k < j) =
      insert k' (univ.filter (fun j : Fin N ↦ k' < j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def,
      Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp)]

lemma y_nonpos {A : Finset (Fin N) → Fin N → ℝ} (hApos : ∀ T i, i ∈ T → 0 < A T i)
    {r : Fin N → ℝ} {σ : Equiv.Perm (Fin N)} {y : Fin N → ℝ}
    (h : IsAdaptiveGreedy A r σ y) (k : Fin N) (hk : (k : ℕ) + 1 < N) : y k ≤ 0 := by
  have hmem : σ k ∈ lowSet σ ((k : ℕ) + 1) := by
    rw [mem_lowSet]; simp
  have hmem' : σ k ∈ lowSet σ (((⟨(k : ℕ) + 1, hk⟩ : Fin N) : ℕ) + 1) := by
    rw [mem_lowSet]; simp
  have h1 := (h ⟨(k : ℕ) + 1, hk⟩).1 (σ k) hmem'
  have h2 := (h k).2
  have hA1 := hApos _ _ hmem
  have hA2 := hApos _ _ hmem'
  unfold greedyNumerator at h1 h2
  rw [filter_split k ⟨(k : ℕ) + 1, hk⟩ rfl] at h2
  rw [div_le_iff₀ hA2] at h1
  rw [div_eq_iff hA1.ne'] at h2
  have hneg : y k * A (lowSet σ ((k : ℕ) + 1)) (σ k) ≤ 0 := by linarith
  by_contra hc
  push_neg at hc
  have := mul_pos hc hA1
  linarith

lemma r_decomp {A : Finset (Fin N) → Fin N → ℝ} (hA0 : ∀ T i, i ∉ T → A T i = 0)
    (hApos : ∀ T i, i ∈ T → 0 < A T i)
    {r : Fin N → ℝ} {σ : Equiv.Perm (Fin N)} {y : Fin N → ℝ}
    (h : IsAdaptiveGreedy A r σ y) (i : Fin N) :
    r i = ∑ j, y j * A (lowSet σ ((j : ℕ) + 1)) i := by
  obtain ⟨k, hk⟩ : ∃ k, σ.symm i = k := ⟨_, rfl⟩
  have hi : σ k = i := by rw [← hk]; simp
  have hmem : i ∈ lowSet σ ((k : ℕ) + 1) := by rw [mem_lowSet, hk]; omega
  have h2 := (h k).2
  rw [hi] at h2
  unfold greedyNumerator at h2
  rw [div_eq_iff (hApos _ _ hmem).ne'] at h2
  have hsplit : ∑ j, y j * A (lowSet σ ((j : ℕ) + 1)) i =
      ∑ j, ((if k < j then A (lowSet σ ((j : ℕ) + 1)) i * y j else 0) +
        (if j = k then y k * A (lowSet σ ((k : ℕ) + 1)) i else 0)) := by
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    by_cases hkj : k < j
    · have hne : j ≠ k := (ne_of_lt hkj).symm
      rw [if_pos hkj, if_neg hne]
      ring
    · by_cases hjk : j = k
      · subst hjk
        simp
      · have hlt : j < k := lt_of_le_of_ne (not_lt.1 hkj) hjk
        have hn : i ∉ lowSet σ ((j : ℕ) + 1) := by
          rw [mem_lowSet, hk]
          rw [Fin.lt_def] at hlt
          omega
        rw [if_neg hkj, if_neg hjk, hA0 _ _ hn]
        ring
  rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_filter]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linarith

lemma hit_not_mem (Z : Set (Fin N)) (ω : ℕ → Fin N) (t : ℕ) (h1 : 1 ≤ t)
    (h : (t : ℕ∞) < hittingTime Z ω) : ω t ∉ Z := by
  intro hz
  have := iInf_le (fun t : {t : ℕ // 1 ≤ t ∧ ω t ∈ Z} ↦ ((t : ℕ) : ℕ∞)) ⟨t, h1, hz⟩
  unfold hittingTime at h
  exact lt_irrefl _ (lt_of_lt_of_le h this)

lemma hit_mem (Z : Set (Fin N)) (ω : ℕ → Fin N) (n : ℕ)
    (h0 : (n : ℕ∞) < hittingTime Z ω) (h1 : ¬ ((n + 1 : ℕ) : ℕ∞) < hittingTime Z ω) :
    ω (n + 1) ∈ Z := by
  obtain ⟨s, hs1, hsn, hs⟩ := (p2mbf_hit_le Z ω (n + 1)).1 (not_lt.1 h1)
  rcases Nat.lt_or_ge s (n + 1) with hlt | hge
  · exfalso
    have := (p2mbf_hit_le Z ω n).2 ⟨s, hs1, by omega, hs⟩
    exact absurd h0 (not_lt.2 this)
  · have : s = n + 1 := by omega
    subst this
    exact hs

noncomputable def Gf (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ)
    (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ) (k0 : Fin N) (z : Fin N) : ℝ :=
  ∑ l, if k0 ≤ l then -(y l * hf P a (lowSet σ ((l : ℕ) + 1)) z) else 0

noncomputable def Ef (P : Kernel (Fin N) (Fin N)) [IsMarkovKernel P] (a : ℝ)
    (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ) (k0 : Fin N) (z : Fin N) : ℝ :=
  ∑ l, if l < k0 then y l * conservationCoeff P a (lowSet σ ((l : ℕ) + 1)) z else 0

lemma dss_lin (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (r : Fin N → ℝ) (c : ℝ)
    (τ : (ℕ → Fin N) → ℕ∞) (ω : ℕ → Fin N) :
    discountedStoppedSum a (fun z ↦ r z - c) τ ω =
      discountedStoppedSum a r τ ω - c * discountedStoppedSum a (fun _ ↦ 1) τ ω := by
  have hs1 := p2mbf_summable a ha0 ha1 r (∑ w, |r w|)
    (Finset.sum_nonneg (fun w _ ↦ abs_nonneg _)) (abs_le_sum r) τ ω
  have hs2 := p2mbf_summable a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one (fun _ ↦ by simp) τ ω
  unfold discountedStoppedSum
  rw [← tsum_mul_left, ← hs1.tsum_sub (hs2.mul_left c)]
  refine tsum_congr (fun t ↦ ?_)
  split_ifs <;> ring

end P2M965

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset AllocationIndices in
theorem solution {N : ℕ} (P : Kernel (Fin N) (Fin N))
    [IsMarkovKernel P] (r : Fin N → ℝ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (σ : Equiv.Perm (Fin N)) (y : Fin N → ℝ) (h : IsAdaptiveGreedy (conservationCoeff P a) r σ y) :
    (∀ j k : Fin N, j ≤ k → greedyIndex σ y (σ j) ≤ greedyIndex σ y (σ k)) ∧
    ∀ i, greedyIndex σ y i = gittinsIndex P r a i := by
  have hApos : ∀ T i, i ∈ T → 0 < conservationCoeff P a T i := fun T i hi ↦ by
    rw [P2M965.A_eq, if_pos hi]
    linarith [P2M965.Wt_ge P a ha0.le ha1 T i]
  have hA0 : ∀ T i, i ∉ T → conservationCoeff P a T i = 0 := fun T i hi ↦ by
    rw [P2M965.A_eq, if_neg hi]
  have hAnn : ∀ T i, 0 ≤ conservationCoeff P a T i := fun T i ↦ by
    by_cases hi : i ∈ T
    · exact (hApos T i hi).le
    · rw [hA0 T i hi]
  have hy : ∀ k : Fin N, (k : ℕ) + 1 < N → y k ≤ 0 := fun k hk ↦ P2M965.y_nonpos hApos h k hk
  have hgi : ∀ i, greedyIndex σ y i = ∑ l, if σ.symm i ≤ l then y l else 0 := fun i ↦ by
    unfold greedyIndex
    rw [Finset.sum_filter]
  refine ⟨fun j k hjk ↦ ?_, fun x ↦ ?_⟩
  · rw [hgi, hgi, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    refine Finset.sum_le_sum (fun l _ ↦ ?_)
    by_cases hkl : k ≤ l
    · rw [if_pos hkl, if_pos (le_trans hjk hkl)]
    · rw [if_neg hkl]
      split_ifs
      · refine hy l ?_
        have := k.2
        rw [not_le, Fin.lt_def] at hkl
        omega
      · exact le_rfl
  · obtain ⟨k0, hk0⟩ : ∃ k0, σ.symm x = k0 := ⟨_, rfl⟩
    have := p2mbf_prob P x
    let f : Fin N → ℝ := fun z ↦ r z - greedyIndex σ y x
    let G : Fin N → ℝ := P2M965.Gf P a σ y k0
    let E : Fin N → ℝ := P2M965.Ef P a σ y k0
    have hK : ∀ z, f z + a * ∫ w, G w ∂P z = G z + E z := by
      intro z
      have hstep : ∀ l : Fin N, a * ∫ w, P2M965.hf P a (lowSet σ ((l : ℕ) + 1)) w ∂P z =
          P2M965.Wt P a (lowSet σ ((l : ℕ) + 1)) z - 1 := fun l ↦ by
        rw [P2M965.Wt_step P a ha0.le ha1]
        ring
      have hint : ∫ w, G w ∂P z = ∑ l, if k0 ≤ l then
          -(y l * ∫ w, P2M965.hf P a (lowSet σ ((l : ℕ) + 1)) w ∂P z) else 0 := by
        simp only [G, P2M965.Gf]
        rw [integral_finsetSum _ (fun l _ ↦ Integrable.of_finite)]
        refine Finset.sum_congr rfl (fun l _ ↦ ?_)
        split_ifs
        · rw [integral_neg, integral_const_mul]
        · simp
      have hterm : ∀ l : Fin N,
          y l * conservationCoeff P a (lowSet σ ((l : ℕ) + 1)) z - (if k0 ≤ l then y l else 0) +
            a * (if k0 ≤ l then
              -(y l * ∫ w, P2M965.hf P a (lowSet σ ((l : ℕ) + 1)) w ∂P z) else 0) =
          (if k0 ≤ l then -(y l * P2M965.hf P a (lowSet σ ((l : ℕ) + 1)) z) else 0) +
            (if l < k0 then y l * conservationCoeff P a (lowSet σ ((l : ℕ) + 1)) z else 0) := by
        intro l
        by_cases hl : k0 ≤ l
        · have hlt : ¬ l < k0 := not_lt.2 hl
          rw [if_pos hl, if_pos hl, if_pos hl, if_neg hlt]
          have e1 := hstep l
          have e2 := P2M965.A_add P a (lowSet σ ((l : ℕ) + 1)) z
          have eA : conservationCoeff P a (lowSet σ ((l : ℕ) + 1)) z =
              P2M965.Wt P a (lowSet σ ((l : ℕ) + 1)) z -
                P2M965.hf P a (lowSet σ ((l : ℕ) + 1)) z := by linarith
          have e3 : a * -(y l * ∫ w, P2M965.hf P a (lowSet σ ((l : ℕ) + 1)) w ∂P z) =
              -(y l * (a * ∫ w, P2M965.hf P a (lowSet σ ((l : ℕ) + 1)) w ∂P z)) := by ring
          rw [e3, e1, eA]
          ring
        · rw [if_neg hl, if_neg hl, if_neg hl, if_pos (lt_of_not_ge hl)]
          ring
      calc f z + a * ∫ w, G w ∂P z
          = ∑ l, (y l * conservationCoeff P a (lowSet σ ((l : ℕ) + 1)) z -
              (if k0 ≤ l then y l else 0) + a * (if k0 ≤ l then
                -(y l * ∫ w, P2M965.hf P a (lowSet σ ((l : ℕ) + 1)) w ∂P z) else 0)) := by
            simp only [f]
            rw [hint, P2M965.r_decomp hA0 hApos h z, hgi x, hk0, Finset.mul_sum,
              ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        _ = ∑ l, ((if k0 ≤ l then -(y l * P2M965.hf P a (lowSet σ ((l : ℕ) + 1)) z) else 0) +
            (if l < k0 then y l * conservationCoeff P a (lowSet σ ((l : ℕ) + 1)) z else 0)) :=
            Finset.sum_congr rfl (fun l _ ↦ hterm l)
        _ = G z + E z := by
            rw [Finset.sum_add_distrib]
            rfl
    have hG0 : ∀ z, 0 ≤ G z := by
      intro z
      refine Finset.sum_nonneg (fun l _ ↦ ?_)
      split_ifs
      · by_cases hz : z ∈ lowSet σ ((l : ℕ) + 1)
        · unfold P2M965.hf
          rw [if_pos hz]
          simp
        · have hW := P2M965.Wt_ge P a ha0.le ha1 (lowSet σ ((l : ℕ) + 1)) z
          have hyl : y l ≤ 0 := by
            refine hy l ?_
            rw [P2M965.mem_lowSet] at hz
            have := (σ.symm z).2
            omega
          unfold P2M965.hf
          rw [if_neg hz]
          nlinarith
      · exact le_rfl
    have hE0 : ∀ z, E z ≤ 0 := by
      intro z
      refine Finset.sum_nonpos (fun l _ ↦ ?_)
      split_ifs with hl
      · have hyl : y l ≤ 0 := by
          refine hy l ?_
          have := k0.2
          rw [Fin.lt_def] at hl
          omega
        nlinarith [hAnn (lowSet σ ((l : ℕ) + 1)) z]
      · exact le_rfl
    have hGlow : ∀ z, ((σ.symm z : Fin N) : ℕ) ≤ k0 → G z = 0 := by
      intro z hz
      refine Finset.sum_eq_zero (fun l _ ↦ ?_)
      split_ifs with hl
      · have hm : z ∈ lowSet σ ((l : ℕ) + 1) := by
          rw [P2M965.mem_lowSet]
          rw [Fin.le_def] at hl
          omega
        unfold P2M965.hf
        rw [if_pos hm]
        simp
      · rfl
    have hEhigh : ∀ z, ¬ ((σ.symm z : Fin N) : ℕ) < k0 → E z = 0 := by
      intro z hz
      refine Finset.sum_eq_zero (fun l _ ↦ ?_)
      split_ifs with hl
      · have hn : z ∉ lowSet σ ((l : ℕ) + 1) := by
          rw [P2M965.mem_lowSet]
          rw [Fin.lt_def] at hl
          omega
        rw [hA0 _ _ hn, mul_zero]
      · rfl
    have hKx : f x + a * ∫ w, G w ∂P x = 0 := by
      rw [hK, hGlow x (by rw [hk0]), hEhigh x (by rw [hk0]; exact lt_irrefl _)]
      ring
    have hBf : 0 ≤ ∑ w, |f w| := Finset.sum_nonneg (fun w _ ↦ abs_nonneg _)
    have hfb : ∀ z, |f z| ≤ ∑ w, |f w| := P2M965.abs_le_sum f
    have hGb : ∀ z, |G z| ≤ ∑ w, |G w| := P2M965.abs_le_sum G
    have hBr : 0 ≤ ∑ w, |r w| := Finset.sum_nonneg (fun w _ ↦ abs_nonneg _)
    have hrb : ∀ z, |r z| ≤ ∑ w, |r w| := P2M965.abs_le_sum r
    -- the stopped value of `f` is `R - ν W`
    have hbase : ∀ τ : (ℕ → Fin N) → ℕ∞, IsTrajStoppingTime τ →
        ∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P x =
          (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P x) - greedyIndex σ y x *
            (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x) := by
      intro τ hτ
      have h1 := p2mbf_dss_int P x a ha0.le ha1 r _ hBr hrb τ hτ
      have h2 := p2mbf_dss_int P x a ha0.le ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one
        (fun _ ↦ by simp) τ hτ
      have : (fun ω ↦ discountedStoppedSum a f τ ω) = fun ω ↦
          discountedStoppedSum a r τ ω -
            greedyIndex σ y x * discountedStoppedSum a (fun _ ↦ 1) τ ω := by
        funext ω
        exact P2M965.dss_lin a ha0.le ha1 r _ τ ω
      rw [this, integral_sub h1 (h2.const_mul _), integral_const_mul]
    -- upper bound
    have hratio : ∀ τ : (ℕ → Fin N) → ℕ∞, IsTrajStoppingTime τ → (∀ ω, 1 ≤ τ ω) →
        (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P x) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x) ≤
          greedyIndex σ y x := by
      intro τ hτ hτ1
      have hup := p2mbf_core P a ha0.le ha1 f G _ _ hBf hfb hGb τ hτ hτ1 (fun ω n ↦ by
        by_cases h1 : ((n + 1 : ℕ) : ℕ∞) < τ ω
        · have h0 : (n : ℕ∞) < τ ω := lt_trans (by exact_mod_cast Nat.lt_succ_self n) h1
          rw [if_pos h1, if_pos h0, hK]
          linarith [hE0 (ω (n + 1))]
        · rw [if_neg h1]
          split_ifs
          · exact hG0 _
          · exact le_rfl) x
      rw [hKx, hbase τ hτ] at hup
      have hW : 1 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x :=
        p2mbf_W1 P a ha0.le ha1 τ ⟨hτ, hτ1⟩ x
      rw [div_le_iff₀ (by linarith)]
      linarith
    -- attainment by the hitting time of the lower set
    have hstop := p2mbf_hit_stop (S := Fin N) (↑(lowSet σ k0) : Set (Fin N))
    have hattain :
        (∫ ω, discountedStoppedSum a r (hittingTime (↑(lowSet σ k0) : Set (Fin N))) ω
            ∂markovChainMeasure P x) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1)
            (hittingTime (↑(lowSet σ k0) : Set (Fin N))) ω ∂markovChainMeasure P x) =
          greedyIndex σ y x := by
      have hlow := p2mbf_core P a ha0.le ha1 (fun z ↦ -f z) (fun z ↦ -G z) _ _ hBf
        (fun z ↦ by rw [abs_neg]; exact hfb z) (fun z ↦ by rw [abs_neg]; exact hGb z)
        _ hstop.1 hstop.2 (fun ω n ↦ by
          by_cases h1 : ((n + 1 : ℕ) : ℕ∞) <
              hittingTime (↑(lowSet σ k0) : Set (Fin N)) ω
          · have h0 : (n : ℕ∞) < hittingTime (↑(lowSet σ k0) : Set (Fin N)) ω :=
              lt_trans (by exact_mod_cast Nat.lt_succ_self n) h1
            rw [if_pos h1, if_pos h0]
            have hz := P2M965.hit_not_mem _ ω (n + 1) (by omega) h1
            have hz' : ¬ ((σ.symm (ω (n + 1)) : Fin N) : ℕ) < k0 := by
              intro hh
              exact hz (Finset.mem_coe.2 ((P2M965.mem_lowSet σ k0 _).2 hh))
            have hE := hEhigh _ hz'
            have hKz := hK (ω (n + 1))
            rw [integral_neg]
            linarith
          · rw [if_neg h1]
            split_ifs with h0
            · have hm := P2M965.hit_mem _ ω n h0 h1
              have hm' := (P2M965.mem_lowSet σ k0 _).1 (Finset.mem_coe.1 hm)
              rw [hGlow _ hm'.le]
              simp
            · exact le_rfl) x
      have hneg : (fun ω ↦ discountedStoppedSum a (fun z ↦ -f z)
          (hittingTime (↑(lowSet σ k0) : Set (Fin N))) ω) = fun ω ↦
          -discountedStoppedSum a f (hittingTime (↑(lowSet σ k0) : Set (Fin N))) ω := by
        funext ω
        exact p2mbf_dss_neg a f _ ω
      rw [hneg, integral_neg, integral_neg, hbase _ hstop.1] at hlow
      have hup := hratio _ hstop.1 hstop.2
      have hW : 1 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1)
          (hittingTime (↑(lowSet σ k0) : Set (Fin N))) ω ∂markovChainMeasure P x :=
        p2mbf_W1 P a ha0.le ha1 _ hstop x
      rw [div_le_iff₀ (by linarith)] at hup
      rw [div_eq_iff (by linarith)]
      have := hKx
      linarith
    have hGr : IsGreatest {g : ℝ | ∃ τ : (ℕ → Fin N) → ℕ∞, IsTrajStoppingTime τ ∧
        (∀ ω, 1 ≤ τ ω) ∧
        g = (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P x) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x)}
        (greedyIndex σ y x) := by
      refine ⟨⟨_, hstop.1, hstop.2, hattain.symm⟩, ?_⟩
      rintro g ⟨τ, hτ, hτ1, rfl⟩
      exact hratio τ hτ hτ1
    unfold gittinsIndex
    exact hGr.csSup_eq.symm
