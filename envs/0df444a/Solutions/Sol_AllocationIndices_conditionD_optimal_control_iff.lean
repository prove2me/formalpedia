-- Prove2me | solution 1 for AllocationIndices.conditionD_optimal_control_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T23:28:53.78167+00:00
-- url     : https://prove2.me/submissions/c1af24b6-9276-467f-b358-6401a3a41076

import Mathlib
import Definitions.Def_AllocationIndices_Superprocess

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_marg0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : (markovChainMeasure P x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_int0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) (F : S → ℝ) (hF : Measurable F) :
    ∫ ω, F (ω 0) ∂markovChainMeasure P x = F x := by
  have hFm : Measurable (fun h : (Π _i : Finset.Iic 0, S) ↦ F (h ⟨0, Finset.mem_Iic.2 le_rfl⟩)) :=
    hF.comp (measurable_pi_apply _)
  have h1 := integral_map (μ := markovChainMeasure P x) (Preorder.measurable_frestrictLe 0).aemeasurable
    hFm.aestronglyMeasurable
  rw [p2ma2_marg0, integral_dirac' _ _ hFm.stronglyMeasurable] at h1
  exact h1.symm

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_meas_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
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
private lemma p2ma2_filt_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) (t : ℕ) :
    MeasurableSet[trajectoryFiltration S t] {ω : ℕ → S | (t : ℕ∞) < τ ω} := by
  have : {ω : ℕ → S | (t : ℕ∞) < τ ω} = {ω | τ ω ≤ (t : ℕ∞)}ᶜ := by
    ext ω; simp [not_le]
  rw [this]
  exact (hτ t).compl

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_int_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_abs_int_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → ℝ) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    |∫ x, F x ∂μ| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := B)
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_term_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (f : S → ℝ) (Bf : ℝ)
    (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (t : ℕ) :
    ‖(if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)‖ ≤ Bf * a ^ t := by
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hf _) (pow_nonneg ha0 t)
  · simp only [norm_zero]; positivity

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_summable {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_left Bf)
    (p2ma2_term_bound a ha0 f Bf hBf hf τ ω)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_dss_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    |discountedStoppedSum a f τ ω| ≤ Bf / (1 - a) := by
  unfold discountedStoppedSum
  have hg : HasSum (fun t : ℕ ↦ Bf * a ^ t) (Bf * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0 ha1).mul_left Bf
  have := tsum_of_norm_bounded hg (p2ma2_term_bound a ha0 f Bf hBf hf τ ω)
  rw [Real.norm_eq_abs] at this
  rwa [div_eq_mul_inv]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_tail {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (N : ℕ) :
    |discountedStoppedSum a f τ ω -
        ∑ t ∈ Finset.range N, (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)| ≤
      Bf * a ^ N / (1 - a) := by
  unfold discountedStoppedSum
  have hs := p2ma2_summable a ha0 ha1 f Bf hBf hf τ ω
  rw [← hs.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have hg : HasSum (fun t : ℕ ↦ Bf * a ^ N * a ^ t) (Bf * a ^ N * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0 ha1).mul_left (Bf * a ^ N)
  have := tsum_of_norm_bounded hg (fun t ↦ by
    have h := p2ma2_term_bound a ha0 f Bf hBf hf τ ω (t + N)
    calc _ ≤ Bf * a ^ (t + N) := h
      _ = Bf * a ^ N * a ^ t := by ring)
  rw [Real.norm_eq_abs] at this
  rwa [div_eq_mul_inv]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_dss_meas {S : Type*} [MeasurableSpace S] (a : ℝ) (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum a f τ) := by
  unfold discountedStoppedSum
  exact Measurable.tsum fun t ↦ Measurable.ite (p2ma2_meas_lt τ hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t))) measurable_const

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_dss_int {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : S → ℝ) (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) :
    Integrable (discountedStoppedSum a f τ) (markovChainMeasure P x) := by
  haveI := p2ma2_prob P x
  exact p2ma2_int_of_bound _ _ (p2ma2_dss_meas a f Measurable.of_discrete τ hτ) (Bf / (1 - a))
    (p2ma2_dss_bound a ha0 ha1 f Bf hBf hf τ)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_dss_neg {S : Type*} (a : ℝ) (f : S → ℝ) (τ : (ℕ → S) → ℕ∞)
    (ω : ℕ → S) :
    discountedStoppedSum a (fun y ↦ -f y) τ ω = -discountedStoppedSum a f τ ω := by
  unfold discountedStoppedSum
  rw [← tsum_neg]
  refine tsum_congr fun t ↦ ?_
  split_ifs <;> ring

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_markov {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (s : ℕ) (A : Set (ℕ → S))
    (hA : MeasurableSet[trajectoryFiltration S s] A) (g : S → ℝ) (Bg : ℝ)
    (hg : ∀ y, |g y| ≤ Bg) :
    ∫ ω, A.indicator (fun ω ↦ g (ω (s + 1))) ω ∂markovChainMeasure P x =
      ∫ ω, A.indicator (fun ω ↦ ∫ z, g z ∂P (ω s)) ω ∂markovChainMeasure P x := by
  haveI := p2ma2_prob P x
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
    p2ma2_int_of_bound _ _ hFm Bg (fun p ↦ by
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
private lemma p2ma2_core {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f G : S → ℝ) (Bf BG : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (hG : ∀ y, |G y| ≤ BG)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (hτ1 : ∀ ω, 1 ≤ τ ω)
    (H : ∀ (ω : ℕ → S) (n : ℕ),
      (if ((n + 1 : ℕ) : ℕ∞) < τ ω then f (ω (n + 1)) + a * ∫ z, G z ∂P (ω (n + 1)) else 0) ≤
        (if (n : ℕ∞) < τ ω then G (ω (n + 1)) else 0))
    (x : S) :
    ∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P x ≤
      f x + a * ∫ z, G z ∂P x := by
  haveI hprob := p2ma2_prob P x
  have hBG : 0 ≤ BG := le_trans (abs_nonneg _) (hG x)
  have hPGb : ∀ y, |∫ z, G z ∂P y| ≤ BG := fun y ↦ p2ma2_abs_int_le (P y) G BG hG
  have hfm : Measurable f := Measurable.of_discrete
  have hGm : Measurable G := Measurable.of_discrete
  have hPGm : Measurable (fun y ↦ ∫ z, G z ∂P y) := Measurable.of_discrete
  have htm : ∀ t : ℕ, Measurable
      (fun ω : ℕ → S ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) :=
    fun t ↦ Measurable.ite (p2ma2_meas_lt τ hτ t)
      (measurable_const.mul (hfm.comp (measurable_pi_apply t))) measurable_const
  have htint : ∀ t : ℕ, Integrable
      (fun ω : ℕ → S ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)
      (markovChainMeasure P x) := fun t ↦
    p2ma2_int_of_bound _ _ (htm t) (Bf * a ^ t) (fun ω ↦ by
      have := p2ma2_term_bound a ha0 f Bf hBf hf τ ω t
      rwa [Real.norm_eq_abs] at this)
  have hYint : ∀ N : ℕ, Integrable (fun ω : ℕ → S ↦ ∑ t ∈ Finset.range N,
      (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) (markovChainMeasure P x) :=
    fun N ↦ integrable_finset_sum _ (fun t _ ↦ htint t)
  have hLint : ∀ n : ℕ, Integrable (fun ω : ℕ → S ↦
      if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0)
      (markovChainMeasure P x) := by
    intro n
    refine p2ma2_int_of_bound _ _ ?_ (a ^ (n + 1) * BG) (fun ω ↦ ?_)
    · exact Measurable.ite (p2ma2_meas_lt τ hτ n)
        (measurable_const.mul (hPGm.comp (measurable_pi_apply n))) measurable_const
    · split_ifs
      · rw [abs_mul, abs_pow, abs_of_nonneg ha0]
        exact mul_le_mul_of_nonneg_left (hPGb _) (pow_nonneg ha0 _)
      · simp only [abs_zero]; positivity
  have hM1int : ∀ n : ℕ, Integrable (fun ω : ℕ → S ↦
      {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ G (ω (n + 1))) ω)
      (markovChainMeasure P x) := fun n ↦
    (p2ma2_int_of_bound _ _ (hGm.comp (measurable_pi_apply (n + 1))) BG
      (fun ω ↦ hG _)).indicator (p2ma2_meas_lt τ hτ n)
  have hM2int : ∀ n : ℕ, Integrable (fun ω : ℕ → S ↦
      {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ ∫ z, G z ∂P (ω n)) ω)
      (markovChainMeasure P x) := fun n ↦
    (p2ma2_int_of_bound _ _ (hPGm.comp (measurable_pi_apply n)) BG
      (fun ω ↦ hPGb _)).indicator (p2ma2_meas_lt τ hτ n)
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
    have hmk := p2ma2_markov P x n {ω : ℕ → S | (n : ℕ∞) < τ ω} (p2ma2_filt_lt τ hτ n) G BG hG
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
    exact p2ma2_int0 P x (fun y ↦ f y + a * ∫ z, G z ∂P y) Measurable.of_discrete
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
      refine p2ma2_abs_int_le _ _ _ (fun ω ↦ ?_)
      split_ifs
      · rw [abs_mul, abs_pow, abs_of_nonneg ha0]
        exact mul_le_mul_of_nonneg_left (hPGb _) (pow_nonneg ha0 _)
      · simp only [abs_zero]; exact mul_nonneg (pow_nonneg ha0 _) hBG
    have h3 : |∫ ω, (discountedStoppedSum a f τ ω - ∑ t ∈ Finset.range (n + 1),
        (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) ∂markovChainMeasure P x| ≤
        Bf * a ^ (n + 1) / (1 - a) :=
      p2ma2_abs_int_le _ _ _ (fun ω ↦ p2ma2_tail a ha0 ha1 f Bf hBf hf τ ω (n + 1))
    rw [integral_sub (p2ma2_dss_int P x a ha0 ha1 f Bf hBf hf τ hτ) (hYint (n + 1))] at h3
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
private lemma p2ma2_hit_le {S : Type*} [MeasurableSpace S] (Z : Set S) (ω : ℕ → S) (n : ℕ) :
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
private lemma p2ma2_hit_stop {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (Z : Set S) : IsPositiveStoppingTime (hittingTime Z) := by
  refine ⟨fun n ↦ ?_, fun ω ↦ ?_⟩
  · have : {ω : ℕ → S | hittingTime Z ω ≤ (n : ℕ∞)} =
        (fun ω (i : Finset.Iic n) ↦ ω i.1) ⁻¹'
          ⋃ i : Finset.Iic n, {h : (Π _i : Finset.Iic n, S) | 1 ≤ i.1 ∧ h i ∈ Z} := by
      ext ω
      simp only [Set.mem_setOf_eq, p2ma2_hit_le, Set.mem_preimage, Set.mem_iUnion]
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
private lemma p2ma2_lower {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f G : S → ℝ) (Bf BG : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (hG : ∀ y, |G y| ≤ BG)
    (hGfix : ∀ y, G y = max 0 (f y + a * ∫ z, G z ∂P y)) (Z : Set S)
    (hZ1 : ∀ z ∈ Z, f z + a * ∫ w, G w ∂P z ≤ 0)
    (hZ2 : ∀ z ∉ Z, 0 ≤ f z + a * ∫ w, G w ∂P z) (x : S) :
    f x + a * ∫ z, G z ∂P x ≤
      ∫ ω, discountedStoppedSum a f (hittingTime Z) ω ∂markovChainMeasure P x := by
  have hstop := p2ma2_hit_stop (S := S) Z
  have hcore := p2ma2_core P a ha0 ha1 (fun y ↦ -f y) (fun y ↦ -G y) Bf BG hBf
    (fun y ↦ by simpa using hf y) (fun y ↦ by simpa using hG y) (hittingTime Z) hstop.1 hstop.2
    ?_ x
  · simp only [p2ma2_dss_neg, integral_neg, mul_neg] at hcore
    linarith
  · intro ω n
    simp only [integral_neg, mul_neg]
    by_cases h1 : ((n + 1 : ℕ) : ℕ∞) < hittingTime Z ω
    · have h0 : (n : ℕ∞) < hittingTime Z ω := lt_trans (by exact_mod_cast Nat.lt_succ_self n) h1
      rw [if_pos h1, if_pos h0]
      have hnot : ω (n + 1) ∉ Z := by
        intro hin
        exact (not_le.2 h1) ((p2ma2_hit_le Z ω (n + 1)).2 ⟨n + 1, by omega, le_rfl, hin⟩)
      have hK := hZ2 _ hnot
      rw [hGfix (ω (n + 1)), max_eq_right hK]
      linarith
    · rw [if_neg h1]
      by_cases h0 : (n : ℕ∞) < hittingTime Z ω
      · rw [if_pos h0]
        have hin : ω (n + 1) ∈ Z := by
          obtain ⟨s, hs1, hsn, hs⟩ := (p2ma2_hit_le Z ω (n + 1)).1 (not_lt.1 h1)
          by_cases hsn' : s ≤ n
          · exact absurd ((p2ma2_hit_le Z ω n).2 ⟨s, hs1, hsn', hs⟩) (not_le.2 h0)
          · have : s = n + 1 := by omega
            rw [← this]; exact hs
        have hK := hZ1 _ hin
        rw [hGfix (ω (n + 1)), max_eq_left hK]
        simp
      · rw [if_neg h0]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_W1 {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsPositiveStoppingTime τ) (y : S) :
    1 ≤ stoppedTime P a τ y := by
  have := p2ma2_prob P y
  have hr1 : ∀ y, |(fun _ : S ↦ (1 : ℝ)) y| ≤ 1 := fun y ↦ by simp
  have hint := p2ma2_dss_int P y a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ hτ.1
  have hmono := integral_mono (integrable_const (1 : ℝ)) hint (fun ω ↦ by
    have hsum : Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * 1 else 0) :=
      p2ma2_summable a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ ω
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
private lemma p2ma2_ratio_le {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
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
    have := p2ma2_prob P y
    have hR := p2ma2_abs_int_le (markovChainMeasure P y) _ _
      (p2ma2_dss_bound a ha0 ha1 r M hM0 hM τ)
    have hW : 1 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y :=
      p2ma2_W1 P a ha0 ha1 τ ⟨hτ1, hτ2⟩ y
    calc (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)
        ≤ |∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y| /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y) :=
          div_le_div_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y| :=
          div_le_self (abs_nonneg _) hW
      _ ≤ M / (1 - a) := hR
  have hWpos : 0 < stoppedTime P a τ y :=
    lt_of_lt_of_le zero_lt_one (p2ma2_W1 P a ha0 ha1 τ hτ y)
  have hle : stoppedReward P r a τ y / stoppedTime P a τ y ≤ gittinsIndex P r a y := by
    unfold gittinsIndex
    exact le_csSup hbdd ⟨τ, hτ.1, hτ.2, rfl⟩
  exact (div_le_iff₀ hWpos).1 hle

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_fixgen {Z : Type*} (T : (Z → ℝ) → (Z → ℝ)) (a B : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (hB : 0 ≤ B)
    (hcontr : ∀ (u v : Z → ℝ) (Bu Bv D : ℝ), (∀ z, |u z| ≤ Bu) → (∀ z, |v z| ≤ Bv) →
      (∀ z, |u z - v z| ≤ D) → ∀ y, |T u y - T v y| ≤ a * D)
    (h0 : ∀ y, |T 0 y| ≤ B) :
    ∃ G : Z → ℝ, (∀ y, |G y| ≤ B / (1 - a)) ∧ ∀ y, G y = T G y := by
  have h1a : 0 < 1 - a := by linarith
  have hbd : ∀ u : Z → ℝ, (∀ z, |u z| ≤ B / (1 - a)) → ∀ y, |T u y| ≤ B / (1 - a) := by
    intro u hu y
    have h1 := hcontr u 0 (B / (1 - a)) 0 (B / (1 - a)) hu (fun z ↦ by simp)
      (fun z ↦ by simpa using hu z) y
    have h2 : |T u y| ≤ |T u y - T 0 y| + |T 0 y| := by
      have := abs_add_le (T u y - T 0 y) (T 0 y)
      rwa [sub_add_cancel] at this
    have h3 : B + a * (B / (1 - a)) = B / (1 - a) := by field_simp; ring
    linarith [h0 y]
  let seq : ℕ → Z → ℝ := fun k ↦ T^[k] 0
  have hseq_succ : ∀ k, seq (k + 1) = T (seq k) := fun k ↦ Function.iterate_succ_apply' T k 0
  have hseqb : ∀ k y, |seq k y| ≤ B / (1 - a) := by
    intro k
    induction k with
    | zero => intro y; show |(0 : ℝ)| ≤ _; rw [abs_zero]; positivity
    | succ k ih => rw [hseq_succ]; exact hbd _ ih
  have hdiff : ∀ k y, |seq (k + 1) y - seq k y| ≤ B * a ^ k := by
    intro k
    induction k with
    | zero =>
        intro y
        show |T 0 y - 0| ≤ B * a ^ 0
        rw [sub_zero, pow_zero, mul_one]
        exact h0 y
    | succ k ih =>
        intro y
        calc |seq (k + 1 + 1) y - seq (k + 1) y| = |T (seq (k + 1)) y - T (seq k) y| := by
              rw [hseq_succ (k + 1), hseq_succ k]
          _ ≤ a * (B * a ^ k) := hcontr _ _ _ _ _ (hseqb (k + 1)) (hseqb k) ih y
          _ = B * a ^ (k + 1) := by ring
  have hgeo : ∀ y k, dist (seq k y) (seq (k + 1) y) ≤ B * a ^ k := fun y k ↦ by
    rw [Real.dist_eq, abs_sub_comm]; exact hdiff k y
  have hcauchy : ∀ y, CauchySeq (fun k ↦ seq k y) := fun y ↦
    cauchySeq_of_le_geometric a B ha1 (hgeo y)
  choose G hG using fun y ↦ cauchySeq_tendsto_of_complete (hcauchy y)
  have hGk : ∀ k y, |seq k y - G y| ≤ B * a ^ k / (1 - a) := fun k y ↦ by
    have := dist_le_of_le_geometric_of_tendsto a B ha1 (hgeo y) (hG y) k
    rwa [Real.dist_eq] at this
  have hGb : ∀ y, |G y| ≤ B / (1 - a) := fun y ↦ by
    have := hGk 0 y
    have h0' : seq 0 y = 0 := rfl
    rwa [h0', zero_sub, abs_neg, pow_zero, mul_one] at this
  refine ⟨G, hGb, fun y ↦ ?_⟩
  have hT : Filter.Tendsto (fun k ↦ seq (k + 1) y) Filter.atTop (nhds (T G y)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hlim : Filter.Tendsto (fun k : ℕ ↦ a * (B * a ^ k / (1 - a))) Filter.atTop
        (nhds 0) := by
      have := (((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul B).div_const
        (1 - a)).const_mul a
      simpa using this
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ ?_) hlim
    rw [Real.dist_eq, hseq_succ k]
    exact hcontr _ _ _ _ _ (hseqb k) hGb (hGk k) y
  have hT' : Filter.Tendsto (fun k ↦ seq (k + 1) y) Filter.atTop (nhds (G y)) :=
    (hG y).comp (Filter.tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hT' hT

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private noncomputable def p2ma2_Q {X U : Type*} [MeasurableSpace X] (E : DecisionProcess X U)
    (a : ℝ) (V : (Fin 2 → X) → ℝ) (z : Fin 2 → X) (c : Fin 2 × U) : ℝ :=
  E.reward (z c.1) c.2 + a * ∫ s, V (Function.update z c.1 s) ∂(E.step c.2 (z c.1))

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private noncomputable def p2ma2_B {X U : Type*} [MeasurableSpace X] (E : DecisionProcess X U)
    (a : ℝ) (V : (Fin 2 → X) → ℝ) (z : Fin 2 → X) : ℝ :=
  (Finset.univ : Finset (Fin 2)).sup' Finset.univ_nonempty
    (fun i ↦ (E.avail (z i)).sup' (E.avail_nonempty (z i)) (fun u ↦ p2ma2_Q E a V z (i, u)))

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_le_B {X U : Type*} [MeasurableSpace X] (E : DecisionProcess X U)
    (a : ℝ) (V : (Fin 2 → X) → ℝ) (z : Fin 2 → X) (c : Fin 2 × U)
    (hc : c.2 ∈ E.avail (z c.1)) : p2ma2_Q E a V z c ≤ p2ma2_B E a V z := by
  unfold p2ma2_B
  refine le_trans ?_ (Finset.le_sup' (fun i ↦ (E.avail (z i)).sup' (E.avail_nonempty (z i))
    (fun u ↦ p2ma2_Q E a V z (i, u))) (Finset.mem_univ c.1))
  exact Finset.le_sup' (fun u ↦ p2ma2_Q E a V z (c.1, u)) hc

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_ex_B {X U : Type*} [MeasurableSpace X] (E : DecisionProcess X U)
    (a : ℝ) (V : (Fin 2 → X) → ℝ) (z : Fin 2 → X) :
    ∃ c : Fin 2 × U, c.2 ∈ E.avail (z c.1) ∧ p2ma2_B E a V z = p2ma2_Q E a V z c := by
  unfold p2ma2_B
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin 2))
    (fun i ↦ (E.avail (z i)).sup' (E.avail_nonempty (z i)) (fun u ↦ p2ma2_Q E a V z (i, u)))
  obtain ⟨u, hu, hu'⟩ := Finset.exists_mem_eq_sup' (E.avail_nonempty (z i))
    (fun u ↦ p2ma2_Q E a V z (i, u))
  exact ⟨(i, u), hu, hi.trans hu'⟩

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_Q_contr {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (E : DecisionProcess X U) (a : ℝ) (ha0 : 0 ≤ a)
    (V V' : (Fin 2 → X) → ℝ) (Bu Bv D : ℝ) (hu : ∀ z, |V z| ≤ Bu) (hv : ∀ z, |V' z| ≤ Bv)
    (huv : ∀ z, |V z - V' z| ≤ D) (z : Fin 2 → X) (c : Fin 2 × U) :
    |p2ma2_Q E a V z c - p2ma2_Q E a V' z c| ≤ a * D := by
  unfold p2ma2_Q
  have hi : Integrable (fun s ↦ V (Function.update z c.1 s)) (E.step c.2 (z c.1)) :=
    p2ma2_int_of_bound _ _ (measurable_of_countable _) Bu (fun s ↦ hu _)
  have hi' : Integrable (fun s ↦ V' (Function.update z c.1 s)) (E.step c.2 (z c.1)) :=
    p2ma2_int_of_bound _ _ (measurable_of_countable _) Bv (fun s ↦ hv _)
  have hI : |∫ s, V (Function.update z c.1 s) ∂(E.step c.2 (z c.1)) -
      ∫ s, V' (Function.update z c.1 s) ∂(E.step c.2 (z c.1))| ≤ D := by
    rw [← integral_sub hi hi']
    exact p2ma2_abs_int_le _ _ D (fun s ↦ huv _)
  rw [show E.reward (z c.1) c.2 + a * ∫ s, V (Function.update z c.1 s) ∂(E.step c.2 (z c.1)) -
      (E.reward (z c.1) c.2 + a * ∫ s, V' (Function.update z c.1 s) ∂(E.step c.2 (z c.1))) =
      a * (∫ s, V (Function.update z c.1 s) ∂(E.step c.2 (z c.1)) -
        ∫ s, V' (Function.update z c.1 s) ∂(E.step c.2 (z c.1))) by ring,
    abs_mul, abs_of_nonneg ha0]
  exact mul_le_mul_of_nonneg_left hI ha0

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_B_contr {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (E : DecisionProcess X U) (a : ℝ) (ha0 : 0 ≤ a)
    (V V' : (Fin 2 → X) → ℝ) (Bu Bv D : ℝ) (hu : ∀ z, |V z| ≤ Bu) (hv : ∀ z, |V' z| ≤ Bv)
    (huv : ∀ z, |V z - V' z| ≤ D) (z : Fin 2 → X) :
    |p2ma2_B E a V z - p2ma2_B E a V' z| ≤ a * D := by
  have hvu : ∀ z, |V' z - V z| ≤ D := fun z ↦ by rw [abs_sub_comm]; exact huv z
  obtain ⟨c, hc, hB⟩ := p2ma2_ex_B E a V z
  obtain ⟨c', hc', hB'⟩ := p2ma2_ex_B E a V' z
  have h1 := p2ma2_Q_contr E a ha0 V V' Bu Bv D hu hv huv z c
  have h2 := p2ma2_Q_contr E a ha0 V' V Bv Bu D hv hu hvu z c'
  have h3 := p2ma2_le_B E a V' z c hc
  have h4 := p2ma2_le_B E a V z c' hc'
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_Vstar {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (E : DecisionProcess X U) (a M : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (hM0 : 0 ≤ M) (hM : ∀ y u, |E.reward y u| ≤ M) :
    ∃ V : (Fin 2 → X) → ℝ, (∀ z, |V z| ≤ M / (1 - a)) ∧ ∀ z, V z = p2ma2_B E a V z := by
  refine p2ma2_fixgen (p2ma2_B E a) a M ha0 ha1 hM0
    (fun u v Bu Bv D hu hv huv y ↦ p2ma2_B_contr E a ha0 u v Bu Bv D hu hv huv y) (fun y ↦ ?_)
  obtain ⟨c, -, hc⟩ := p2ma2_ex_B E a 0 y
  rw [hc]
  unfold p2ma2_Q
  simp only [Pi.zero_apply, integral_zero, mul_zero, add_zero]
  exact hM _ _

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_step {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (π : SFASPolicy 2 X U) (z0 : Fin 2 → X) (t : ℕ)
    (φ : SFASHistory 2 X U (t + 1) → ℝ) (B : ℝ) (hφ : ∀ h, |φ h| ≤ B) :
    ∫ h, φ h ∂sfasMeasure E π z0 (t + 1) =
      ∫ h, ∫ c, ∫ s, φ (Fin.snoc (α := fun _ ↦ (Fin 2 → X) × (Fin 2 × U)) h.1 (h.2, c),
        Function.update h.2 c.1 s) ∂(E.step c.2 (h.2 c.1)) ∂(π.select t h)
        ∂(sfasMeasure E π z0 t) := by
  rw [sfasMeasure.eq_2, integral_map
    (measurable_sfasSnoc (n := 2) (S := X) (U := U) (t := t)).aemeasurable
    (measurable_of_countable φ).aestronglyMeasurable, Measure.integral_compProd]
  swap
  · exact p2ma2_int_of_bound _ _ (measurable_of_countable _) B (fun p ↦ hφ _)
  refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
  haveI hη : IsMarkovKernel (Kernel.mk (fun p : SFASHistory 2 X U t × (Fin 2 × U) ↦
      E.step p.2.2 (p.1.2 p.2.1)) (measurable_of_countable _)) :=
    ⟨fun p ↦ (E.markov p.2.2).isProbabilityMeasure _⟩
  try dsimp only
  rw [sfasStepKernel, ProbabilityTheory.integral_compProd]
  swap
  · exact p2ma2_int_of_bound _ _ (measurable_of_countable _) B (fun p ↦ hφ _)
  rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_rr {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (M : ℝ) (hM : ∀ y u, |E.reward y u| ≤ M) (π : SFASPolicy 2 X U)
    (z0 : Fin 2 → X) (t : ℕ) :
    sfasRoundReward E π z0 t =
      ∫ h, ∫ c, E.reward (h.2 c.1) c.2 ∂(π.select t h) ∂(sfasMeasure E π z0 t) := by
  unfold sfasRoundReward
  rw [p2ma2_step E π z0 t (fun h ↦ E.reward ((h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2.1))
    ((h.1 (Fin.last t)).2.2)) M (fun h ↦ hM _ _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun c ↦ ?_)
  simp only [Fin.snoc_last, integral_const, probReal_univ, one_smul, smul_eq_mul, one_mul]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_Astep {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (V : (Fin 2 → X) → ℝ) (BV : ℝ) (hV : ∀ z, |V z| ≤ BV)
    (π : SFASPolicy 2 X U) (z0 : Fin 2 → X) (t : ℕ) :
    ∫ h, V h.2 ∂sfasMeasure E π z0 (t + 1) =
      ∫ h, ∫ c, ∫ s, V (Function.update h.2 c.1 s) ∂(E.step c.2 (h.2 c.1)) ∂(π.select t h)
        ∂(sfasMeasure E π z0 t) :=
  p2ma2_step E π z0 t (fun h ↦ V h.2) BV (fun h ↦ hV _)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_Q_bd {X U : Type*} [MeasurableSpace X] (E : DecisionProcess X U) (a : ℝ)
    (ha0 : 0 ≤ a) (M : ℝ) (hM : ∀ y u, |E.reward y u| ≤ M) (V : (Fin 2 → X) → ℝ) (BV : ℝ)
    (hV : ∀ z, |V z| ≤ BV) (z : Fin 2 → X) (c : Fin 2 × U) :
    |p2ma2_Q E a V z c| ≤ M + a * BV := by
  unfold p2ma2_Q
  have h1 := p2ma2_abs_int_le (E.step c.2 (z c.1)) (fun s ↦ V (Function.update z c.1 s)) BV
    (fun s ↦ hV _)
  calc _ ≤ |E.reward (z c.1) c.2| +
        |a * ∫ s, V (Function.update z c.1 s) ∂(E.step c.2 (z c.1))| := abs_add_le _ _
    _ ≤ M + a * BV := by
        rw [abs_mul, abs_of_nonneg ha0]
        exact add_le_add (hM _ _) (mul_le_mul_of_nonneg_left h1 ha0)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_comb {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (a : ℝ) (M : ℝ) (hM : ∀ y u, |E.reward y u| ≤ M)
    (V : (Fin 2 → X) → ℝ) (BV : ℝ) (hV : ∀ z, |V z| ≤ BV) (π : SFASPolicy 2 X U)
    (z0 : Fin 2 → X) (t : ℕ) :
    sfasRoundReward E π z0 t + a * ∫ h, V h.2 ∂sfasMeasure E π z0 (t + 1) =
      ∫ h, ∫ c, p2ma2_Q E a V h.2 c ∂(π.select t h) ∂(sfasMeasure E π z0 t) := by
  rw [p2ma2_rr E M hM π z0 t, p2ma2_Astep E V BV hV π z0 t]
  have hR : Integrable (fun h : SFASHistory 2 X U t ↦ ∫ c, E.reward (h.2 c.1) c.2
      ∂(π.select t h)) (sfasMeasure E π z0 t) :=
    p2ma2_int_of_bound _ _ (measurable_of_countable _) M
      (fun h ↦ p2ma2_abs_int_le _ _ M (fun c ↦ hM _ _))
  have hG : Integrable (fun h : SFASHistory 2 X U t ↦ ∫ c, ∫ s, V (Function.update h.2 c.1 s)
      ∂(E.step c.2 (h.2 c.1)) ∂(π.select t h)) (sfasMeasure E π z0 t) :=
    p2ma2_int_of_bound _ _ (measurable_of_countable _) BV
      (fun h ↦ p2ma2_abs_int_le _ _ BV (fun c ↦ p2ma2_abs_int_le _ _ BV (fun s ↦ hV _)))
  have e1 := integral_add hR (hG.const_mul a)
  rw [integral_const_mul] at e1
  rw [← e1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
  try dsimp only
  have hR' : Integrable (fun c : Fin 2 × U ↦ E.reward (h.2 c.1) c.2) (π.select t h) :=
    Integrable.of_finite
  have hG' : Integrable (fun c : Fin 2 × U ↦ ∫ s, V (Function.update h.2 c.1 s)
      ∂(E.step c.2 (h.2 c.1))) (π.select t h) := Integrable.of_finite
  have e2 := integral_add hR' (hG'.const_mul a)
  rw [integral_const_mul] at e2
  rw [← e2]
  rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_inner_le {X U : Type*} [MeasurableSpace X] [MeasurableSpace U] [Fintype U]
    [MeasurableSingletonClass U] (E : DecisionProcess X U) (a : ℝ) (V : (Fin 2 → X) → ℝ)
    (hfix : ∀ z, V z = p2ma2_B E a V z) (ν : Measure (Fin 2 × U)) [IsProbabilityMeasure ν]
    (z : Fin 2 → X) (hν : ν {c | c.2 ∈ E.avail (z c.1)} = 1) :
    ∫ c, p2ma2_Q E a V z c ∂ν ≤ V z := by
  have h1 : ν {c | c.2 ∈ E.avail (z c.1)}ᶜ = 0 :=
    (prob_compl_eq_zero_iff MeasurableSet.of_discrete).2 hν
  have hae : ∀ᵐ c ∂ν, c.2 ∈ E.avail (z c.1) := ae_iff.2 h1
  calc ∫ c, p2ma2_Q E a V z c ∂ν ≤ ∫ _c, V z ∂ν :=
        integral_mono_ae Integrable.of_finite (integrable_const _)
          (hae.mono fun c hc ↦ (p2ma2_le_B E a V z c hc).trans_eq (hfix z).symm)
    _ = V z := by rw [integral_const, probReal_univ, one_smul]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_seq_sum (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (rr : ℕ → ℝ) (M : ℝ)
    (hrr : ∀ t, |rr t| ≤ M) : Summable (fun t ↦ a ^ t * rr t) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_left M)
    (fun t ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm]
  exact mul_le_mul_of_nonneg_right (hrr t) (pow_nonneg ha0 t)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_seq_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (rr A : ℕ → ℝ) (M B : ℝ)
    (hrr : ∀ t, |rr t| ≤ M) (hA : ∀ t, |A t| ≤ B)
    (hstep : ∀ t, rr t + a * A (t + 1) ≤ A t) :
    ∑' t, a ^ t * rr t ≤ rr 0 + a * A 1 := by
  have hsum := p2ma2_seq_sum a ha0 ha1 rr M hrr
  have hJ : ∀ k : ℕ, ∑ s ∈ Finset.range (k + 1), a ^ s * rr s + a ^ (k + 1) * A (k + 1) ≤
      rr 0 + a * A 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ]
        have h1 := hstep (k + 1)
        have h2 : 0 ≤ a ^ (k + 1) := pow_nonneg ha0 _
        have h3 : a ^ (k + 1) * (rr (k + 1) + a * A (k + 1 + 1)) ≤ a ^ (k + 1) * A (k + 1) :=
          mul_le_mul_of_nonneg_left h1 h2
        have h4 : a ^ (k + 1 + 1) = a ^ (k + 1) * a := pow_succ a (k + 1)
        rw [h4]
        nlinarith [h3, ih]
  have hlim1 := hsum.hasSum.tendsto_sum_nat
  have hlim2 : Filter.Tendsto (fun t : ℕ ↦ rr 0 + a * A 1 + B * a ^ t) Filter.atTop
      (nhds (rr 0 + a * A 1)) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul B
    simpa using (tendsto_const_nhds (x := rr 0 + a * A 1)).add this
  refine le_of_tendsto_of_tendsto hlim1 hlim2 (Filter.eventually_atTop.2 ⟨1, fun t ht ↦ ?_⟩)
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have h1 := hJ k
  have h2 : -(B * a ^ (k + 1)) ≤ a ^ (k + 1) * A (k + 1) := by
    have hp := pow_nonneg ha0 (k + 1)
    have hA' := (abs_le.1 (hA (k + 1))).1
    nlinarith
  show ∑ s ∈ Finset.range (k + 1), a ^ s * rr s ≤ rr 0 + a * A 1 + B * a ^ (k + 1)
  linarith

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_seq_eq (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (rr A : ℕ → ℝ) (M B : ℝ)
    (hrr : ∀ t, |rr t| ≤ M) (hA : ∀ t, |A t| ≤ B)
    (hstep : ∀ t, rr t + a * A (t + 1) = A t) :
    ∑' t, a ^ t * rr t = A 0 := by
  have hsum := p2ma2_seq_sum a ha0 ha1 rr M hrr
  have hJ : ∀ k : ℕ, ∑ s ∈ Finset.range k, a ^ s * rr s = A 0 - a ^ k * A k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih, pow_succ, ← hstep k]
        ring
  have hlim1 := hsum.hasSum.tendsto_sum_nat
  have h0 : Filter.Tendsto (fun k : ℕ ↦ a ^ k * A k) Filter.atTop (nhds 0) := by
    have hB : Filter.Tendsto (fun k : ℕ ↦ a ^ k * B) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const B
    refine squeeze_zero_norm (fun k ↦ ?_) hB
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (hA k) (pow_nonneg ha0 k)
  have hlim2 : Filter.Tendsto (fun k : ℕ ↦ A 0 - a ^ k * A k) Filter.atTop (nhds (A 0)) := by
    simpa using (tendsto_const_nhds (x := A 0)).sub h0
  exact tendsto_nhds_unique (hlim1.congr hJ) hlim2

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_val_le {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (M : ℝ)
    (hM : ∀ y u, |E.reward y u| ≤ M) (V : (Fin 2 → X) → ℝ) (BV : ℝ)
    (hV : ∀ z, |V z| ≤ BV) (hfix : ∀ z, V z = p2ma2_B E a V z) (π : SFASPolicy 2 X U)
    (hπ : IsFeasiblePolicy E π) (z0 : Fin 2 → X) :
    sfasValue E a π z0 ≤ ∫ c, p2ma2_Q E a V z0 c ∂(π.select 0 (fun i ↦ i.elim0, z0)) := by
  have hstep : ∀ t, sfasRoundReward E π z0 t + a * ∫ h, V h.2 ∂sfasMeasure E π z0 (t + 1) ≤
      ∫ h, V h.2 ∂sfasMeasure E π z0 t := by
    intro t
    rw [p2ma2_comb E a M hM V BV hV π z0 t]
    exact integral_mono (p2ma2_int_of_bound _ _ (measurable_of_countable _) (M + a * BV)
      (fun h ↦ p2ma2_abs_int_le _ _ _ (fun c ↦ p2ma2_Q_bd E a ha0 M hM V BV hV _ _)))
      (p2ma2_int_of_bound _ _ (measurable_of_countable _) BV (fun h ↦ hV _))
      (fun h ↦ p2ma2_inner_le E a V hfix (π.select t h) h.2 (hπ t h))
  have h1 := p2ma2_seq_le a ha0 ha1 (fun t ↦ sfasRoundReward E π z0 t)
    (fun t ↦ ∫ h, V h.2 ∂sfasMeasure E π z0 t) M BV
    (fun t ↦ p2ma2_abs_int_le _ _ M (fun h ↦ hM _ _))
    (fun t ↦ p2ma2_abs_int_le _ _ BV (fun h ↦ hV _)) hstep
  unfold sfasValue
  refine h1.trans (le_of_eq ?_)
  have hc := p2ma2_comb E a M hM V BV hV π z0 0
  rw [zero_add] at hc
  rw [hc, sfasMeasure.eq_1, integral_dirac]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private noncomputable def p2ma2_pol {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (f : (Fin 2 → X) → Fin 2 × U) : SFASPolicy 2 X U where
  select t := Kernel.deterministic (fun h : SFASHistory 2 X U t ↦ f h.2)
    (measurable_of_countable _)
  markov _ := inferInstance

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_pol_apply {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (f : (Fin 2 → X) → Fin 2 × U) (t : ℕ) (h : SFASHistory 2 X U t) :
    (p2ma2_pol f).select t h = Measure.dirac (f h.2) :=
  Kernel.deterministic_apply (f := fun h : SFASHistory 2 X U t ↦ f h.2)
    (measurable_of_countable _) h

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_pol_feas {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (f : (Fin 2 → X) → Fin 2 × U)
    (hf : ∀ z, (f z).2 ∈ E.avail (z (f z).1)) : IsFeasiblePolicy E (p2ma2_pol f) := by
  intro t h
  rw [p2ma2_pol_apply]
  exact Measure.dirac_apply_of_mem (hf h.2)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_pol_val {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (M : ℝ)
    (hM : ∀ y u, |E.reward y u| ≤ M) (V : (Fin 2 → X) → ℝ) (BV : ℝ)
    (hV : ∀ z, |V z| ≤ BV) (f : (Fin 2 → X) → Fin 2 × U)
    (hfQ : ∀ z, p2ma2_Q E a V z (f z) = V z) (z0 : Fin 2 → X) :
    sfasValue E a (p2ma2_pol f) z0 = V z0 := by
  have hstep : ∀ t, sfasRoundReward E (p2ma2_pol f) z0 t +
      a * ∫ h, V h.2 ∂sfasMeasure E (p2ma2_pol f) z0 (t + 1) =
      ∫ h, V h.2 ∂sfasMeasure E (p2ma2_pol f) z0 t := by
    intro t
    rw [p2ma2_comb E a M hM V BV hV (p2ma2_pol f) z0 t]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
    show ∫ c, p2ma2_Q E a V h.2 c ∂((p2ma2_pol f).select t h) = V h.2
    rw [p2ma2_pol_apply, integral_dirac]
    exact hfQ h.2
  have h1 := p2ma2_seq_eq a ha0 ha1 (fun t ↦ sfasRoundReward E (p2ma2_pol f) z0 t)
    (fun t ↦ ∫ h, V h.2 ∂sfasMeasure E (p2ma2_pol f) z0 t) M BV
    (fun t ↦ p2ma2_abs_int_le _ _ M (fun h ↦ hM _ _))
    (fun t ↦ p2ma2_abs_int_le _ _ BV (fun h ↦ hV _)) hstep
  unfold sfasValue
  rw [h1, sfasMeasure.eq_1, integral_dirac]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_greedyF {X U : Type*} [MeasurableSpace X] (E : DecisionProcess X U)
    (a : ℝ) (V : (Fin 2 → X) → ℝ) (hfix : ∀ z, V z = p2ma2_B E a V z) :
    ∃ f : (Fin 2 → X) → Fin 2 × U, (∀ z, (f z).2 ∈ E.avail (z (f z).1)) ∧
      ∀ z, p2ma2_Q E a V z (f z) = V z := by
  have hex : ∀ z, ∃ c : Fin 2 × U, c.2 ∈ E.avail (z c.1) ∧ p2ma2_Q E a V z c = V z := by
    intro z
    obtain ⟨c, hc, hB⟩ := p2ma2_ex_B E a V z
    exact ⟨c, hc, by rw [← hB, ← hfix z]⟩
  choose f hf hfQ using hex
  exact ⟨f, hf, hfQ⟩

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_sup {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (M : ℝ)
    (hM : ∀ y u, |E.reward y u| ≤ M) (V : (Fin 2 → X) → ℝ) (BV : ℝ)
    (hV : ∀ z, |V z| ≤ BV) (hfix : ∀ z, V z = p2ma2_B E a V z) (z : Fin 2 → X) :
    (⨆ π' : {π' : SFASPolicy 2 X U // IsFeasiblePolicy E π'}, sfasValue E a π'.1 z) = V z := by
  obtain ⟨f, hf, hfQ⟩ := p2ma2_greedyF E a V hfix
  have hle : ∀ π' : {π' : SFASPolicy 2 X U // IsFeasiblePolicy E π'},
      sfasValue E a π'.1 z ≤ V z := fun π' ↦
    (p2ma2_val_le E a ha0 ha1 M hM V BV hV hfix π'.1 π'.2 z).trans
      (p2ma2_inner_le E a V hfix (π'.1.select 0 (fun i ↦ i.elim0, z)) z
        (π'.2 0 (fun i ↦ i.elim0, z)))
  haveI : Nonempty {π' : SFASPolicy 2 X U // IsFeasiblePolicy E π'} :=
    ⟨⟨p2ma2_pol f, p2ma2_pol_feas E f hf⟩⟩
  refine le_antisymm (ciSup_le hle) ?_
  rw [← p2ma2_pol_val E a ha0 ha1 M hM V BV hV f hfQ z]
  exact le_ciSup (f := fun π' : {π' : SFASPolicy 2 X U // IsFeasiblePolicy E π'} ↦
      sfasValue E a π'.1 z) ⟨V z, by rintro _ ⟨π', rfl⟩; exact hle π'⟩
    ⟨p2ma2_pol f, p2ma2_pol_feas E f hf⟩

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_mkopt {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (M : ℝ)
    (hM : ∀ y u, |E.reward y u| ≤ M) (V : (Fin 2 → X) → ℝ) (BV : ℝ)
    (hV : ∀ z, |V z| ≤ BV) (hfix : ∀ z, V z = p2ma2_B E a V z) (z0 : Fin 2 → X)
    (c0 : Fin 2 × U) (hc0 : c0.2 ∈ E.avail (z0 c0.1)) (hQ : p2ma2_Q E a V z0 c0 = V z0) :
    ∃ π : SFASPolicy 2 X U, IsOptimalSFASPolicy E a π ∧
      π.select 0 (fun i ↦ i.elim0, z0) = Measure.dirac c0 := by
  classical
  obtain ⟨g, hg, hgQ⟩ := p2ma2_greedyF E a V hfix
  have hf : ∀ z, (Function.update g z0 c0 z).2 ∈ E.avail (z (Function.update g z0 c0 z).1) := by
    intro z
    by_cases h : z = z0
    · rw [h, Function.update_self]; exact hc0
    · rw [Function.update_of_ne h]; exact hg z
  have hfQ : ∀ z, p2ma2_Q E a V z (Function.update g z0 c0 z) = V z := by
    intro z
    by_cases h : z = z0
    · rw [h, Function.update_self]; exact hQ
    · rw [Function.update_of_ne h]; exact hgQ z
  refine ⟨p2ma2_pol (Function.update g z0 c0),
    ⟨p2ma2_pol_feas E _ hf, fun z ↦ ?_⟩, ?_⟩
  · rw [p2ma2_pol_val E a ha0 ha1 M hM V BV hV _ hfQ z,
      p2ma2_sup E a ha0 ha1 M hM V BV hV hfix z]
  · rw [p2ma2_pol_apply]
    show Measure.dirac (Function.update g z0 c0 z0) = _
    rw [Function.update_self]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_opt_val {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (M : ℝ)
    (hM : ∀ y u, |E.reward y u| ≤ M) (V : (Fin 2 → X) → ℝ) (BV : ℝ)
    (hV : ∀ z, |V z| ≤ BV) (hfix : ∀ z, V z = p2ma2_B E a V z) (π : SFASPolicy 2 X U)
    (hopt : IsOptimalSFASPolicy E a π) (z : Fin 2 → X) : sfasValue E a π z = V z :=
  (hopt.2 z).trans (p2ma2_sup E a ha0 ha1 M hM V BV hV hfix z)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_upd0 {S : Type*} (y : S) (s : S ⊕ Unit) :
    Function.update (![Sum.inl y, Sum.inr ()] : Fin 2 → S ⊕ Unit) 0 s = ![s, Sum.inr ()] := by
  funext i; fin_cases i <;> simp

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_upd1 {S : Type*} (y : S) :
    Function.update (![Sum.inl y, Sum.inr ()] : Fin 2 → S ⊕ Unit) 1 (Sum.inr ()) =
      ![Sum.inl y, Sum.inr ()] := by
  funext i; fin_cases i <;> simp

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_Q_ws0 {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MeasurableSpace U] [Fintype U] [Nonempty U]
    [MeasurableSingletonClass U] [DiscreteMeasurableSpace (S ⊕ Unit)]
    (D : DecisionProcess S U) (lam a : ℝ) (V : (Fin 2 → S ⊕ Unit) → ℝ) (y : S) (u : U) :
    p2ma2_Q (withStandard D lam) a V ![Sum.inl y, Sum.inr ()] (0, u) =
      D.reward y u + a * ∫ s, V ![Sum.inl s, Sum.inr ()] ∂(D.step u y) := by
  have hstep : (withStandard D lam).step u (Sum.inl y) = (D.step u y).map Sum.inl := by
    show ((D.step u).map Sum.inl) y = _
    exact Kernel.map_apply _ measurable_inl _
  show D.reward y u + a * ∫ s, V (Function.update ![Sum.inl y, Sum.inr ()] 0 s)
      ∂((withStandard D lam).step u (Sum.inl y)) = _
  rw [hstep, integral_map measurable_inl.aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  simp only [p2ma2_upd0]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_Q_ws1 {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MeasurableSpace U] [Fintype U] [Nonempty U]
    [MeasurableSingletonClass U] [DiscreteMeasurableSpace (S ⊕ Unit)]
    (D : DecisionProcess S U) (lam a : ℝ) (V : (Fin 2 → S ⊕ Unit) → ℝ) (y : S) (u : U) :
    p2ma2_Q (withStandard D lam) a V ![Sum.inl y, Sum.inr ()] (1, u) =
      lam + a * V ![Sum.inl y, Sum.inr ()] := by
  have hstep : (withStandard D lam).step u (Sum.inr ()) = Measure.dirac (Sum.inr ()) := by
    show ((Kernel.const Unit (Measure.dirac ())).map Sum.inr) () = _
    rw [Kernel.map_apply _ measurable_inr, Kernel.const_apply, Measure.map_dirac' measurable_inr]
  show lam + a * ∫ s, V (Function.update ![Sum.inl y, Sum.inr ()] 1 s)
      ∂((withStandard D lam).step u (Sum.inr ())) = _
  rw [hstep, integral_dirac, p2ma2_upd1]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private noncomputable def p2ma2_Qu {S U : Type*} [MeasurableSpace S] (D : DecisionProcess S U)
    (a lam : ℝ) (W : S → ℝ) (u : U) (y : S) : ℝ :=
  D.reward y u - lam + a * ∫ s, W s ∂(D.step u y)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_pkg {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MeasurableSpace U] [Fintype U] [Nonempty U]
    [MeasurableSingletonClass U] (D : DecisionProcess S U) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y u, |D.reward y u| ≤ M) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (lam : ℝ) (x : S) :
    ∃ W : S → ℝ, (∃ BW : ℝ, ∀ y, |W y| ≤ BW) ∧ (∀ y, 0 ≤ W y) ∧
      (∀ y, ∀ u ∈ D.avail y, p2ma2_Qu D a lam W u y ≤ W y) ∧
      (∀ y, W y = 0 ∨ ∃ u ∈ D.avail y, W y = p2ma2_Qu D a lam W u y) ∧
      (∀ u ∈ D.avail x, OptimalToApply D a lam x u ↔ p2ma2_Qu D a lam W u x = W x) ∧
      (OptimalToSelect D a lam x ↔ ∃ u ∈ D.avail x, p2ma2_Qu D a lam W u x = W x) := by
  haveI : DiscreteMeasurableSpace (S ⊕ Unit) :=
    ⟨fun s ↦ ⟨(MeasurableSet.of_discrete : MeasurableSet (Sum.inl ⁻¹' s : Set S)),
      (MeasurableSet.of_discrete : MeasurableSet (Sum.inr ⁻¹' s : Set Unit))⟩⟩
  have h1a : 0 < 1 - a := by linarith
  have hME : ∀ y u, |(withStandard D lam).reward y u| ≤ M + |lam| := by
    rintro (y | y) u
    · exact (hM y u).trans (le_add_of_nonneg_right (abs_nonneg _))
    · exact le_add_of_nonneg_left hM0
  obtain ⟨V, hVb, hfix⟩ := p2ma2_Vstar (withStandard D lam) a (M + |lam|) ha0.le ha1
    (add_nonneg hM0 (abs_nonneg _)) hME
  obtain ⟨BV, hBV⟩ : ∃ BV : ℝ, BV = (M + |lam|) / (1 - a) := ⟨_, rfl⟩
  rw [← hBV] at hVb
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = lam / (1 - a) := ⟨_, rfl⟩
  have hLeq : lam + a * L = L := by rw [hL]; field_simp; ring
  obtain ⟨W, hW⟩ : ∃ W : S → ℝ, ∀ y, W y = V ![Sum.inl y, Sum.inr ()] - L :=
    ⟨fun y ↦ V ![Sum.inl y, Sum.inr ()] - L, fun y ↦ rfl⟩
  have hVW : ∀ y, V ![Sum.inl y, Sum.inr ()] = W y + L := fun y ↦ by rw [hW]; ring
  have hQ0 : ∀ y u, p2ma2_Q (withStandard D lam) a V ![Sum.inl y, Sum.inr ()] (0, u) =
      p2ma2_Qu D a lam W u y + L := by
    intro y u
    rw [p2ma2_Q_ws0]
    have hint : ∫ s, W s ∂(D.step u y) = ∫ s, V ![Sum.inl s, Sum.inr ()] ∂(D.step u y) - L := by
      simp_rw [hW]
      rw [integral_sub (p2ma2_int_of_bound _ _ (measurable_of_countable _) BV (fun s ↦ hVb _))
        (integrable_const L), integral_const, probReal_univ, one_smul]
    unfold p2ma2_Qu
    rw [hint]
    linear_combination hLeq
  have hQ1 : ∀ y u, p2ma2_Q (withStandard D lam) a V ![Sum.inl y, Sum.inr ()] (1, u) =
      lam + a * (W y + L) := by
    intro y u
    rw [p2ma2_Q_ws1, hVW]
  have hF1 : ∀ y, ∀ u ∈ D.avail y, p2ma2_Qu D a lam W u y ≤ W y := by
    intro y u hu
    have := p2ma2_le_B (withStandard D lam) a V ![Sum.inl y, Sum.inr ()] (0, u) hu
    rw [← hfix, hQ0, hVW] at this
    linarith
  have hWa : ∀ y, a * W y ≤ W y := by
    intro y
    have := p2ma2_le_B (withStandard D lam) a V ![Sum.inl y, Sum.inr ()]
      (1, Classical.arbitrary U) (Finset.mem_univ _)
    rw [← hfix, hQ1, hVW] at this
    linarith
  have hF0 : ∀ y, 0 ≤ W y := by
    intro y
    have := hWa y
    nlinarith
  have hF2 : ∀ y, W y = 0 ∨ ∃ u ∈ D.avail y, W y = p2ma2_Qu D a lam W u y := by
    intro y
    obtain ⟨c, hc, hB⟩ := p2ma2_ex_B (withStandard D lam) a V ![Sum.inl y, Sum.inr ()]
    rw [← hfix, hVW] at hB
    obtain ⟨i, u⟩ := c
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · right
      refine ⟨u, hc, ?_⟩
      rw [hQ0] at hB
      linarith
    · left
      rw [hQ1] at hB
      have h2 : (1 - a) * W y = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h | h
      · linarith
      · exact h
  have hopt : ∀ π : SFASPolicy 2 (S ⊕ Unit) U, IsOptimalSFASPolicy (withStandard D lam) a π →
      V ![Sum.inl x, Sum.inr ()] ≤ ∫ c, p2ma2_Q (withStandard D lam) a V
        ![Sum.inl x, Sum.inr ()] c ∂(π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])) := by
    intro π hπ
    rw [← p2ma2_opt_val (withStandard D lam) a ha0.le ha1 (M + |lam|) hME V BV hVb hfix π hπ]
    exact p2ma2_val_le (withStandard D lam) a ha0.le ha1 (M + |lam|) hME V BV hVb hfix π hπ.1 _
  refine ⟨W, ⟨BV + |L|, fun y ↦ ?_⟩, hF0, hF1, hF2, fun u hu ↦ ?_, ?_⟩
  · rw [hW, abs_le]
    have h1 := abs_le.1 (hVb ![Sum.inl y, Sum.inr ()])
    constructor <;> linarith [neg_abs_le L, le_abs_self L, h1.1, h1.2]
  · constructor
    · rintro ⟨π, hπ, hsel⟩
      have hle := hopt π hπ
      have hsel' : (π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])) {(0, u)} = 1 := hsel
      have hae : ∀ᵐ c ∂(π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])), c = (0, u) :=
        ae_iff.2 ((prob_compl_eq_zero_iff (measurableSet_singleton _)).2 hsel')
      rw [integral_congr_ae (hae.mono fun c hc ↦ congrArg
        (p2ma2_Q (withStandard D lam) a V ![Sum.inl x, Sum.inr ()]) hc), integral_const,
        probReal_univ, one_smul] at hle
      have hup := p2ma2_le_B (withStandard D lam) a V ![Sum.inl x, Sum.inr ()] (0, u) hu
      rw [← hfix] at hup
      rw [hQ0, hVW] at hle hup
      exact le_antisymm (by linarith) (by linarith)
    · intro hQ
      obtain ⟨π, hπ, hsel⟩ := p2ma2_mkopt (withStandard D lam) a ha0.le ha1 (M + |lam|) hME V
        BV hVb hfix ![Sum.inl x, Sum.inr ()] (0, u) hu (by rw [hQ0, hVW, hQ])
      refine ⟨π, hπ, ?_⟩
      show (π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])) {(0, u)} = 1
      rw [hsel]
      exact Measure.dirac_apply_of_mem rfl
  · constructor
    · rintro ⟨π, hπ, hsel⟩
      have hle := hopt π hπ
      have hsel' : (π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()]))
          {c | c.1 = 0} = 1 := hsel
      have hfe := hπ.1 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])
      have hae1 : ∀ᵐ c ∂(π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])), c.1 = 0 :=
        ae_iff.2 ((prob_compl_eq_zero_iff MeasurableSet.of_discrete).2 hsel')
      have hae2 : ∀ᵐ c ∂(π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])),
          c.2 ∈ (withStandard D lam).avail (![Sum.inl x, Sum.inr ()] c.1) :=
        ae_iff.2 ((prob_compl_eq_zero_iff MeasurableSet.of_discrete).2 hfe)
      obtain ⟨u, hu, hmax⟩ := Finset.exists_mem_eq_sup' (D.avail_nonempty x)
        (fun u ↦ p2ma2_Q (withStandard D lam) a V ![Sum.inl x, Sum.inr ()] (0, u))
      have hbound : ∀ᵐ c ∂(π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])),
          p2ma2_Q (withStandard D lam) a V ![Sum.inl x, Sum.inr ()] c ≤
            p2ma2_Q (withStandard D lam) a V ![Sum.inl x, Sum.inr ()] (0, u) := by
        filter_upwards [hae1, hae2] with c hc1 hc2
        obtain ⟨i, v⟩ := c
        simp only at hc1
        subst hc1
        exact (Finset.le_sup' (fun u ↦ p2ma2_Q (withStandard D lam) a V
          ![Sum.inl x, Sum.inr ()] (0, u)) hc2).trans_eq hmax
      have hle2 := integral_mono_ae Integrable.of_finite (integrable_const _) hbound
      rw [integral_const, probReal_univ, one_smul] at hle2
      have hup := p2ma2_le_B (withStandard D lam) a V ![Sum.inl x, Sum.inr ()] (0, u) hu
      rw [← hfix] at hup
      have hfin := hle.trans hle2
      rw [hQ0, hVW] at hfin hup
      exact ⟨u, hu, le_antisymm (by linarith) (by linarith)⟩
    · rintro ⟨u, hu, hQ⟩
      obtain ⟨π, hπ, hsel⟩ := p2ma2_mkopt (withStandard D lam) a ha0.le ha1 (M + |lam|) hME V
        BV hVb hfix ![Sum.inl x, Sum.inr ()] (0, u) hu (by rw [hQ0, hVW, hQ])
      refine ⟨π, hπ, ?_⟩
      show (π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])) {c | c.1 = 0} = 1
      rw [hsel]
      exact Measure.dirac_apply_of_mem rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_dss_lin {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hr : ∀ y, |r y| ≤ M) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) (lam : ℝ) (x : S) :
    ∫ ω, discountedStoppedSum a (fun y ↦ r y - lam) τ ω ∂markovChainMeasure P x =
      stoppedReward P r a τ x - lam * stoppedTime P a τ x := by
  have h1 : ∀ y, |(fun _ : S ↦ (1 : ℝ)) y| ≤ 1 := fun y ↦ by simp
  have key : ∀ ω, discountedStoppedSum a (fun y ↦ r y - lam) τ ω =
      discountedStoppedSum a r τ ω - lam * discountedStoppedSum a (fun _ ↦ 1) τ ω := by
    intro ω
    unfold discountedStoppedSum
    have h := ((p2ma2_summable a ha0 ha1 r M hM0 hr τ ω).hasSum.sub
      ((p2ma2_summable a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one h1 τ ω).hasSum.mul_left
        lam)).tsum_eq
    refine (tsum_congr (fun t ↦ ?_)).trans h
    split_ifs <;> ring
  simp_rw [key]
  rw [integral_sub (p2ma2_dss_int P x a ha0 ha1 r M hM0 hr τ hτ)
    ((p2ma2_dss_int P x a ha0 ha1 (fun _ ↦ 1) 1 zero_le_one h1 τ hτ).const_mul lam),
    integral_const_mul]
  rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_Tle {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (τ : (ℕ → S) → ℕ∞) (y : S) : stoppedTime P a τ y ≤ 1 / (1 - a) := by
  have := p2ma2_prob P y
  have h := p2ma2_abs_int_le (markovChainMeasure P y) _ _
    (p2ma2_dss_bound a ha0 ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one (fun _ ↦ by simp) τ)
  exact (le_abs_self _).trans h

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_gi_le {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (r : S → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hr : ∀ y, |r y| ≤ M) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (y : S) :
    gittinsIndex P r a y ≤ M / (1 - a) := by
  unfold gittinsIndex
  refine csSup_le ⟨_, fun _ ↦ 1, fun n ↦ MeasurableSet.const _, fun _ ↦ le_rfl, rfl⟩ ?_
  rintro g ⟨τ, hτ1, hτ2, rfl⟩
  have := p2ma2_prob P y
  have hR := p2ma2_abs_int_le (markovChainMeasure P y) _ _
    (p2ma2_dss_bound a ha0 ha1 r M hM0 hr τ)
  have hW : 1 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y :=
    p2ma2_W1 P a ha0 ha1 τ ⟨hτ1, hτ2⟩ y
  calc _ ≤ |∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y| /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y) :=
        div_le_div_of_nonneg_right (le_abs_self _) (by linarith)
    _ ≤ |∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y| :=
        div_le_self (abs_nonneg _) hW
    _ ≤ M / (1 - a) := hR

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_gi_super {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (D : DecisionProcess S U) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y u, |D.reward y u| ≤ M) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (g : S → U)
    (hg : D.IsFeasibleStationary g) (x : S) :
    gittinsIndex (stationaryKernel D g) (stationaryReward D g) a x ≤ superIndex D a x (g x) := by
  unfold superIndex
  exact le_ciSup (f := fun g' : {g' : S → U // D.IsFeasibleStationary g' ∧ g' x = g x} ↦
      gittinsIndex (stationaryKernel D g'.1) (stationaryReward D g'.1) a x)
    ⟨M / (1 - a), by
      rintro _ ⟨g', rfl⟩
      exact p2ma2_gi_le _ _ M hM0 (fun y ↦ hM y (g'.1 y)) a ha0 ha1 x⟩
    ⟨g, hg, rfl⟩

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_fbd {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (D : DecisionProcess S U) (M : ℝ)
    (hM : ∀ y u, |D.reward y u| ≤ M) (lam : ℝ) (g : S → U) (y : S) :
    |stationaryReward D g y - lam| ≤ M + |lam| := by
  have h1 := abs_le.1 (hM y (g y))
  show |D.reward y (g y) - lam| ≤ M + |lam|
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, neg_abs_le lam, le_abs_self lam]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_IU {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (D : DecisionProcess S U) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y u, |D.reward y u| ≤ M) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (lam : ℝ)
    (W : S → ℝ) (BW : ℝ) (hWb : ∀ y, |W y| ≤ BW) (hF0 : ∀ y, 0 ≤ W y)
    (hF1 : ∀ y, ∀ u ∈ D.avail y, p2ma2_Qu D a lam W u y ≤ W y)
    (g : S → U) (hg : ∀ y, g y ∈ D.avail y) (τ : (ℕ → S) → ℕ∞)
    (hτ : IsPositiveStoppingTime τ) (x : S) :
    stoppedReward (stationaryKernel D g) (stationaryReward D g) a τ x -
      lam * stoppedTime (stationaryKernel D g) a τ x ≤ p2ma2_Qu D a lam W (g x) x := by
  have H : ∀ (ω : ℕ → S) (n : ℕ),
      (if ((n + 1 : ℕ) : ℕ∞) < τ ω then (fun y ↦ stationaryReward D g y - lam) (ω (n + 1)) +
        a * ∫ z, W z ∂(stationaryKernel D g) (ω (n + 1)) else 0) ≤
        (if (n : ℕ∞) < τ ω then W (ω (n + 1)) else 0) := by
    intro ω n
    have hK : (fun y ↦ stationaryReward D g y - lam) (ω (n + 1)) +
        a * ∫ z, W z ∂(stationaryKernel D g) (ω (n + 1)) ≤ W (ω (n + 1)) :=
      hF1 _ _ (hg _)
    by_cases h1 : ((n + 1 : ℕ) : ℕ∞) < τ ω
    · have h0 : (n : ℕ∞) < τ ω := lt_trans (by exact_mod_cast Nat.lt_succ_self n) h1
      rw [if_pos h1, if_pos h0]
      exact hK
    · rw [if_neg h1]
      split_ifs
      · exact hF0 _
      · exact le_rfl
  have hcore := p2ma2_core (stationaryKernel D g) a ha0 ha1
    (fun y ↦ stationaryReward D g y - lam) W (M + |lam|) BW (add_nonneg hM0 (abs_nonneg _))
    (p2ma2_fbd D M hM lam g) hWb τ hτ.1 hτ.2 H x
  rw [← p2ma2_dss_lin (stationaryKernel D g) (stationaryReward D g) M hM0 (fun y ↦ hM y (g y))
    a ha0 ha1 τ hτ.1 lam x]
  exact hcore

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_IL {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (D : DecisionProcess S U) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y u, |D.reward y u| ≤ M) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (lam : ℝ)
    (W : S → ℝ) (BW : ℝ) (hWb : ∀ y, |W y| ≤ BW) (g : S → U)
    (hex : ∀ y, W y = max 0 (p2ma2_Qu D a lam W (g y) y)) (x : S) :
    ∃ τ : (ℕ → S) → ℕ∞, IsPositiveStoppingTime τ ∧
      p2ma2_Qu D a lam W (g x) x ≤ stoppedReward (stationaryKernel D g) (stationaryReward D g)
        a τ x - lam * stoppedTime (stationaryKernel D g) a τ x := by
  refine ⟨hittingTime {y | p2ma2_Qu D a lam W (g y) y ≤ 0}, p2ma2_hit_stop _, ?_⟩
  rw [← p2ma2_dss_lin (stationaryKernel D g) (stationaryReward D g) M hM0 (fun y ↦ hM y (g y))
    a ha0 ha1 (hittingTime {y | p2ma2_Qu D a lam W (g y) y ≤ 0}) (p2ma2_hit_stop _).1 lam x]
  exact p2ma2_lower (stationaryKernel D g) a ha0 ha1 (fun y ↦ stationaryReward D g y - lam) W
    (M + |lam|) BW (add_nonneg hM0 (abs_nonneg _)) (p2ma2_fbd D M hM lam g) hWb hex
    {y | p2ma2_Qu D a lam W (g y) y ≤ 0} (fun z hz ↦ hz) (fun z hz ↦ le_of_lt (not_le.1 hz)) x

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_Bl {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (D : DecisionProcess S U) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y u, |D.reward y u| ≤ M) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (lam : ℝ)
    (W : S → ℝ) (BW : ℝ) (hWb : ∀ y, |W y| ≤ BW) (g : S → U)
    (hex : ∀ y, W y = max 0 (p2ma2_Qu D a lam W (g y) y)) (x : S) :
    ∃ T : ℝ, 1 ≤ T ∧ p2ma2_Qu D a lam W (g x) x ≤
      (gittinsIndex (stationaryKernel D g) (stationaryReward D g) a x - lam) * T := by
  obtain ⟨τ, hτ, hle⟩ := p2ma2_IL D M hM0 hM a ha0 ha1 lam W BW hWb g hex x
  have hr := p2ma2_ratio_le (stationaryKernel D g) (stationaryReward D g)
    ⟨M, fun y ↦ hM y (g y)⟩ a ha0 ha1 τ hτ x
  have hT := p2ma2_W1 (stationaryKernel D g) a ha0 ha1 τ hτ x
  exact ⟨_, hT, by nlinarith⟩

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_A {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (D : DecisionProcess S U) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y u, |D.reward y u| ≤ M) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (lam : ℝ)
    (W : S → ℝ) (BW : ℝ) (hWb : ∀ y, |W y| ≤ BW) (hF0 : ∀ y, 0 ≤ W y)
    (hF1 : ∀ y, ∀ u ∈ D.avail y, p2ma2_Qu D a lam W u y ≤ W y) (x : S) (u : U)
    (hu : u ∈ D.avail x) (hlam : lam ≤ superIndex D a x u) :
    0 ≤ p2ma2_Qu D a lam W u x := by
  classical
  by_contra hneg
  push_neg at hneg
  have h1a : 0 < 1 - a := by linarith
  have key : ∀ g : {g : S → U // D.IsFeasibleStationary g ∧ g x = u},
      gittinsIndex (stationaryKernel D g.1) (stationaryReward D g.1) a x ≤
        lam + (1 - a) * p2ma2_Qu D a lam W u x := by
    intro g
    unfold gittinsIndex
    refine csSup_le ⟨_, fun _ ↦ 1, fun n ↦ MeasurableSet.const _, fun _ ↦ le_rfl, rfl⟩ ?_
    rintro _ ⟨τ, hτ1, hτ2, rfl⟩
    have hIU := p2ma2_IU D M hM0 hM a ha0 ha1 lam W BW hWb hF0 hF1 g.1 g.2.1 τ ⟨hτ1, hτ2⟩ x
    rw [g.2.2] at hIU
    have hT1 := p2ma2_W1 (stationaryKernel D g.1) a ha0 ha1 τ ⟨hτ1, hτ2⟩ x
    have hT2 := p2ma2_Tle (stationaryKernel D g.1) a ha0 ha1 τ x
    unfold stoppedReward stoppedTime at hIU hT1 hT2
    have hT2' := (le_div_iff₀ h1a).1 hT2
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (neg_nonneg.2 hneg.le) (by linarith : (0 : ℝ) ≤ 1 -
      (1 - a) * ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω
        ∂markovChainMeasure (stationaryKernel D g.1) x)]
  haveI : Nonempty {g : S → U // D.IsFeasibleStationary g ∧ g x = u} := by
    refine ⟨⟨fun y ↦ if y = x then u else (D.avail_nonempty y).choose, fun y ↦ ?_, by simp⟩⟩
    show (if y = x then u else (D.avail_nonempty y).choose) ∈ D.avail y
    by_cases h : y = x
    · rw [if_pos h, h]; exact hu
    · rw [if_neg h]; exact (D.avail_nonempty y).choose_spec
  have hsup := ciSup_le key
  unfold superIndex at hlam
  nlinarith [mul_neg_of_pos_of_neg h1a hneg]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_greedy {S U : Type*} [MeasurableSpace S] (D : DecisionProcess S U)
    (a lam : ℝ) (W : S → ℝ) (hF0 : ∀ y, 0 ≤ W y)
    (hF1 : ∀ y, ∀ u ∈ D.avail y, p2ma2_Qu D a lam W u y ≤ W y)
    (hF2 : ∀ y, W y = 0 ∨ ∃ u ∈ D.avail y, W y = p2ma2_Qu D a lam W u y)
    (x : S) (u : U) (hu : u ∈ D.avail x) (hWx : W x = max 0 (p2ma2_Qu D a lam W u x)) :
    ∃ g : S → U, D.IsFeasibleStationary g ∧ g x = u ∧
      ∀ y, W y = max 0 (p2ma2_Qu D a lam W (g y) y) := by
  classical
  have hy : ∀ y, ∃ v ∈ D.avail y, W y = max 0 (p2ma2_Qu D a lam W v y) := by
    intro y
    rcases hF2 y with h0 | ⟨v, hv, hveq⟩
    · obtain ⟨v, hv⟩ := D.avail_nonempty y
      refine ⟨v, hv, ?_⟩
      have := hF1 y v hv
      rw [h0, max_eq_left (by linarith)]
    · refine ⟨v, hv, ?_⟩
      rw [← hveq, max_eq_right (hF0 y)]
  choose g0 hg0 hg0' using hy
  refine ⟨Function.update g0 x u, fun y ↦ ?_, Function.update_self _ _ _, fun y ↦ ?_⟩
  · by_cases h : y = x
    · rw [h, Function.update_self]; exact hu
    · rw [Function.update_of_ne h]; exact hg0 y
  · by_cases h : y = x
    · rw [h, Function.update_self]; exact hWx
    · rw [Function.update_of_ne h]; exact hg0' y

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
theorem solution {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MeasurableSpace U] [Fintype U] [Nonempty U]
    [MeasurableSingletonClass U] (D : DecisionProcess S U) (hD : D.BoundedRewards)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hcond : ConditionD D a) (x : S) :
    (∀ lam : ℝ, OptimalToSelect D a lam x ↔ lam ≤ superIndexMax D a x) ∧
    (∀ u ∈ D.avail x, OptimalToApply D a (superIndexMax D a x) x u ↔
      superIndex D a x u = superIndexMax D a x) := by
  obtain ⟨M, hM⟩ := hD
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM x (Classical.arbitrary U))
  have ha0' : 0 ≤ a := ha0.le
  have hgi : ∀ g : S → U, D.IsFeasibleStationary g →
      gittinsIndex (stationaryKernel D g) (stationaryReward D g) a x ≤ superIndexMax D a x :=
    fun g hg ↦ (p2ma2_gi_super D M hM0 hM a ha0' ha1 g hg x).trans
      (Finset.le_sup' (superIndex D a x) (hg x))
  refine ⟨fun lam ↦ ?_, fun u hu ↦ ?_⟩
  · obtain ⟨W, ⟨BW, hWb⟩, hF0, hF1, hF2, -, hsel⟩ := p2ma2_pkg D M hM0 hM a ha0 ha1 lam x
    rw [hsel]
    constructor
    · rintro ⟨u, hu, hQ⟩
      obtain ⟨g, hg, hgx, hgW⟩ := p2ma2_greedy D a lam W hF0 hF1 hF2 x u hu
        (by rw [hQ, max_eq_right (hF0 x)])
      obtain ⟨T, hT, hQT⟩ := p2ma2_Bl D M hM0 hM a ha0' ha1 lam W BW hWb g hgW x
      rw [hgx, hQ] at hQT
      have h1 := hgi g hg
      by_contra hlt
      push_neg at hlt
      have hneg : gittinsIndex (stationaryKernel D g) (stationaryReward D g) a x - lam < 0 := by
        linarith
      nlinarith [mul_neg_of_neg_of_pos hneg (lt_of_lt_of_le one_pos hT), hF0 x]
    · intro hlam
      obtain ⟨u, hu, hmax⟩ := Finset.exists_mem_eq_sup' (D.avail_nonempty x) (superIndex D a x)
      have hQ0 := p2ma2_A D M hM0 hM a ha0' ha1 lam W BW hWb hF0 hF1 x u hu
        (by unfold superIndexMax at hlam; rwa [hmax] at hlam)
      rcases hF2 x with h0 | ⟨v, hv, hveq⟩
      · exact ⟨u, hu, le_antisymm (hF1 x u hu) (by rw [h0]; exact hQ0)⟩
      · exact ⟨v, hv, hveq.symm⟩
  · obtain ⟨W, ⟨BW, hWb⟩, hF0, hF1, hF2, happ, -⟩ :=
      p2ma2_pkg D M hM0 hM a ha0 ha1 (superIndexMax D a x) x
    rw [happ u hu]
    have hWx : W x = 0 := by
      rcases hF2 x with h0 | ⟨v, hv, hveq⟩
      · exact h0
      · by_contra hne
        have hpos : 0 < W x := lt_of_le_of_ne (hF0 x) (Ne.symm hne)
        obtain ⟨g, hg, hgx, hgW⟩ := p2ma2_greedy D a _ W hF0 hF1 hF2 x v hv
          (by rw [← hveq, max_eq_right (hF0 x)])
        obtain ⟨T, hT, hQT⟩ := p2ma2_Bl D M hM0 hM a ha0' ha1 _ W BW hWb g hgW x
        rw [hgx, ← hveq] at hQT
        have h1 := hgi g hg
        have hnp : gittinsIndex (stationaryKernel D g) (stationaryReward D g) a x -
            superIndexMax D a x ≤ 0 := by linarith
        nlinarith [mul_nonneg (neg_nonneg.2 hnp) (by linarith : (0 : ℝ) ≤ T)]
    constructor
    · intro hQ
      obtain ⟨g, hg, hgx, hgW⟩ := p2ma2_greedy D a _ W hF0 hF1 hF2 x u hu
        (by rw [hQ, hWx, max_self])
      obtain ⟨T, hT, hQT⟩ := p2ma2_Bl D M hM0 hM a ha0' ha1 _ W BW hWb g hgW x
      rw [hgx, hQ, hWx] at hQT
      have h1 : superIndexMax D a x ≤
          gittinsIndex (stationaryKernel D g) (stationaryReward D g) a x := by
        by_contra hlt
        push_neg at hlt
        nlinarith [mul_neg_of_neg_of_pos (sub_neg.2 hlt) (lt_of_lt_of_le one_pos hT)]
      have h2 := p2ma2_gi_super D M hM0 hM a ha0' ha1 g hg x
      rw [hgx] at h2
      exact le_antisymm (Finset.le_sup' (superIndex D a x) hu) (h1.trans h2)
    · intro hS
      have hQ0 := p2ma2_A D M hM0 hM a ha0' ha1 _ W BW hWb hF0 hF1 x u hu hS.ge
      exact le_antisymm (hF1 x u hu) (by rw [hWx]; exact hQ0)
