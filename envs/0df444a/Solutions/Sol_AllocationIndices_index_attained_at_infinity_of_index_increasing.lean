-- Prove2me | solution 1 for AllocationIndices.index_attained_at_infinity_of_index_increasing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T13:55:49.79346+00:00
-- url     : https://prove2.me/submissions/0d53d4bd-e123-46d0-9e05-d8fd69b1e9a2

import Mathlib
import Definitions.Def_AllocationIndices_Index

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mcf_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mcf_marg0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : (markovChainMeasure P x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mcf_int0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) (F : S → ℝ) (hF : Measurable F) :
    ∫ ω, F (ω 0) ∂markovChainMeasure P x = F x := by
  have hFm : Measurable (fun h : (Π _i : Finset.Iic 0, S) ↦ F (h ⟨0, Finset.mem_Iic.2 le_rfl⟩)) :=
    hF.comp (measurable_pi_apply _)
  have h1 := integral_map (μ := markovChainMeasure P x) (Preorder.measurable_frestrictLe 0).aemeasurable
    hFm.aestronglyMeasurable
  rw [p2mcf_marg0, integral_dirac' _ _ hFm.stronglyMeasurable] at h1
  exact h1.symm

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mcf_meas_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
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
private lemma p2mcf_filt_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) (t : ℕ) :
    MeasurableSet[trajectoryFiltration S t] {ω : ℕ → S | (t : ℕ∞) < τ ω} := by
  have : {ω : ℕ → S | (t : ℕ∞) < τ ω} = {ω | τ ω ≤ (t : ℕ∞)}ᶜ := by
    ext ω; simp [not_le]
  rw [this]
  exact (hτ t).compl

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mcf_int_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mcf_abs_int_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → ℝ) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    |∫ x, F x ∂μ| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := B)
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mcf_term_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (f : S → ℝ) (Bf : ℝ)
    (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (t : ℕ) :
    ‖(if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)‖ ≤ Bf * a ^ t := by
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hf _) (pow_nonneg ha0 t)
  · simp only [norm_zero]; positivity

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mcf_summable {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_left Bf)
    (p2mcf_term_bound a ha0 f Bf hBf hf τ ω)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mcf_dss_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    |discountedStoppedSum a f τ ω| ≤ Bf / (1 - a) := by
  unfold discountedStoppedSum
  have hg : HasSum (fun t : ℕ ↦ Bf * a ^ t) (Bf * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0 ha1).mul_left Bf
  have := tsum_of_norm_bounded hg (p2mcf_term_bound a ha0 f Bf hBf hf τ ω)
  rw [Real.norm_eq_abs] at this
  rwa [div_eq_mul_inv]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mcf_tail {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (N : ℕ) :
    |discountedStoppedSum a f τ ω -
        ∑ t ∈ Finset.range N, (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)| ≤
      Bf * a ^ N / (1 - a) := by
  unfold discountedStoppedSum
  have hs := p2mcf_summable a ha0 ha1 f Bf hBf hf τ ω
  rw [← hs.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have hg : HasSum (fun t : ℕ ↦ Bf * a ^ N * a ^ t) (Bf * a ^ N * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0 ha1).mul_left (Bf * a ^ N)
  have := tsum_of_norm_bounded hg (fun t ↦ by
    have h := p2mcf_term_bound a ha0 f Bf hBf hf τ ω (t + N)
    calc _ ≤ Bf * a ^ (t + N) := h
      _ = Bf * a ^ N * a ^ t := by ring)
  rw [Real.norm_eq_abs] at this
  rwa [div_eq_mul_inv]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mcf_dss_meas {S : Type*} [MeasurableSpace S] (a : ℝ) (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum a f τ) := by
  unfold discountedStoppedSum
  exact Measurable.tsum fun t ↦ Measurable.ite (p2mcf_meas_lt τ hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t))) measurable_const

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mcf_dss_int {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : S → ℝ) (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) :
    Integrable (discountedStoppedSum a f τ) (markovChainMeasure P x) := by
  haveI := p2mcf_prob P x
  exact p2mcf_int_of_bound _ _ (p2mcf_dss_meas a f Measurable.of_discrete τ hτ) (Bf / (1 - a))
    (p2mcf_dss_bound a ha0 ha1 f Bf hBf hf τ)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mcf_dss_neg {S : Type*} (a : ℝ) (f : S → ℝ) (τ : (ℕ → S) → ℕ∞)
    (ω : ℕ → S) :
    discountedStoppedSum a (fun y ↦ -f y) τ ω = -discountedStoppedSum a f τ ω := by
  unfold discountedStoppedSum
  rw [← tsum_neg]
  refine tsum_congr fun t ↦ ?_
  split_ifs <;> ring

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mcf_markov {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (s : ℕ) (A : Set (ℕ → S))
    (hA : MeasurableSet[trajectoryFiltration S s] A) (g : S → ℝ) (Bg : ℝ)
    (hg : ∀ y, |g y| ≤ Bg) :
    ∫ ω, A.indicator (fun ω ↦ g (ω (s + 1))) ω ∂markovChainMeasure P x =
      ∫ ω, A.indicator (fun ω ↦ ∫ z, g z ∂P (ω s)) ω ∂markovChainMeasure P x := by
  haveI := p2mcf_prob P x
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
    p2mcf_int_of_bound _ _ hFm Bg (fun p ↦ by
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
private lemma p2mcf_core {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f G : S → ℝ) (Bf BG : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (hG : ∀ y, |G y| ≤ BG)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) (hτ1 : ∀ ω, 1 ≤ τ ω)
    (H : ∀ (ω : ℕ → S) (n : ℕ),
      (if ((n + 1 : ℕ) : ℕ∞) < τ ω then f (ω (n + 1)) + a * ∫ z, G z ∂P (ω (n + 1)) else 0) ≤
        (if (n : ℕ∞) < τ ω then G (ω (n + 1)) else 0))
    (x : S) :
    ∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P x ≤
      f x + a * ∫ z, G z ∂P x := by
  haveI hprob := p2mcf_prob P x
  have hBG : 0 ≤ BG := le_trans (abs_nonneg _) (hG x)
  have hPGb : ∀ y, |∫ z, G z ∂P y| ≤ BG := fun y ↦ p2mcf_abs_int_le (P y) G BG hG
  have hfm : Measurable f := Measurable.of_discrete
  have hGm : Measurable G := Measurable.of_discrete
  have hPGm : Measurable (fun y ↦ ∫ z, G z ∂P y) := Measurable.of_discrete
  have htm : ∀ t : ℕ, Measurable
      (fun ω : ℕ → S ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) :=
    fun t ↦ Measurable.ite (p2mcf_meas_lt τ hτ t)
      (measurable_const.mul (hfm.comp (measurable_pi_apply t))) measurable_const
  have htint : ∀ t : ℕ, Integrable
      (fun ω : ℕ → S ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)
      (markovChainMeasure P x) := fun t ↦
    p2mcf_int_of_bound _ _ (htm t) (Bf * a ^ t) (fun ω ↦ by
      have := p2mcf_term_bound a ha0 f Bf hBf hf τ ω t
      rwa [Real.norm_eq_abs] at this)
  have hYint : ∀ N : ℕ, Integrable (fun ω : ℕ → S ↦ ∑ t ∈ Finset.range N,
      (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) (markovChainMeasure P x) :=
    fun N ↦ integrable_finset_sum _ (fun t _ ↦ htint t)
  have hLint : ∀ n : ℕ, Integrable (fun ω : ℕ → S ↦
      if (n : ℕ∞) < τ ω then a ^ (n + 1) * ∫ z, G z ∂P (ω n) else 0)
      (markovChainMeasure P x) := by
    intro n
    refine p2mcf_int_of_bound _ _ ?_ (a ^ (n + 1) * BG) (fun ω ↦ ?_)
    · exact Measurable.ite (p2mcf_meas_lt τ hτ n)
        (measurable_const.mul (hPGm.comp (measurable_pi_apply n))) measurable_const
    · split_ifs
      · rw [abs_mul, abs_pow, abs_of_nonneg ha0]
        exact mul_le_mul_of_nonneg_left (hPGb _) (pow_nonneg ha0 _)
      · simp only [abs_zero]; positivity
  have hM1int : ∀ n : ℕ, Integrable (fun ω : ℕ → S ↦
      {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ G (ω (n + 1))) ω)
      (markovChainMeasure P x) := fun n ↦
    (p2mcf_int_of_bound _ _ (hGm.comp (measurable_pi_apply (n + 1))) BG
      (fun ω ↦ hG _)).indicator (p2mcf_meas_lt τ hτ n)
  have hM2int : ∀ n : ℕ, Integrable (fun ω : ℕ → S ↦
      {ω : ℕ → S | (n : ℕ∞) < τ ω}.indicator (fun ω ↦ ∫ z, G z ∂P (ω n)) ω)
      (markovChainMeasure P x) := fun n ↦
    (p2mcf_int_of_bound _ _ (hPGm.comp (measurable_pi_apply n)) BG
      (fun ω ↦ hPGb _)).indicator (p2mcf_meas_lt τ hτ n)
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
    have hmk := p2mcf_markov P x n {ω : ℕ → S | (n : ℕ∞) < τ ω} (p2mcf_filt_lt τ hτ n) G BG hG
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
    exact p2mcf_int0 P x (fun y ↦ f y + a * ∫ z, G z ∂P y) Measurable.of_discrete
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
      refine p2mcf_abs_int_le _ _ _ (fun ω ↦ ?_)
      split_ifs
      · rw [abs_mul, abs_pow, abs_of_nonneg ha0]
        exact mul_le_mul_of_nonneg_left (hPGb _) (pow_nonneg ha0 _)
      · simp only [abs_zero]; exact mul_nonneg (pow_nonneg ha0 _) hBG
    have h3 : |∫ ω, (discountedStoppedSum a f τ ω - ∑ t ∈ Finset.range (n + 1),
        (if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)) ∂markovChainMeasure P x| ≤
        Bf * a ^ (n + 1) / (1 - a) :=
      p2mcf_abs_int_le _ _ _ (fun ω ↦ p2mcf_tail a ha0 ha1 f Bf hBf hf τ ω (n + 1))
    rw [integral_sub (p2mcf_dss_int P x a ha0 ha1 f Bf hBf hf τ hτ) (hYint (n + 1))] at h3
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

open MeasureTheory ProbabilityTheory in
private lemma p2mcf_fix {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f : S → ℝ) (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) :
    ∃ G : S → ℝ, (∀ y, |G y| ≤ Bf / (1 - a)) ∧
      ∀ y, G y = max 0 (f y + a * ∫ z, G z ∂P y) := by
  have h1a : 0 < 1 - a := by linarith
  let T : (S → ℝ) → (S → ℝ) := fun u y ↦ max 0 (f y + a * ∫ z, u z ∂P y)
  have hmax0 : ∀ p : ℝ, |max 0 p| ≤ |p| := by
    intro p
    rcases le_total 0 p with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, abs_zero]; exact abs_nonneg p
  have hmax : ∀ p q : ℝ, |max 0 p - max 0 q| ≤ |p - q| := by
    intro p q
    rw [max_comm 0 p, max_comm 0 q]; exact abs_max_sub_max_le_abs p q 0
  have hcontr : ∀ (u v : S → ℝ) (Bu Bv D : ℝ), (∀ z, |u z| ≤ Bu) → (∀ z, |v z| ≤ Bv) →
      (∀ z, |u z - v z| ≤ D) → ∀ y, |T u y - T v y| ≤ a * D := by
    intro u v Bu Bv D hu hv huv y
    have hui : Integrable u (P y) := p2mcf_int_of_bound _ _ Measurable.of_discrete Bu hu
    have hvi : Integrable v (P y) := p2mcf_int_of_bound _ _ Measurable.of_discrete Bv hv
    have hI : |∫ z, u z ∂P y - ∫ z, v z ∂P y| ≤ D := by
      rw [← integral_sub hui hvi]; exact p2mcf_abs_int_le (P y) _ D huv
    calc |T u y - T v y|
        ≤ |(f y + a * ∫ z, u z ∂P y) - (f y + a * ∫ z, v z ∂P y)| := hmax _ _
      _ = a * |∫ z, u z ∂P y - ∫ z, v z ∂P y| := by
          rw [show (f y + a * ∫ z, u z ∂P y) - (f y + a * ∫ z, v z ∂P y) =
            a * (∫ z, u z ∂P y - ∫ z, v z ∂P y) by ring, abs_mul, abs_of_nonneg ha0]
      _ ≤ a * D := mul_le_mul_of_nonneg_left hI ha0
  have hbd : ∀ u : S → ℝ, (∀ z, |u z| ≤ Bf / (1 - a)) → ∀ y, |T u y| ≤ Bf / (1 - a) := by
    intro u hu y
    have hI : |∫ z, u z ∂P y| ≤ Bf / (1 - a) := p2mcf_abs_int_le (P y) u _ hu
    calc |T u y| ≤ |f y + a * ∫ z, u z ∂P y| := hmax0 _
      _ ≤ |f y| + |a * ∫ z, u z ∂P y| := abs_add_le _ _
      _ = |f y| + a * |∫ z, u z ∂P y| := by rw [abs_mul, abs_of_nonneg ha0]
      _ ≤ Bf + a * (Bf / (1 - a)) := add_le_add (hf y) (mul_le_mul_of_nonneg_left hI ha0)
      _ = Bf / (1 - a) := by field_simp; ring
  let seq : ℕ → S → ℝ := fun k ↦ T^[k] 0
  have hseq_succ : ∀ k, seq (k + 1) = T (seq k) := fun k ↦ Function.iterate_succ_apply' T k 0
  have hseqb : ∀ k y, |seq k y| ≤ Bf / (1 - a) := by
    intro k
    induction k with
    | zero => intro y; show |(0 : ℝ)| ≤ _; rw [abs_zero]; positivity
    | succ k ih => rw [hseq_succ]; exact hbd _ ih
  have hdiff : ∀ k y, |seq (k + 1) y - seq k y| ≤ Bf * a ^ k := by
    intro k
    induction k with
    | zero =>
        intro y
        show |T 0 y - 0| ≤ Bf * a ^ 0
        have : T 0 y = max 0 (f y + a * ∫ z, (0 : S → ℝ) z ∂P y) := rfl
        rw [this, sub_zero, pow_zero, mul_one]
        simp only [Pi.zero_apply, integral_zero, mul_zero, add_zero]
        exact (hmax0 _).trans (hf y)
    | succ k ih =>
        intro y
        calc |seq (k + 1 + 1) y - seq (k + 1) y| = |T (seq (k + 1)) y - T (seq k) y| := by
              rw [hseq_succ (k + 1), hseq_succ k]
          _ ≤ a * (Bf * a ^ k) := hcontr _ _ _ _ _ (hseqb (k + 1)) (hseqb k) ih y
          _ = Bf * a ^ (k + 1) := by ring
  have hgeo : ∀ y k, dist (seq k y) (seq (k + 1) y) ≤ Bf * a ^ k := fun y k ↦ by
    rw [Real.dist_eq, abs_sub_comm]; exact hdiff k y
  have hcauchy : ∀ y, CauchySeq (fun k ↦ seq k y) := fun y ↦
    cauchySeq_of_le_geometric a Bf ha1 (hgeo y)
  choose G hG using fun y ↦ cauchySeq_tendsto_of_complete (hcauchy y)
  have hGk : ∀ k y, |seq k y - G y| ≤ Bf * a ^ k / (1 - a) := fun k y ↦ by
    have := dist_le_of_le_geometric_of_tendsto a Bf ha1 (hgeo y) (hG y) k
    rwa [Real.dist_eq] at this
  have hGb : ∀ y, |G y| ≤ Bf / (1 - a) := fun y ↦ by
    have := hGk 0 y
    have h0 : seq 0 y = 0 := rfl
    rwa [h0, zero_sub, abs_neg, pow_zero, mul_one] at this
  refine ⟨G, hGb, fun y ↦ ?_⟩
  have hT : Filter.Tendsto (fun k ↦ seq (k + 1) y) Filter.atTop (nhds (T G y)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hlim : Filter.Tendsto (fun k : ℕ ↦ a * (Bf * a ^ k / (1 - a))) Filter.atTop (nhds 0) := by
      have := (((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul Bf).div_const
        (1 - a)).const_mul a
      simpa using this
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ ?_) hlim
    rw [Real.dist_eq, hseq_succ k]
    exact hcontr _ _ _ _ _ (hseqb k) hGb (hGk k) y
  have hT' : Filter.Tendsto (fun k ↦ seq (k + 1) y) Filter.atTop (nhds (G y)) :=
    (hG y).comp (Filter.tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hT' hT

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2mcf_hit_le {S : Type*} [MeasurableSpace S] (Z : Set S) (ω : ℕ → S) (n : ℕ) :
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
private lemma p2mcf_hit_stop {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (Z : Set S) : IsPositiveStoppingTime (hittingTime Z) := by
  refine ⟨fun n ↦ ?_, fun ω ↦ ?_⟩
  · have : {ω : ℕ → S | hittingTime Z ω ≤ (n : ℕ∞)} =
        (fun ω (i : Finset.Iic n) ↦ ω i.1) ⁻¹'
          ⋃ i : Finset.Iic n, {h : (Π _i : Finset.Iic n, S) | 1 ≤ i.1 ∧ h i ∈ Z} := by
      ext ω
      simp only [Set.mem_setOf_eq, p2mcf_hit_le, Set.mem_preimage, Set.mem_iUnion]
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
private lemma p2mcf_upper {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f G : S → ℝ) (Bf BG : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (hG : ∀ y, |G y| ≤ BG)
    (hGfix : ∀ y, G y = max 0 (f y + a * ∫ z, G z ∂P y))
    (τ : (ℕ → S) → ℕ∞) (hτ : IsPositiveStoppingTime τ) (x : S) :
    ∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P x ≤
      f x + a * ∫ z, G z ∂P x := by
  refine p2mcf_core P a ha0 ha1 f G Bf BG hBf hf hG τ hτ.1 hτ.2 (fun ω n ↦ ?_) x
  by_cases h1 : ((n + 1 : ℕ) : ℕ∞) < τ ω
  · have h0 : (n : ℕ∞) < τ ω := lt_trans (by exact_mod_cast Nat.lt_succ_self n) h1
    rw [if_pos h1, if_pos h0, hGfix (ω (n + 1))]
    exact le_max_right _ _
  · rw [if_neg h1]
    split_ifs
    · rw [hGfix (ω (n + 1))]; exact le_max_left _ _
    · exact le_rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2mcf_lower {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (f G : S → ℝ) (Bf BG : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (hG : ∀ y, |G y| ≤ BG)
    (hGfix : ∀ y, G y = max 0 (f y + a * ∫ z, G z ∂P y)) (Z : Set S)
    (hZ1 : ∀ z ∈ Z, f z + a * ∫ w, G w ∂P z ≤ 0)
    (hZ2 : ∀ z ∉ Z, 0 ≤ f z + a * ∫ w, G w ∂P z) (x : S) :
    f x + a * ∫ z, G z ∂P x ≤
      ∫ ω, discountedStoppedSum a f (hittingTime Z) ω ∂markovChainMeasure P x := by
  have hstop := p2mcf_hit_stop (S := S) Z
  have hcore := p2mcf_core P a ha0 ha1 (fun y ↦ -f y) (fun y ↦ -G y) Bf BG hBf
    (fun y ↦ by simpa using hf y) (fun y ↦ by simpa using hG y) (hittingTime Z) hstop.1 hstop.2
    ?_ x
  · simp only [p2mcf_dss_neg, integral_neg, mul_neg] at hcore
    linarith
  · intro ω n
    simp only [integral_neg, mul_neg]
    by_cases h1 : ((n + 1 : ℕ) : ℕ∞) < hittingTime Z ω
    · have h0 : (n : ℕ∞) < hittingTime Z ω := lt_trans (by exact_mod_cast Nat.lt_succ_self n) h1
      rw [if_pos h1, if_pos h0]
      have hnot : ω (n + 1) ∉ Z := by
        intro hin
        exact (not_le.2 h1) ((p2mcf_hit_le Z ω (n + 1)).2 ⟨n + 1, by omega, le_rfl, hin⟩)
      have hK := hZ2 _ hnot
      rw [hGfix (ω (n + 1)), max_eq_right hK]
      linarith
    · rw [if_neg h1]
      by_cases h0 : (n : ℕ∞) < hittingTime Z ω
      · rw [if_pos h0]
        have hin : ω (n + 1) ∈ Z := by
          obtain ⟨s, hs1, hsn, hs⟩ := (p2mcf_hit_le Z ω (n + 1)).1 (not_lt.1 h1)
          by_cases hsn' : s ≤ n
          · exact absurd ((p2mcf_hit_le Z ω n).2 ⟨s, hs1, hsn', hs⟩) (not_le.2 h0)
          · have : s = n + 1 := by omega
            rw [← this]; exact hs
        have hK := hZ1 _ hin
        rw [hGfix (ω (n + 1)), max_eq_left hK]
        simp
      · rw [if_neg h0]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2mcf_l22 {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ξ : S) (stopSet : Set S)
    (h₁ : {x | gittinsIndex P r a x < gittinsIndex P r a ξ} ⊆ stopSet)
    (h₂ : stopSet ⊆ {x | gittinsIndex P r a x ≤ gittinsIndex P r a ξ}) :
    IsPositiveStoppingTime (hittingTime stopSet) ∧
      stoppedRatio P r a (hittingTime stopSet) ξ = gittinsIndex P r a ξ ∧
      ∃ G : S → ℝ, (∃ B : ℝ, ∀ y, |G y| ≤ B) ∧ (∀ y, 0 ≤ G y) ∧
        r ξ - gittinsIndex P r a ξ + a * ∫ z, G z ∂P ξ ≤ 0 ∧
        ∀ y, gittinsIndex P r a ξ < gittinsIndex P r a y → 0 < G y := by
  refine ⟨p2mcf_hit_stop stopSet, ?_⟩
  obtain ⟨M, hM⟩ := hr
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ξ)
  have ha0' : 0 ≤ a := ha0.le
  have h1a : 0 < 1 - a := by linarith
  obtain ⟨lam, hlam⟩ : ∃ l : ℝ, gittinsIndex P r a ξ = l := ⟨_, rfl⟩
  rw [hlam] at h₁ h₂ ⊢
  obtain ⟨f, hfdef⟩ : ∃ f : S → ℝ, f = fun y ↦ r y - lam := ⟨_, rfl⟩
  have hf : ∀ y, |f y| ≤ M + |lam| := fun y ↦ by
    rw [hfdef]; exact (abs_sub _ _).trans (add_le_add (hM y) le_rfl)
  have hBf : 0 ≤ M + |lam| := by positivity
  obtain ⟨G, hGb, hGfix⟩ := p2mcf_fix P a ha0' ha1 f (M + |lam|) hBf hf
  have hr1 : ∀ y, |(fun _ : S ↦ (1 : ℝ)) y| ≤ 1 := fun y ↦ by simp
  -- basic facts about the stopped reward and time
  have hW1 : ∀ τ, IsPositiveStoppingTime τ → ∀ y, 1 ≤ stoppedTime P a τ y := by
    intro τ hτ y
    haveI := p2mcf_prob P y
    have hint := p2mcf_dss_int P y a ha0' ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ hτ.1
    have hmono := integral_mono (integrable_const (1 : ℝ)) hint (fun ω ↦ by
      have hsum : Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * 1 else 0) :=
        p2mcf_summable a ha0' ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ ω
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
  have hWb : ∀ τ, ∀ y, stoppedTime P a τ y ≤ 1 / (1 - a) := by
    intro τ y
    haveI := p2mcf_prob P y
    have := p2mcf_abs_int_le (markovChainMeasure P y) _ _
      (p2mcf_dss_bound a ha0' ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ)
    exact (le_abs_self _).trans this
  have hV : ∀ τ, IsPositiveStoppingTime τ → ∀ y,
      ∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P y =
        stoppedReward P r a τ y - lam * stoppedTime P a τ y := by
    intro τ hτ y
    have hpt : ∀ ω, discountedStoppedSum a f τ ω =
        discountedStoppedSum a r τ ω - lam * discountedStoppedSum a (fun _ ↦ 1) τ ω := by
      intro ω
      unfold discountedStoppedSum
      rw [← tsum_mul_left, ← (p2mcf_summable a ha0' ha1 r M hM0 hM τ ω).tsum_sub
        ((p2mcf_summable a ha0' ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ ω).mul_left lam)]
      refine tsum_congr fun t ↦ ?_
      rw [hfdef]
      split_ifs <;> ring
    simp only [hpt]
    rw [integral_sub (p2mcf_dss_int P y a ha0' ha1 r M hM0 hM τ hτ.1)
      ((p2mcf_dss_int P y a ha0' ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one hr1 τ hτ.1).const_mul lam),
      integral_const_mul]
    rfl
  have hbdd : ∀ y, BddAbove {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧
      (∀ ω, 1 ≤ τ ω) ∧ g = (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)} := by
    intro y
    refine ⟨M / (1 - a), ?_⟩
    rintro g ⟨τ, hτ1, hτ2, rfl⟩
    haveI := p2mcf_prob P y
    have hR := p2mcf_abs_int_le (markovChainMeasure P y) _ _
      (p2mcf_dss_bound a ha0' ha1 r M hM0 hM τ)
    have hW : 1 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y :=
      hW1 τ ⟨hτ1, hτ2⟩ y
    calc (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)
        ≤ |∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y| /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y) :=
          div_le_div_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y| :=
          div_le_self (abs_nonneg _) hW
      _ ≤ M / (1 - a) := hR
  have hratio_le : ∀ τ, IsPositiveStoppingTime τ → ∀ y,
      stoppedReward P r a τ y ≤ gittinsIndex P r a y * stoppedTime P a τ y := by
    intro τ hτ y
    have hWpos : 0 < stoppedTime P a τ y := lt_of_lt_of_le zero_lt_one (hW1 τ hτ y)
    have hle : stoppedReward P r a τ y / stoppedTime P a τ y ≤ gittinsIndex P r a y := by
      unfold gittinsIndex
      exact le_csSup (hbdd y) ⟨τ, hτ.1, hτ.2, rfl⟩
    exact (div_le_iff₀ hWpos).1 hle
  have hupper : ∀ τ, IsPositiveStoppingTime τ → ∀ y,
      ∫ ω, discountedStoppedSum a f τ ω ∂markovChainMeasure P y ≤
        f y + a * ∫ z, G z ∂P y := fun τ hτ y ↦
    p2mcf_upper P a ha0' ha1 f G (M + |lam|) _ hBf hf hGb hGfix τ hτ y
  -- (ii): states whose index is at least `lam` have nonnegative continuation value
  have hii : ∀ y, lam ≤ gittinsIndex P r a y → 0 ≤ f y + a * ∫ z, G z ∂P y := by
    intro y hy
    by_contra hneg
    push_neg at hneg
    set K := f y + a * ∫ z, G z ∂P y with hK
    have hε : 0 < -K * (1 - a) := mul_pos (by linarith) h1a
    have hne : Set.Nonempty {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧
        (∀ ω, 1 ≤ τ ω) ∧ g = (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)} :=
      ⟨_, fun _ ↦ 1, fun n ↦ MeasurableSet.const _, fun _ ↦ le_rfl, rfl⟩
    have hlt : gittinsIndex P r a y - (-K * (1 - a)) < gittinsIndex P r a y := by linarith
    obtain ⟨g, ⟨τ, hτ1, hτ2, rfl⟩, hg⟩ := exists_lt_of_lt_csSup hne hlt
    have hτ : IsPositiveStoppingTime τ := ⟨hτ1, hτ2⟩
    have hWpos : 0 < stoppedTime P a τ y := lt_of_lt_of_le zero_lt_one (hW1 τ hτ y)
    have hWb' := hWb τ y
    have hup := hupper τ hτ y
    rw [hV τ hτ y] at hup
    have hR : (gittinsIndex P r a y - (-K * (1 - a))) * stoppedTime P a τ y <
        stoppedReward P r a τ y := (lt_div_iff₀ hWpos).1 hg
    have hWb'' : (1 - a) * stoppedTime P a τ y ≤ 1 := by
      rw [le_div_iff₀ h1a] at hWb'; linarith
    have hyW : lam * stoppedTime P a τ y ≤ gittinsIndex P r a y * stoppedTime P a τ y :=
      mul_le_mul_of_nonneg_right hy hWpos.le
    nlinarith
  -- (i): states whose index is at most `lam` have nonpositive continuation value
  have hi : ∀ y, gittinsIndex P r a y ≤ lam → f y + a * ∫ z, G z ∂P y ≤ 0 := by
    intro y hy
    have hstop := p2mcf_hit_stop (S := S) {z | f z + a * ∫ w, G w ∂P z ≤ 0}
    have hZ := p2mcf_lower P a ha0' ha1 f G (M + |lam|) _ hBf hf hGb hGfix
      {z | f z + a * ∫ w, G w ∂P z ≤ 0} (fun z hz ↦ hz)
      (fun z hz ↦ le_of_lt (not_le.1 hz)) y
    rw [hV _ hstop y] at hZ
    have h1 := hratio_le _ hstop y
    have h2 := hW1 _ hstop y
    have h3 : gittinsIndex P r a y * stoppedTime P a (hittingTime
        {z | f z + a * ∫ w, G w ∂P z ≤ 0}) y ≤
        lam * stoppedTime P a (hittingTime {z | f z + a * ∫ w, G w ∂P z ≤ 0}) y :=
      mul_le_mul_of_nonneg_right hy (by linarith)
    linarith
  -- the main argument
  have hstop := p2mcf_hit_stop (S := S) stopSet
  have hmain := p2mcf_lower P a ha0' ha1 f G (M + |lam|) _ hBf hf hGb hGfix stopSet
    (fun z hz ↦ hi z (h₂ hz)) (fun z hz ↦ hii z (not_lt.1 (fun h ↦ hz (h₁ h)))) ξ
  rw [hV _ hstop ξ] at hmain
  have hK0 := hii ξ (le_of_eq hlam.symm)
  have hle := hratio_le _ hstop ξ
  rw [hlam] at hle
  have hW := hW1 _ hstop ξ
  have heq : stoppedReward P r a (hittingTime stopSet) ξ =
      lam * stoppedTime P a (hittingTime stopSet) ξ := le_antisymm hle (by linarith)
  have hK0' : f ξ + a * ∫ z, G z ∂P ξ ≤ 0 := hi ξ (le_of_eq hlam)
  have hfξ : f ξ = r ξ - lam := by rw [hfdef]
  have hpos : ∀ y, lam < gittinsIndex P r a y → 0 < G y := by
    intro y hy
    have hne : Set.Nonempty {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧
        (∀ ω, 1 ≤ τ ω) ∧ g = (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)} :=
      ⟨_, fun _ ↦ 1, fun n ↦ MeasurableSet.const _, fun _ ↦ le_rfl, rfl⟩
    obtain ⟨g, ⟨τ, hτ1, hτ2, rfl⟩, hg⟩ := exists_lt_of_lt_csSup hne hy
    have hτ : IsPositiveStoppingTime τ := ⟨hτ1, hτ2⟩
    have hWpos : 0 < stoppedTime P a τ y := lt_of_lt_of_le zero_lt_one (hW1 τ hτ y)
    have hR : lam * stoppedTime P a τ y < stoppedReward P r a τ y := (lt_div_iff₀ hWpos).1 hg
    have hup := hupper τ hτ y
    rw [hV τ hτ y] at hup
    rw [hGfix y]
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  refine ⟨?_, G, ⟨_, hGb⟩, fun y ↦ by rw [hGfix y]; exact le_max_left _ _,
    by linarith, hpos⟩
  unfold stoppedRatio
  rw [heq, mul_div_assoc, div_self (by linarith), mul_one]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2mcf_hit_top {S : Type*} (Z : Set S) (ω : ℕ → S)
    (hω : ∀ t : ℕ, 1 ≤ t → ω t ∉ Z) : hittingTime Z ω = ⊤ := by
  unfold hittingTime
  exact iInf_eq_top.2 fun t ↦ absurd t.2.2 (hω t.1 t.2.1)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
theorem solution {S : Type*} [MeasurableSpace S]
    [Countable S] [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (x : S)
    (h : markovChainMeasure P x
      {ω | ∀ t : ℕ, 1 ≤ t → gittinsIndex P r a x < gittinsIndex P r a (ω t)} = 1) :
    stoppedRatio P r a (fun _ ↦ ⊤) x = gittinsIndex P r a x ∧ r x < gittinsIndex P r a x := by
  obtain ⟨_, hL, G, ⟨BG, hGb⟩, hG0, hK, hpos⟩ :=
    p2mcf_l22 P hr ha0 ha1 x {y | gittinsIndex P r a y ≤ gittinsIndex P r a x}
      (fun y (hy : gittinsIndex P r a y < gittinsIndex P r a x) ↦
        (le_of_lt hy : gittinsIndex P r a y ≤ gittinsIndex P r a x))
      (fun y hy ↦ hy)
  haveI := p2mcf_prob P x
  set E := {ω : ℕ → S | ∀ t : ℕ, 1 ≤ t → gittinsIndex P r a x < gittinsIndex P r a (ω t)}
    with hE
  have hmeas : MeasurableSet E := by
    have : E = ⋂ t : ℕ, (fun ω : ℕ → S ↦ ω t) ⁻¹'
        {y | 1 ≤ t → gittinsIndex P r a x < gittinsIndex P r a y} := by
      ext ω; simp [hE]
    rw [this]
    exact MeasurableSet.iInter fun t ↦ measurable_pi_apply t MeasurableSet.of_discrete
  have h0 : markovChainMeasure P x Eᶜ = 0 := by
    rw [measure_compl hmeas (measure_ne_top _ _), h, measure_univ]
    simp
  have hs : E ∈ ae (markovChainMeasure P x) := mem_ae_iff.2 h0
  have hae : ∀ᵐ ω ∂markovChainMeasure P x,
      hittingTime {y | gittinsIndex P r a y ≤ gittinsIndex P r a x} ω = ⊤ := by
    filter_upwards [hs] with ω hω
    exact p2mcf_hit_top _ ω (fun t ht hin ↦ absurd hin (not_le.2 (hω t ht)))
  have hRe : ∀ f : S → ℝ,
      ∫ ω, discountedStoppedSum a f
        (hittingTime {y | gittinsIndex P r a y ≤ gittinsIndex P r a x}) ω
          ∂markovChainMeasure P x =
      ∫ ω, discountedStoppedSum a f (fun _ ↦ ⊤) ω ∂markovChainMeasure P x := by
    intro f
    refine integral_congr_ae (hae.mono fun ω hω ↦ ?_)
    show discountedStoppedSum a f _ ω = discountedStoppedSum a f (fun _ ↦ ⊤) ω
    unfold discountedStoppedSum
    rw [hω]
  have hEq : stoppedRatio P r a (fun _ ↦ ⊤) x = gittinsIndex P r a x := by
    rw [← hL]
    unfold stoppedRatio stoppedReward stoppedTime
    rw [hRe r, hRe (fun _ ↦ 1)]
  refine ⟨hEq, ?_⟩
  have hPG : ∫ z, G z ∂P x = ∫ ω, G (ω 1) ∂markovChainMeasure P x := by
    have hm := p2mcf_markov P x 0 Set.univ MeasurableSet.univ G BG hGb
    simp only [Set.indicator_univ, zero_add] at hm
    rw [hm]
    exact (p2mcf_int0 P x (fun y ↦ ∫ z, G z ∂P y) Measurable.of_discrete).symm
  have hpos1 : 0 < ∫ ω, G (ω 1) ∂markovChainMeasure P x := by
    have hint : Integrable (fun ω : ℕ → S ↦ G (ω 1)) (markovChainMeasure P x) :=
      p2mcf_int_of_bound _ _ ((Measurable.of_discrete (f := G)).comp (measurable_pi_apply 1))
        BG (fun ω ↦ hGb _)
    rw [integral_pos_iff_support_of_nonneg (fun ω ↦ hG0 _) hint]
    have hsub : E ⊆ Function.support (fun ω : ℕ → S ↦ G (ω 1)) :=
      fun ω hω ↦ (hpos _ (hω 1 le_rfl)).ne'
    have hle := measure_mono (μ := markovChainMeasure P x) hsub
    rw [h] at hle
    exact lt_of_lt_of_le zero_lt_one hle
  have := mul_pos ha0 (hPG ▸ hpos1)
  linarith
