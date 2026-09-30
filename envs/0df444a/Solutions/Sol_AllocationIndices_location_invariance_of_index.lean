-- Prove2me | solution 1 for AllocationIndices.location_invariance_of_index
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T08:16:11.42432+00:00
-- url     : https://prove2.me/submissions/4dc3864a-ab61-493f-9d47-ff538fc7d0ba

import Mathlib
import Definitions.Def_AllocationIndices_Sampling

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m68_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m68_marg0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : (markovChainMeasure P x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

open MeasureTheory ProbabilityTheory in
private lemma p2m68_ext {S : Type*} [MeasurableSpace S] (μ ν : Measure (ℕ → S))
    [IsFiniteMeasure ν]
    (h : ∀ a, μ.map (Preorder.frestrictLe a) = ν.map (Preorder.frestrictLe a)) : μ = ν := by
  have hproj : IsProjectiveMeasureFamily (α := fun _ : ℕ ↦ S)
      (fun I : Finset ℕ ↦ ν.map (fun (f : ℕ → S) (i : I) ↦ f i)) := by
    intro I J hJI
    dsimp only
    rw [Measure.map_map (Finset.measurable_restrict₂ _)
      (measurable_pi_lambda _ (fun i ↦ measurable_pi_apply _))]
    rfl
  have h1 : IsProjectiveLimit (α := fun _ : ℕ ↦ S) μ
      (fun I : Finset ℕ ↦ ν.map (fun (f : ℕ → S) (i : I) ↦ f i)) :=
    (isProjectiveLimit_nat_iff hproj μ).2 h
  have h2 : IsProjectiveLimit (α := fun _ : ℕ ↦ S) ν
      (fun I : Finset ℕ ↦ ν.map (fun (f : ℕ → S) (i : I) ↦ f i)) :=
    fun I ↦ rfl
  exact h1.unique h2

open MeasureTheory ProbabilityTheory in
private lemma p2m68_map_compProd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (m : Measure α) [SFinite m] (κ : Kernel α β) [IsSFiniteKernel κ] (f : α → α)
    (hf : Measurable f) (g : β → β) (hg : Measurable g)
    (h : ∀ᵐ y ∂m, κ (f y) = (κ y).map g) :
    (m.map f) ⊗ₘ κ = (m ⊗ₘ κ).map (Prod.map f g) := by
  ext s hs
  rw [Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf,
    Measure.map_apply (hf.prodMap hg) hs, Measure.compProd_apply ((hf.prodMap hg) hs)]
  refine lintegral_congr_ae (h.mono fun y hy ↦ ?_)
  dsimp only
  rw [hy, Measure.map_apply hg (measurable_prodMk_left hs)]
  rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m68_natural {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (T : S → S) (hT : Measurable T) (A : Set S) (hA : MeasurableSet A)
    (hPA : ∀ y ∈ A, P y Aᶜ = 0) (hPT : ∀ y ∈ A, P (T y) = (P y).map T) (x : S) (hx : x ∈ A) :
    markovChainMeasure P (T x) = (markovChainMeasure P x).map (fun ω n ↦ T (ω n)) := by
  have := p2m68_prob P x
  have := p2m68_prob P (T x)
  have hΦ : Measurable (fun (ω : ℕ → S) n ↦ T (ω n)) :=
    measurable_pi_lambda _ (fun n ↦ hT.comp (measurable_pi_apply n))
  have hTt : ∀ a : ℕ, Measurable (fun (h : Finset.Iic a → S) i ↦ T (h i)) := fun a ↦
    measurable_pi_lambda _ (fun i ↦ hT.comp (measurable_pi_apply i))
  have F1 : ∀ (z : S) (a : ℕ),
      (markovChainMeasure P z).map (Preorder.frestrictLe a) ⊗ₘ markovChainStep P a =
      (markovChainMeasure P z).map (fun ω ↦ (Preorder.frestrictLe a ω, ω (a + 1))) :=
    fun z a ↦ Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  let G : (a : ℕ) → (Finset.Iic a → S) × S → (Finset.Iic (a + 1) → S) := fun a p i ↦
    if h : (i : ℕ) ≤ a then p.1 ⟨i, Finset.mem_Iic.2 h⟩ else p.2
  have hG : ∀ a, Measurable (G a) := by
    intro a
    refine measurable_pi_lambda _ (fun i ↦ ?_)
    by_cases h : (i : ℕ) ≤ a
    · simp only [G, h, dif_pos]
      exact (measurable_pi_apply _).comp measurable_fst
    · simp only [G, h, dif_neg, not_false_eq_true]
      exact measurable_snd
  have hGf : ∀ a (ω : ℕ → S), G a (Preorder.frestrictLe a ω, ω (a + 1)) =
      Preorder.frestrictLe (a + 1) ω := by
    intro a ω
    funext i
    by_cases h : (i : ℕ) ≤ a
    · simp [G, h, Preorder.frestrictLe]
    · have hi : (i : ℕ) = a + 1 := by
        have := Finset.mem_Iic.1 i.2
        omega
      simp [G, Preorder.frestrictLe, hi]
  have hGT : ∀ a (p : (Finset.Iic a → S) × S),
      G a (Prod.map (fun h i ↦ T (h i)) T p) = fun i ↦ T (G a p i) := by
    intro a p
    funext i
    by_cases h : (i : ℕ) ≤ a
    · simp [G, h]
    · simp [G, h]
  have hsplit : ∀ z a, (markovChainMeasure P z).map (Preorder.frestrictLe (a + 1)) =
      ((markovChainMeasure P z).map (Preorder.frestrictLe a) ⊗ₘ markovChainStep P a).map
        (G a) := by
    intro z a
    have := p2m68_prob P z
    rw [F1, Measure.map_map (hG a) (by fun_prop)]
    congr 1
    funext ω
    exact (hGf a ω).symm
  have hae : ∀ a : ℕ, ∀ᵐ ω ∂(markovChainMeasure P x), ω a ∈ A := by
    intro a
    induction a with
    | zero =>
      have h0 : ∀ᵐ h ∂((markovChainMeasure P x).map (Preorder.frestrictLe 0)),
          (h : Finset.Iic 0 → S) ⟨0, Finset.mem_Iic.2 le_rfl⟩ ∈ A := by
        rw [p2m68_marg0]
        exact (ae_dirac_iff (measurable_pi_apply _ hA)).2 hx
      exact ae_of_ae_map (Preorder.measurable_frestrictLe 0).aemeasurable h0
    | succ a ih =>
      rw [ae_iff]
      have hs : MeasurableSet {p : (Finset.Iic a → S) × S | p.2 ∉ A} :=
        measurable_snd hA.compl
      have hmeas : Measurable (fun ω : ℕ → S ↦ (Preorder.frestrictLe a ω, ω (a + 1))) := by
        fun_prop
      have e1 : (markovChainMeasure P x) {ω | ¬ ω (a + 1) ∈ A} =
          ((markovChainMeasure P x).map
            (fun ω ↦ (Preorder.frestrictLe a ω, ω (a + 1)))) {p | p.2 ∉ A} := by
        rw [Measure.map_apply hmeas hs]
        rfl
      have ih' : ∀ᵐ h ∂((markovChainMeasure P x).map (Preorder.frestrictLe a)),
          (h : Finset.Iic a → S) ⟨a, Finset.mem_Iic.2 le_rfl⟩ ∈ A := by
        have hpa : MeasurableSet
            {h : Finset.Iic a → S | h ⟨a, Finset.mem_Iic.2 le_rfl⟩ ∈ A} :=
          (measurable_pi_apply (X := fun _ : Finset.Iic a ↦ S)
            ⟨a, Finset.mem_Iic.2 le_rfl⟩) hA
        exact (ae_map_iff (Preorder.measurable_frestrictLe a).aemeasurable hpa).2 ih
      rw [e1, ← F1, Measure.compProd_apply hs]
      refine (lintegral_congr_ae (ih'.mono fun h hh ↦ ?_)).trans lintegral_zero
      show P (h ⟨a, Finset.mem_Iic.2 le_rfl⟩) Aᶜ = 0
      exact hPA _ hh
  have hm : ∀ a : ℕ, (markovChainMeasure P (T x)).map (Preorder.frestrictLe a) =
      ((markovChainMeasure P x).map (Preorder.frestrictLe a)).map (fun h i ↦ T (h i)) := by
    intro a
    induction a with
    | zero =>
      rw [p2m68_marg0, p2m68_marg0, Measure.map_dirac' (hTt 0)]
    | succ a ih =>
      have ih' : ∀ᵐ h ∂((markovChainMeasure P x).map (Preorder.frestrictLe a)),
          (h : Finset.Iic a → S) ⟨a, Finset.mem_Iic.2 le_rfl⟩ ∈ A := by
        have hpa : MeasurableSet
            {h : Finset.Iic a → S | h ⟨a, Finset.mem_Iic.2 le_rfl⟩ ∈ A} :=
          (measurable_pi_apply (X := fun _ : Finset.Iic a ↦ S)
            ⟨a, Finset.mem_Iic.2 le_rfl⟩) hA
        exact (ae_map_iff (Preorder.measurable_frestrictLe a).aemeasurable hpa).2 (hae a)
      rw [hsplit (T x) a, hsplit x a, ih,
        p2m68_map_compProd _ _ _ (hTt a) T hT (ih'.mono fun h hh ↦ hPT _ hh),
        Measure.map_map (hG a) (by fun_prop), Measure.map_map (hTt (a + 1)) (hG a)]
      congr 1
      funext p
      exact hGT a p
  refine p2m68_ext _ _ (fun a ↦ ?_)
  rw [hm a, Measure.map_map (Preorder.measurable_frestrictLe a) hΦ,
    Measure.map_map (hTt a) (Preorder.measurable_frestrictLe a)]
  rfl


open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m68_stop {S : Type*} [MeasurableSpace S] (T : S → S) (hT : Measurable T)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    IsTrajStoppingTime (fun ω ↦ τ (fun n ↦ T (ω n))) := by
  intro n
  obtain ⟨s, hs, hse⟩ := hτ n
  refine ⟨(fun (h : Finset.Iic n → S) i ↦ T (h i)) ⁻¹' s,
    (measurable_pi_lambda _ (fun i ↦ hT.comp (measurable_pi_apply i))) hs, ?_⟩
  ext ω
  exact Set.ext_iff.1 hse (fun n ↦ T (ω n))

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m68_meas_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
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
private lemma p2m68_meas {S : Type*} [MeasurableSpace S] (a : ℝ) (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum a f τ) := by
  unfold discountedStoppedSum
  exact Measurable.tsum fun t ↦ Measurable.ite (p2m68_meas_lt τ hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t))) measurable_const

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m68_enorm_le {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (f : S → ℝ)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    ‖discountedStoppedSum a f τ ω‖ₑ ≤ ∑' t, ENNReal.ofReal (a ^ t * |f (ω t)|) := by
  unfold discountedStoppedSum
  refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun t ↦ ?_)
  split_ifs
  · rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_pow, abs_of_nonneg ha0]
  · simp

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m68_integrable {S : Type*} [MeasurableSpace S] (ρ : Measure (ℕ → S)) (a : ℝ)
    (ha0 : 0 ≤ a) (f : S → ℝ) (hf : Measurable f) (τ : (ℕ → S) → ℕ∞)
    (hτ : IsTrajStoppingTime τ)
    (hfin : ∫⁻ ω, ∑' t, ENNReal.ofReal (a ^ t * |f (ω t)|) ∂ρ < ⊤) :
    Integrable (discountedStoppedSum a f τ) ρ := by
  refine ⟨(p2m68_meas a f hf τ hτ).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (lintegral_mono fun ω ↦ p2m68_enorm_le a ha0 f τ ω) hfin

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m68_summable1 {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * 1 else 0) := by
  refine Summable.of_nonneg_of_le (fun t ↦ ?_) (fun t ↦ ?_)
    (summable_geometric_of_lt_one ha0 ha1)
  · split_ifs
    · positivity
    · exact le_rfl
  · split_ifs
    · simp
    · exact pow_nonneg ha0 t

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m68_D1_ge {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (h1 : 1 ≤ τ ω) :
    1 ≤ discountedStoppedSum a (fun _ ↦ 1) τ ω := by
  unfold discountedStoppedSum
  have h0 : ((0 : ℕ) : ℕ∞) < τ ω := by
    simpa using lt_of_lt_of_le zero_lt_one h1
  calc (1 : ℝ) = (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * 1 else 0) 0 := by
        simp only [if_pos h0]; simp
    _ ≤ _ := (p2m68_summable1 a ha0 ha1 τ ω).le_tsum 0 (fun j _ ↦ by
        split_ifs
        · positivity
        · exact le_rfl)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m68_D_add {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (c : ℝ) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S)
    (hω : ∑' t, ENNReal.ofReal (a ^ t * |f (ω t)|) < ⊤) :
    discountedStoppedSum a (fun y ↦ f y + c) τ ω =
      discountedStoppedSum a f τ ω + c * discountedStoppedSum a (fun _ ↦ 1) τ ω := by
  unfold discountedStoppedSum
  have hg : Summable (fun t ↦ a ^ t * |f (ω t)|) := by
    refine (ENNReal.summable_toReal hω.ne).congr (fun t ↦ ?_)
    exact ENNReal.toReal_ofReal (by positivity)
  have hs1 : Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) := by
    refine Summable.of_norm_bounded hg (fun t ↦ ?_)
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0]
    · simp only [norm_zero]; positivity
  rw [← tsum_mul_left, ← hs1.tsum_add ((p2m68_summable1 a ha0 ha1 τ ω).mul_left c)]
  refine tsum_congr (fun t ↦ ?_)
  split_ifs <;> ring

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m68_gittins_shift {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (r : S → ℝ) (hrm : Measurable r) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (T U : S → S) (hT : Measurable T) (hU : Measurable U) (hUT : ∀ y, U (T y) = y)
    (c : ℝ) (hrT : ∀ y, r (T y) = r y + c) (x : S)
    (hfin : ∫⁻ ω, ∑' t, ENNReal.ofReal (a ^ t * |r (ω t)|) ∂markovChainMeasure P x < ⊤)
    (y : S)
    (hnat : markovChainMeasure P y = (markovChainMeasure P x).map (fun ω t ↦ T (ω t))) :
    gittinsIndex P r a y = c + gittinsIndex P r a x := by
  have := p2m68_prob P x
  have hΦ : Measurable (fun (ω : ℕ → S) t ↦ T (ω t)) :=
    measurable_pi_lambda _ (fun t ↦ hT.comp (measurable_pi_apply t))
  have hfin1 : ∫⁻ ω, ∑' t, ENNReal.ofReal (a ^ t * |(fun _ : S ↦ (1 : ℝ)) (ω t)|)
      ∂markovChainMeasure P x < ⊤ := by
    simp only [abs_one, mul_one]
    rw [lintegral_const, measure_univ, mul_one, ← ENNReal.ofReal_tsum_of_nonneg
      (fun t ↦ pow_nonneg ha0 t) (summable_geometric_of_lt_one ha0 ha1)]
    exact ENNReal.ofReal_lt_top
  have hDge : ∀ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ → (∀ ω, 1 ≤ τ ω) →
      1 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x := by
    intro τ hτ hτ1
    have hI := p2m68_integrable (markovChainMeasure P x) a ha0 (fun _ ↦ 1) measurable_const
      τ hτ hfin1
    calc (1 : ℝ) = ∫ _ω, (1 : ℝ) ∂markovChainMeasure P x := by simp
      _ ≤ _ := integral_mono (integrable_const 1) hI
          (fun ω ↦ p2m68_D1_ge a ha0 ha1 τ ω (hτ1 ω))
  have hae : ∀ᵐ ω ∂markovChainMeasure P x, ∑' t, ENNReal.ofReal (a ^ t * |r (ω t)|) < ⊤ :=
    ae_lt_top (Measurable.ennreal_tsum fun t ↦ by fun_prop) hfin.ne
  have key : ∀ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ → (∀ ω, 1 ≤ τ ω) →
      (∫ ω, discountedStoppedSum a r τ ω
          ∂((markovChainMeasure P x).map (fun ω t ↦ T (ω t)))) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω
          ∂((markovChainMeasure P x).map (fun ω t ↦ T (ω t)))) =
      c + (∫ ω, discountedStoppedSum a r (fun ω ↦ τ (fun t ↦ T (ω t))) ω
          ∂markovChainMeasure P x) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) (fun ω ↦ τ (fun t ↦ T (ω t))) ω
          ∂markovChainMeasure P x) := by
    intro τ hτ hτ1
    have hτ' := p2m68_stop T hT τ hτ
    rw [integral_map hΦ.aemeasurable (p2m68_meas a r hrm τ hτ).aestronglyMeasurable,
      integral_map hΦ.aemeasurable
        (p2m68_meas a (fun _ ↦ 1) measurable_const τ hτ).aestronglyMeasurable]
    have h1 : ∫ ω, discountedStoppedSum a r τ (fun t ↦ T (ω t)) ∂markovChainMeasure P x =
        ∫ ω, discountedStoppedSum a r (fun ω ↦ τ (fun t ↦ T (ω t))) ω ∂markovChainMeasure P x +
          c * ∫ ω, discountedStoppedSum a (fun _ ↦ 1) (fun ω ↦ τ (fun t ↦ T (ω t))) ω
            ∂markovChainMeasure P x := by
      rw [← integral_const_mul, ← integral_add
        (p2m68_integrable _ a ha0 r hrm _ hτ' hfin)
        ((p2m68_integrable _ a ha0 (fun _ ↦ 1) measurable_const _ hτ' hfin1).const_mul c)]
      refine integral_congr_ae (hae.mono fun ω hω ↦ ?_)
      have e : discountedStoppedSum a r τ (fun t ↦ T (ω t)) =
          discountedStoppedSum a (fun y ↦ r y + c) (fun ω ↦ τ (fun t ↦ T (ω t))) ω := by
        unfold discountedStoppedSum
        simp only [hrT]
      dsimp only
      rw [e, p2m68_D_add a ha0 ha1 r c _ ω hω]
    have h2 : ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ (fun t ↦ T (ω t))
          ∂markovChainMeasure P x =
        ∫ ω, discountedStoppedSum a (fun _ ↦ 1) (fun ω ↦ τ (fun t ↦ T (ω t))) ω
          ∂markovChainMeasure P x := rfl
    have hpos := hDge _ hτ' (fun ω ↦ hτ1 _)
    rw [h1, h2]
    field_simp
    ring
  have hS : {g | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      g = (∫ ω, discountedStoppedSum a r τ ω
          ∂((markovChainMeasure P x).map (fun ω t ↦ T (ω t)))) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω
          ∂((markovChainMeasure P x).map (fun ω t ↦ T (ω t))))} =
      (OrderIso.addLeft c) '' {g | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧
        (∀ ω, 1 ≤ τ ω) ∧
        g = (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P x) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x)} := by
    ext g
    constructor
    · rintro ⟨τ, hτ, hτ1, rfl⟩
      exact ⟨_, ⟨_, p2m68_stop T hT τ hτ, fun ω ↦ hτ1 _, rfl⟩,
        by rw [OrderIso.addLeft_apply]; exact (key τ hτ hτ1).symm⟩
    · rintro ⟨g₀, ⟨τ₀, hτ₀, hτ₀1, rfl⟩, rfl⟩
      refine ⟨fun ω ↦ τ₀ (fun t ↦ U (ω t)), p2m68_stop U hU τ₀ hτ₀, fun ω ↦ hτ₀1 _, ?_⟩
      rw [key _ (p2m68_stop U hU τ₀ hτ₀) (fun ω ↦ hτ₀1 _), OrderIso.addLeft_apply]
      simp only [hUT]
  have hne : {g | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
        g = (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P x) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x)}.Nonempty :=
    ⟨_, fun _ ↦ 1, fun n ↦ MeasurableSet.const _, fun _ ↦ le_rfl, rfl⟩
  have hbdd : BddAbove {g | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
        g = (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P x) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x)} := by
    refine ⟨(∫⁻ ω, ∑' t, ENNReal.ofReal (a ^ t * |r (ω t)|) ∂markovChainMeasure P x).toReal,
      ?_⟩
    rintro g ⟨τ, hτ, hτ1, rfl⟩
    have hM0 := (ENNReal.toReal_nonneg (a := ∫⁻ ω, ∑' t, ENNReal.ofReal (a ^ t * |r (ω t)|)
      ∂markovChainMeasure P x))
    have hN : ∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P x ≤
        (∫⁻ ω, ∑' t, ENNReal.ofReal (a ^ t * |r (ω t)|) ∂markovChainMeasure P x).toReal := by
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_lintegral_norm _).trans
        (ENNReal.toReal_mono hfin.ne (lintegral_mono fun ω ↦ ?_))
      rw [ofReal_norm]
      exact p2m68_enorm_le a ha0 r τ ω
    have hD := hDge τ hτ hτ1
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  calc gittinsIndex P r a y
      = sSup {g | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
          g = (∫ ω, discountedStoppedSum a r τ ω
            ∂((markovChainMeasure P x).map (fun ω t ↦ T (ω t)))) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω
            ∂((markovChainMeasure P x).map (fun ω t ↦ T (ω t))))} := by
        rw [gittinsIndex, hnat]
    _ = _ := by rw [hS, ← OrderIso.map_csSup' _ hne hbdd, OrderIso.addLeft_apply]; rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m68_pred_shift (F : SamplingModel ℝ (ℝ × ℝ))
    (hlik : HasLocationParameter F.likelihood) (hprior : PriorHasLocationParameter F.prior)
    (xb n c : ℝ) : F.predictive (xb + c, n) = (F.predictive (xb, n)).map (· + c) := by
  have hc : Measurable (· + c : ℝ → ℝ) := measurable_add_const c
  ext s hs
  rw [Measure.map_apply hc hs]
  unfold SamplingModel.predictive
  rw [Kernel.comp_apply' _ _ _ hs, Kernel.comp_apply' _ _ _ (hc hs), hprior,
    lintegral_map (F.likelihood.measurable_coe hs) hc]
  refine lintegral_congr (fun θ ↦ ?_)
  rw [hlik, Measure.map_apply hc hs]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m68_reward_shift (F : SamplingModel ℝ (ℝ × ℝ))
    (hlik : HasLocationParameter F.likelihood) (hprior : PriorHasLocationParameter F.prior)
    (hmean : ∀ p, Integrable (fun x : ℝ ↦ x) (F.predictive p)) (xb n c : ℝ) :
    F.rewardOf (xb + c, n) = F.rewardOf (xb, n) + c := by
  unfold SamplingModel.rewardOf
  rw [p2m68_pred_shift F hlik hprior, integral_map (measurable_add_const c).aemeasurable
    (f := fun x : ℝ ↦ x) measurable_id.aestronglyMeasurable,
    integral_add (hmean _) (integrable_const c)]
  simp

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m68_chain_apply {Θ Q : Type*} [MeasurableSpace Θ] [MeasurableSpace Q]
    (F : SamplingModel Θ Q) (p : Q) :
    F.rewardChain p = (F.predictive p).map (F.update p) := by
  rw [SamplingModel.rewardChain, Kernel.map_apply _ F.measurable_update, Kernel.prod_apply,
    Kernel.id_apply, Measure.dirac_prod, Measure.map_map F.measurable_update
      measurable_prodMk_left]
  rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
theorem solution (F : SamplingModel ℝ (ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2})
    (hlik : HasLocationParameter F.likelihood) (hprior : PriorHasLocationParameter F.prior)
    (hupd : F.update = meanUpdate) (hmean : ∀ p, Integrable (fun x : ℝ ↦ x) (F.predictive p))
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hint : DiscountedRewardIntegrable F.rewardChain F.rewardOf a) (xb n : ℝ) (hn : 0 < n) :
    (∀ c : ℝ, F.rewardOf (xb + c, n) = F.rewardOf (xb, n) + c) ∧
    gittinsIndex F.rewardChain F.rewardOf a (xb, n) =
      xb + gittinsIndex F.rewardChain F.rewardOf a (0, n) := by
  have hr : ∀ (p : ℝ × ℝ) (c : ℝ), F.rewardOf (p.1 + c, p.2) = F.rewardOf p + c := by
    intro p c
    have := p2m68_reward_shift F hlik hprior hmean p.1 p.2 c
    rwa [Prod.mk.eta] at this
  refine ⟨fun c ↦ p2m68_reward_shift F hlik hprior hmean xb n c, ?_⟩
  have hrm : Measurable F.rewardOf :=
    (StronglyMeasurable.integral_kernel (κ := F.predictive) stronglyMeasurable_id).measurable
  have hmu : ∀ p : ℝ × ℝ, Measurable (meanUpdate p) := fun p ↦ by
    unfold meanUpdate; fun_prop
  have hA : MeasurableSet {p : ℝ × ℝ | 0 < p.2} := measurableSet_lt measurable_const measurable_snd
  have hPA : ∀ y ∈ {p : ℝ × ℝ | 0 < p.2}, F.rewardChain y {p : ℝ × ℝ | 0 < p.2}ᶜ = 0 := by
    intro y hy
    have hy' : 0 < y.2 := hy
    rw [p2m68_chain_apply, hupd, Measure.map_apply (hmu y) hA.compl]
    have : meanUpdate y ⁻¹' {p : ℝ × ℝ | 0 < p.2}ᶜ = ∅ := by
      ext z
      simp only [meanUpdate, Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_not]
      linarith
    rw [this, measure_empty]
  have hPT : ∀ c : ℝ, ∀ y ∈ {p : ℝ × ℝ | 0 < p.2},
      F.rewardChain ((fun p : ℝ × ℝ ↦ (p.1 + c, p.2)) y) =
        (F.rewardChain y).map (fun p : ℝ × ℝ ↦ (p.1 + c, p.2)) := by
    intro c y hy
    obtain ⟨y1, y2⟩ := y
    have hy' : 0 < y2 := hy
    have hc : Measurable (fun p : ℝ × ℝ ↦ (p.1 + c, p.2)) := by fun_prop
    show F.rewardChain (y1 + c, y2) = _
    rw [p2m68_chain_apply, p2m68_chain_apply, hupd, p2m68_pred_shift F hlik hprior,
      Measure.map_map (hmu _) (measurable_add_const c), Measure.map_map hc (hmu _)]
    congr 1
    funext z
    simp only [Function.comp, meanUpdate, Prod.mk.injEq, and_true]
    field_simp
    ring
  have hTm : Measurable (fun p : ℝ × ℝ ↦ (p.1 + xb, p.2)) := by fun_prop
  have hnat0 := p2m68_natural F.rewardChain (fun p : ℝ × ℝ ↦ (p.1 + xb, p.2)) hTm
    {p : ℝ × ℝ | 0 < p.2} hA hPA (hPT xb) ((0 : ℝ), n) hn
  have hnat : markovChainMeasure F.rewardChain (xb, n) =
      (markovChainMeasure F.rewardChain ((0 : ℝ), n)).map
        (fun ω t ↦ (fun p : ℝ × ℝ ↦ (p.1 + xb, p.2)) (ω t)) := by
    rw [← hnat0]
    simp
  exact p2m68_gittins_shift F.rewardChain F.rewardOf hrm a ha0.le ha1
    (fun p : ℝ × ℝ ↦ (p.1 + xb, p.2)) (fun p : ℝ × ℝ ↦ (p.1 + -xb, p.2)) hTm (by fun_prop)
    (fun y ↦ by simp) xb (fun y ↦ hr y xb) ((0 : ℝ), n) (hint ((0 : ℝ), n)) (xb, n) hnat
