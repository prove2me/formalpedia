-- Prove2me | solution 1 for AllocationIndices.scale_invariance_of_index
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T10:14:39.859648+00:00
-- url     : https://prove2.me/submissions/e5224ea2-f15e-408f-a646-4d88d866f05e

import Mathlib
import Definitions.Def_AllocationIndices_Sampling

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m8e_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m8e_marg0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : (markovChainMeasure P x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

open MeasureTheory ProbabilityTheory in
private lemma p2m8e_ext {S : Type*} [MeasurableSpace S] (μ ν : Measure (ℕ → S))
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
private lemma p2m8e_map_compProd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
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
private lemma p2m8e_natural {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (T : S → S) (hT : Measurable T) (A : Set S) (hA : MeasurableSet A)
    (hPA : ∀ y ∈ A, P y Aᶜ = 0) (hPT : ∀ y ∈ A, P (T y) = (P y).map T) (x : S) (hx : x ∈ A) :
    markovChainMeasure P (T x) = (markovChainMeasure P x).map (fun ω n ↦ T (ω n)) := by
  have := p2m8e_prob P x
  have := p2m8e_prob P (T x)
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
    have := p2m8e_prob P z
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
        rw [p2m8e_marg0]
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
      rw [p2m8e_marg0, p2m8e_marg0, Measure.map_dirac' (hTt 0)]
    | succ a ih =>
      have ih' : ∀ᵐ h ∂((markovChainMeasure P x).map (Preorder.frestrictLe a)),
          (h : Finset.Iic a → S) ⟨a, Finset.mem_Iic.2 le_rfl⟩ ∈ A := by
        have hpa : MeasurableSet
            {h : Finset.Iic a → S | h ⟨a, Finset.mem_Iic.2 le_rfl⟩ ∈ A} :=
          (measurable_pi_apply (X := fun _ : Finset.Iic a ↦ S)
            ⟨a, Finset.mem_Iic.2 le_rfl⟩) hA
        exact (ae_map_iff (Preorder.measurable_frestrictLe a).aemeasurable hpa).2 (hae a)
      rw [hsplit (T x) a, hsplit x a, ih,
        p2m8e_map_compProd _ _ _ (hTt a) T hT (ih'.mono fun h hh ↦ hPT _ hh),
        Measure.map_map (hG a) (by fun_prop), Measure.map_map (hTt (a + 1)) (hG a)]
      congr 1
      funext p
      exact hGT a p
  refine p2m8e_ext _ _ (fun a ↦ ?_)
  rw [hm a, Measure.map_map (Preorder.measurable_frestrictLe a) hΦ,
    Measure.map_map (hTt a) (Preorder.measurable_frestrictLe a)]
  rfl


open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m8e_stop {S : Type*} [MeasurableSpace S] (T : S → S) (hT : Measurable T)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    IsTrajStoppingTime (fun ω ↦ τ (fun n ↦ T (ω n))) := by
  intro n
  obtain ⟨s, hs, hse⟩ := hτ n
  refine ⟨(fun (h : Finset.Iic n → S) i ↦ T (h i)) ⁻¹' s,
    (measurable_pi_lambda _ (fun i ↦ hT.comp (measurable_pi_apply i))) hs, ?_⟩
  ext ω
  exact Set.ext_iff.1 hse (fun n ↦ T (ω n))

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2m8e_meas_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
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
private lemma p2m8e_meas {S : Type*} [MeasurableSpace S] (a : ℝ) (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum a f τ) := by
  unfold discountedStoppedSum
  exact Measurable.tsum fun t ↦ Measurable.ite (p2m8e_meas_lt τ hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t))) measurable_const

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m8e_chain_apply {Θ Q : Type*} [MeasurableSpace Θ] [MeasurableSpace Q]
    (F : SamplingModel Θ Q) (p : Q) :
    F.rewardChain p = (F.predictive p).map (F.update p) := by
  rw [SamplingModel.rewardChain, Kernel.map_apply _ F.measurable_update, Kernel.prod_apply,
    Kernel.id_apply, Measure.dirac_prod, Measure.map_map F.measurable_update
      measurable_prodMk_left]
  rfl


open MeasureTheory ProbabilityTheory BanditAlgorithm Pointwise in
private lemma p2m8e_gittins_scale {S : Type*} [MeasurableSpace S] (P : Kernel S S)
    [IsMarkovKernel P] (r : S → ℝ) (hrm : Measurable r) (a : ℝ)
    (T U : S → S) (hT : Measurable T) (hU : Measurable U) (hUT : ∀ y, U (T y) = y)
    (c : ℝ) (hc : 0 ≤ c) (hrT : ∀ y, r (T y) = c * r y) (x y : S)
    (hnat : markovChainMeasure P y = (markovChainMeasure P x).map (fun ω t ↦ T (ω t))) :
    gittinsIndex P r a y = c * gittinsIndex P r a x := by
  have hΦ : Measurable (fun (ω : ℕ → S) t ↦ T (ω t)) :=
    measurable_pi_lambda _ (fun t ↦ hT.comp (measurable_pi_apply t))
  have key : ∀ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ →
      (∫ ω, discountedStoppedSum a r τ ω
          ∂((markovChainMeasure P x).map (fun ω t ↦ T (ω t)))) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω
          ∂((markovChainMeasure P x).map (fun ω t ↦ T (ω t)))) =
      c * ((∫ ω, discountedStoppedSum a r (fun ω ↦ τ (fun t ↦ T (ω t))) ω
          ∂markovChainMeasure P x) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) (fun ω ↦ τ (fun t ↦ T (ω t))) ω
          ∂markovChainMeasure P x)) := by
    intro τ hτ
    rw [integral_map hΦ.aemeasurable (p2m8e_meas a r hrm τ hτ).aestronglyMeasurable,
      integral_map hΦ.aemeasurable
        (p2m8e_meas a (fun _ ↦ 1) measurable_const τ hτ).aestronglyMeasurable]
    have hpt : ∀ ω : ℕ → S, discountedStoppedSum a r τ (fun t ↦ T (ω t)) =
        c * discountedStoppedSum a r (fun ω ↦ τ (fun t ↦ T (ω t))) ω := by
      intro ω
      unfold discountedStoppedSum
      rw [← tsum_mul_left]
      refine tsum_congr (fun t ↦ ?_)
      rw [hrT]
      split_ifs <;> ring
    have h1 : ∫ ω, discountedStoppedSum a r τ (fun t ↦ T (ω t)) ∂markovChainMeasure P x =
        c * ∫ ω, discountedStoppedSum a r (fun ω ↦ τ (fun t ↦ T (ω t))) ω
          ∂markovChainMeasure P x := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ hpt)
    have h2 : ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ (fun t ↦ T (ω t))
          ∂markovChainMeasure P x =
        ∫ ω, discountedStoppedSum a (fun _ ↦ 1) (fun ω ↦ τ (fun t ↦ T (ω t))) ω
          ∂markovChainMeasure P x := rfl
    rw [h1, h2, mul_div_assoc]
  have hS : {g | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      g = (∫ ω, discountedStoppedSum a r τ ω
          ∂((markovChainMeasure P x).map (fun ω t ↦ T (ω t)))) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω
          ∂((markovChainMeasure P x).map (fun ω t ↦ T (ω t))))} =
      c • {g | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧
        (∀ ω, 1 ≤ τ ω) ∧
        g = (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P x) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P x)} := by
    ext g
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨τ, hτ, hτ1, rfl⟩
      exact ⟨_, ⟨_, p2m8e_stop T hT τ hτ, fun ω ↦ hτ1 _, rfl⟩,
        by rw [smul_eq_mul]; exact (key τ hτ).symm⟩
    · rintro ⟨g₀, ⟨τ₀, hτ₀, hτ₀1, rfl⟩, rfl⟩
      refine ⟨fun ω ↦ τ₀ (fun t ↦ U (ω t)), p2m8e_stop U hU τ₀ hτ₀, fun ω ↦ hτ₀1 _, ?_⟩
      rw [key _ (p2m8e_stop U hU τ₀ hτ₀), smul_eq_mul]
      simp only [hUT]
  calc gittinsIndex P r a y
      = sSup {g | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
          g = (∫ ω, discountedStoppedSum a r τ ω
            ∂((markovChainMeasure P x).map (fun ω t ↦ T (ω t)))) /
          (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω
            ∂((markovChainMeasure P x).map (fun ω t ↦ T (ω t))))} := by
        rw [gittinsIndex, hnat]
    _ = _ := by rw [hS, Real.sSup_smul_of_nonneg hc, smul_eq_mul]; rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m8e_pred_scale (F : SamplingModel ℝ (ℝ × ℝ))
    (hlik : HasScaleParameter F.likelihood) (hprior : PriorHasScaleParameter F.prior)
    (xb n b : ℝ) (hb : 0 < b) :
    F.predictive (b * xb, n) = (F.predictive (xb, n)).map (b * ·) := by
  have hc : Measurable (b * · : ℝ → ℝ) := measurable_const_mul b
  ext s hs
  rw [Measure.map_apply hc hs]
  unfold SamplingModel.predictive
  rw [Kernel.comp_apply' _ _ _ hs, Kernel.comp_apply' _ _ _ (hc hs), hprior _ _ _ hb,
    lintegral_map (F.likelihood.measurable_coe hs) hc]
  refine lintegral_congr (fun θ ↦ ?_)
  rw [hlik _ _ hb, Measure.map_apply hc hs]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m8e_reward_scale (F : SamplingModel ℝ (ℝ × ℝ))
    (hlik : HasScaleParameter F.likelihood) (hprior : PriorHasScaleParameter F.prior)
    (xb n b : ℝ) (hb : 0 < b) :
    F.rewardOf (b * xb, n) = b * F.rewardOf (xb, n) := by
  unfold SamplingModel.rewardOf
  rw [p2m8e_pred_scale F hlik hprior xb n b hb, integral_map (measurable_const_mul b).aemeasurable
    (f := fun x : ℝ ↦ x) measurable_id.aestronglyMeasurable]
  exact integral_const_mul b (fun x : ℝ ↦ x)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
theorem solution (F : SamplingModel ℝ (ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2})
    (hlik : HasScaleParameter F.likelihood) (hprior : PriorHasScaleParameter F.prior)
    (hupd : F.update = meanUpdate) (hmean : ∀ p, Integrable (fun x : ℝ ↦ x) (F.predictive p))
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hint : DiscountedRewardIntegrable F.rewardChain F.rewardOf a) (xb n : ℝ) (hn : 0 < n) (hxb : 0 < xb) :
    (∀ b : ℝ, 0 < b → F.rewardOf (b * xb, n) = b * F.rewardOf (xb, n)) ∧
    gittinsIndex F.rewardChain F.rewardOf a (xb, n) =
      xb * gittinsIndex F.rewardChain F.rewardOf a (1, n) := by
  refine ⟨fun b hb ↦ p2m8e_reward_scale F hlik hprior xb n b hb, ?_⟩
  have hr : ∀ p : ℝ × ℝ, F.rewardOf ((fun p : ℝ × ℝ ↦ (xb * p.1, p.2)) p) = xb * F.rewardOf p := by
    intro p
    have := p2m8e_reward_scale F hlik hprior p.1 p.2 xb hxb
    rwa [Prod.mk.eta] at this
  have hrm : Measurable F.rewardOf :=
    (StronglyMeasurable.integral_kernel (κ := F.predictive) stronglyMeasurable_id).measurable
  have hmu : ∀ p : ℝ × ℝ, Measurable (meanUpdate p) := fun p ↦ by
    unfold meanUpdate; fun_prop
  have hTm : Measurable (fun p : ℝ × ℝ ↦ (xb * p.1, p.2)) := by fun_prop
  have hPA : ∀ y ∈ (Set.univ : Set (ℝ × ℝ)), F.rewardChain y (Set.univ : Set (ℝ × ℝ))ᶜ = 0 := by
    intro y _
    simp
  have hPT : ∀ y ∈ (Set.univ : Set (ℝ × ℝ)),
      F.rewardChain ((fun p : ℝ × ℝ ↦ (xb * p.1, p.2)) y) =
        (F.rewardChain y).map (fun p : ℝ × ℝ ↦ (xb * p.1, p.2)) := by
    intro y _
    obtain ⟨y1, y2⟩ := y
    show F.rewardChain (xb * y1, y2) = _
    rw [p2m8e_chain_apply, p2m8e_chain_apply, hupd, p2m8e_pred_scale F hlik hprior y1 y2 xb hxb,
      Measure.map_map (hmu _) (measurable_const_mul xb), Measure.map_map hTm (hmu _)]
    congr 1
    funext z
    simp only [Function.comp, meanUpdate, Prod.mk.injEq, and_true]
    ring
  have hnat0 := p2m8e_natural F.rewardChain (fun p : ℝ × ℝ ↦ (xb * p.1, p.2)) hTm
    Set.univ MeasurableSet.univ hPA hPT ((1 : ℝ), n) (Set.mem_univ _)
  have hnat : markovChainMeasure F.rewardChain (xb, n) =
      (markovChainMeasure F.rewardChain ((1 : ℝ), n)).map
        (fun ω t ↦ (fun p : ℝ × ℝ ↦ (xb * p.1, p.2)) (ω t)) := by
    rw [← hnat0]
    simp
  exact p2m8e_gittins_scale F.rewardChain F.rewardOf hrm a
    (fun p : ℝ × ℝ ↦ (xb * p.1, p.2)) (fun p : ℝ × ℝ ↦ (xb⁻¹ * p.1, p.2)) hTm (by fun_prop)
    (fun y ↦ by simp [hxb.ne']) xb hxb.le hr ((1 : ℝ), n) (xb, n) hnat
