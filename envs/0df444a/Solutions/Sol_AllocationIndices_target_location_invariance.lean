-- Prove2me | solution 1 for AllocationIndices.target_location_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T10:32:14.357559+00:00
-- url     : https://prove2.me/submissions/8753dec4-e657-4e75-843a-f4e49c4f9391

import Mathlib
import Definitions.Def_AllocationIndices_Sampling

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mdb_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mdb_marg0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : (markovChainMeasure P x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

open MeasureTheory ProbabilityTheory in
private lemma p2mdb_ext {S : Type*} [MeasurableSpace S] (μ ν : Measure (ℕ → S))
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
private lemma p2mdb_map_compProd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (m : Measure α) [SFinite m] (κ κ' : Kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel κ']
    (f : α → α) (hf : Measurable f) (g : β → β) (hg : Measurable g)
    (h : ∀ᵐ y ∂m, κ (f y) = (κ' y).map g) :
    (m.map f) ⊗ₘ κ = (m ⊗ₘ κ').map (Prod.map f g) := by
  ext s hs
  rw [Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf,
    Measure.map_apply (hf.prodMap hg) hs, Measure.compProd_apply ((hf.prodMap hg) hs)]
  refine lintegral_congr_ae (h.mono fun y hy ↦ ?_)
  dsimp only
  rw [hy, Measure.map_apply hg (measurable_prodMk_left hs)]
  rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mdb_natural {S : Type*} [MeasurableSpace S] (P Q : Kernel S S)
    [IsMarkovKernel P] [IsMarkovKernel Q]
    (T : S → S) (hT : Measurable T) (A : Set S) (hA : MeasurableSet A)
    (hPA : ∀ y ∈ A, P y Aᶜ = 0) (hPT : ∀ y ∈ A, Q (T y) = (P y).map T) (x : S) (hx : x ∈ A) :
    markovChainMeasure Q (T x) = (markovChainMeasure P x).map (fun ω n ↦ T (ω n)) := by
  have := p2mdb_prob P x
  have := p2mdb_prob Q (T x)
  have hΦ : Measurable (fun (ω : ℕ → S) n ↦ T (ω n)) :=
    measurable_pi_lambda _ (fun n ↦ hT.comp (measurable_pi_apply n))
  have hTt : ∀ a : ℕ, Measurable (fun (h : Finset.Iic a → S) i ↦ T (h i)) := fun a ↦
    measurable_pi_lambda _ (fun i ↦ hT.comp (measurable_pi_apply i))
  have F1 : ∀ (R : Kernel S S) [IsMarkovKernel R] (z : S) (a : ℕ),
      (markovChainMeasure R z).map (Preorder.frestrictLe a) ⊗ₘ markovChainStep R a =
      (markovChainMeasure R z).map (fun ω ↦ (Preorder.frestrictLe a ω, ω (a + 1))) :=
    fun R _ z a ↦ Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
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
  have hsplit : ∀ (R : Kernel S S) [IsMarkovKernel R] (z : S) (a : ℕ),
      (markovChainMeasure R z).map (Preorder.frestrictLe (a + 1)) =
      ((markovChainMeasure R z).map (Preorder.frestrictLe a) ⊗ₘ markovChainStep R a).map
        (G a) := by
    intro R _ z a
    have := p2mdb_prob R z
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
        rw [p2mdb_marg0]
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
  have hm : ∀ a : ℕ, (markovChainMeasure Q (T x)).map (Preorder.frestrictLe a) =
      ((markovChainMeasure P x).map (Preorder.frestrictLe a)).map (fun h i ↦ T (h i)) := by
    intro a
    induction a with
    | zero =>
      rw [p2mdb_marg0, p2mdb_marg0, Measure.map_dirac' (hTt 0)]
    | succ a ih =>
      have ih' : ∀ᵐ h ∂((markovChainMeasure P x).map (Preorder.frestrictLe a)),
          (h : Finset.Iic a → S) ⟨a, Finset.mem_Iic.2 le_rfl⟩ ∈ A := by
        have hpa : MeasurableSet
            {h : Finset.Iic a → S | h ⟨a, Finset.mem_Iic.2 le_rfl⟩ ∈ A} :=
          (measurable_pi_apply (X := fun _ : Finset.Iic a ↦ S)
            ⟨a, Finset.mem_Iic.2 le_rfl⟩) hA
        exact (ae_map_iff (Preorder.measurable_frestrictLe a).aemeasurable hpa).2 (hae a)
      rw [hsplit Q (T x) a, hsplit P x a, ih,
        p2mdb_map_compProd _ (markovChainStep Q a) (markovChainStep P a) _ (hTt a) T hT
          (ih'.mono fun h hh ↦ hPT _ hh),
        Measure.map_map (hG a) (by fun_prop), Measure.map_map (hTt (a + 1)) (hG a)]
      congr 1
      funext p
      exact hGT a p
  refine p2mdb_ext _ _ (fun a ↦ ?_)
  rw [hm a, Measure.map_map (Preorder.measurable_frestrictLe a) hΦ,
    Measure.map_map (hTt a) (Preorder.measurable_frestrictLe a)]
  rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mdb_stop {S : Type*} [MeasurableSpace S] (T : S → S) (hT : Measurable T)
    (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    IsTrajStoppingTime (fun ω ↦ τ (fun n ↦ T (ω n))) := by
  intro n
  obtain ⟨s, hs, hse⟩ := hτ n
  refine ⟨(fun (h : Finset.Iic n → S) i ↦ T (h i)) ⁻¹' s,
    (measurable_pi_lambda _ (fun i ↦ hT.comp (measurable_pi_apply i))) hs, ?_⟩
  ext ω
  exact Set.ext_iff.1 hse (fun n ↦ T (ω n))

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mdb_meas_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
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
private lemma p2mdb_meas {S : Type*} [MeasurableSpace S] (a : ℝ) (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum a f τ) := by
  unfold discountedStoppedSum
  exact Measurable.tsum fun t ↦ Measurable.ite (p2mdb_meas_lt τ hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t))) measurable_const

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2mdb_gittins_eq {S : Type*} [MeasurableSpace S] (P Q : Kernel S S)
    [IsMarkovKernel P] [IsMarkovKernel Q] (r r' : S → ℝ) (hr' : Measurable r') (a : ℝ)
    (T U : S → S) (hT : Measurable T) (hU : Measurable U) (hUT : ∀ y, U (T y) = y)
    (hrT : ∀ y, r' (T y) = r y) (x y : S)
    (hnat : markovChainMeasure Q y = (markovChainMeasure P x).map (fun ω t ↦ T (ω t))) :
    gittinsIndex Q r' a y = gittinsIndex P r a x := by
  have hΦ : Measurable (fun (ω : ℕ → S) t ↦ T (ω t)) :=
    measurable_pi_lambda _ (fun t ↦ hT.comp (measurable_pi_apply t))
  have key : ∀ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ →
      (∫ ω, discountedStoppedSum a r' τ ω
          ∂((markovChainMeasure P x).map (fun ω t ↦ T (ω t)))) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω
          ∂((markovChainMeasure P x).map (fun ω t ↦ T (ω t)))) =
      (∫ ω, discountedStoppedSum a r (fun ω ↦ τ (fun t ↦ T (ω t))) ω
          ∂markovChainMeasure P x) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) (fun ω ↦ τ (fun t ↦ T (ω t))) ω
          ∂markovChainMeasure P x) := by
    intro τ hτ
    rw [integral_map hΦ.aemeasurable (p2mdb_meas a r' hr' τ hτ).aestronglyMeasurable,
      integral_map hΦ.aemeasurable
        (p2mdb_meas a (fun _ ↦ 1) measurable_const τ hτ).aestronglyMeasurable]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    simp only [discountedStoppedSum, hrT]
  rw [gittinsIndex, gittinsIndex, hnat]
  congr 1
  ext g
  constructor
  · rintro ⟨τ, hτ, hτ1, rfl⟩
    exact ⟨_, p2mdb_stop T hT τ hτ, fun ω ↦ hτ1 _, key τ hτ⟩
  · rintro ⟨τ₀, hτ₀, hτ₀1, rfl⟩
    refine ⟨fun ω ↦ τ₀ (fun t ↦ U (ω t)), p2mdb_stop U hU τ₀ hτ₀, fun ω ↦ hτ₀1 _, ?_⟩
    rw [key _ (p2mdb_stop U hU τ₀ hτ₀)]
    simp only [hUT]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2mdb_pred_shift (F : SamplingModel ℝ (ℝ × ℝ))
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
private lemma p2mdb_step_apply {Θ Q : Type*} [MeasurableSpace Θ] [MeasurableSpace Q]
    (F : SamplingModel Θ Q) (T : ℝ) (p : Q) :
    F.targetChain T (Sum.inl p) = (F.predictive p).map
      (fun x ↦ if T ≤ x then (Sum.inr () : Q ⊕ Unit) else Sum.inl (F.update p x)) := by
  show F.targetStep T p = _
  rw [SamplingModel.targetStep, Kernel.map_apply _ (F.measurable_targetStepFun T),
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map (F.measurable_targetStepFun T) measurable_prodMk_left]
  rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
theorem solution (F : SamplingModel ℝ (ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2})
    (hlik : HasLocationParameter F.likelihood) (hprior : PriorHasLocationParameter F.prior)
    (hupd : F.update = meanUpdate) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (xb n T : ℝ)
    (hn : 0 < n) :
    gittinsIndex (F.targetChain T) (F.targetReward T) a (Sum.inl (xb, n)) =
      gittinsIndex (F.targetChain 0) (F.targetReward 0) a (Sum.inl (xb - T, n)) := by
  let sh : ℝ → ℝ × ℝ → ℝ × ℝ := fun c p ↦ (p.1 - c, p.2)
  let Tm : (ℝ × ℝ) ⊕ Unit → (ℝ × ℝ) ⊕ Unit := Sum.map (sh T) id
  let Um : (ℝ × ℝ) ⊕ Unit → (ℝ × ℝ) ⊕ Unit := Sum.map (sh (-T)) id
  have hsh : ∀ c, Measurable (sh c) := fun c ↦ by fun_prop
  have hTm : Measurable Tm := (hsh T).sumMap measurable_id
  have hUm : Measurable Um := (hsh (-T)).sumMap measurable_id
  have hUT : ∀ y, Um (Tm y) = y := by
    rintro (p | u)
    · simp [Tm, Um, sh]
    · rfl
  let f : (ℝ × ℝ) ⊕ Unit → ℝ := Sum.elim (fun p ↦ p.2) (fun _ ↦ 1)
  have hf : Measurable f := measurable_snd.sumElim measurable_const
  let A : Set ((ℝ × ℝ) ⊕ Unit) := f ⁻¹' Set.Ioi 0
  have hA : MeasurableSet A := hf measurableSet_Ioi
  have hAl : ∀ p : ℝ × ℝ, Sum.inl p ∈ A ↔ 0 < p.2 := fun p ↦ Iff.rfl
  have hAr : ∀ u : Unit, Sum.inr u ∈ A := fun u ↦ show (0 : ℝ) < 1 from one_pos
  have hmu : ∀ p : ℝ × ℝ, Measurable (meanUpdate p) := fun p ↦ by
    unfold meanUpdate; fun_prop
  have hstepm : ∀ (c : ℝ) (p : ℝ × ℝ), Measurable
      (fun x ↦ if c ≤ x then (Sum.inr () : (ℝ × ℝ) ⊕ Unit) else Sum.inl (F.update p x)) :=
    fun c p ↦ (F.measurable_targetStepFun c).comp measurable_prodMk_left
  have hPA : ∀ y ∈ A, F.targetChain T y Aᶜ = 0 := by
    rintro (p | u) hy
    · have hp : 0 < p.2 := (hAl p).1 hy
      rw [p2mdb_step_apply, Measure.map_apply (hstepm T p) hA.compl]
      have : (fun x ↦ if T ≤ x then (Sum.inr () : (ℝ × ℝ) ⊕ Unit)
          else Sum.inl (F.update p x)) ⁻¹' Aᶜ = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
          not_not]
        split_ifs
        · exact hAr ()
        · rw [hAl, hupd]
          simp only [meanUpdate]
          linarith
      rw [this, measure_empty]
    · show (Measure.dirac (Sum.inr () : (ℝ × ℝ) ⊕ Unit)) Aᶜ = 0
      rw [Measure.dirac_apply' _ hA.compl]
      simp [hAr]
  have hPT : ∀ y ∈ A, F.targetChain 0 (Tm y) = (F.targetChain T y).map Tm := by
    rintro (p | u) hy
    · obtain ⟨y1, y2⟩ := p
      have hp : 0 < y2 := (hAl _).1 hy
      show F.targetChain 0 (Sum.inl (y1 - T, y2)) = _
      have hps := p2mdb_pred_shift F hlik hprior y1 y2 (-T)
      rw [← sub_eq_add_neg] at hps
      rw [p2mdb_step_apply, p2mdb_step_apply, hps,
        Measure.map_map (hstepm 0 _) (measurable_add_const (-T)),
        Measure.map_map hTm (hstepm T _)]
      congr 1
      funext x
      simp only [Function.comp]
      by_cases hx : T ≤ x
      · have hx' : (0 : ℝ) ≤ x + -T := by linarith
        simp [hx, hx', Tm]
      · have hx' : ¬ (0 : ℝ) ≤ x + -T := by intro h; exact hx (by linarith)
        simp only [hx, hx', if_false, Tm, Sum.map_inl, hupd, meanUpdate, sh,
          Sum.inl.injEq, Prod.mk.injEq, and_true]
        have : y2 + 1 ≠ 0 := by linarith
        field_simp
        ring
    · show (Measure.dirac (Sum.inr () : (ℝ × ℝ) ⊕ Unit)) =
        (Measure.dirac (Sum.inr () : (ℝ × ℝ) ⊕ Unit)).map Tm
      rw [Measure.map_dirac' hTm]
      rfl
  have hx : (Sum.inl (xb, n) : (ℝ × ℝ) ⊕ Unit) ∈ A := (hAl _).2 hn
  have hnat := p2mdb_natural (F.targetChain T) (F.targetChain 0) Tm hTm A hA hPA hPT _ hx
  have hr0 : Measurable (F.targetReward 0) := by
    unfold SamplingModel.targetReward
    exact ((F.predictive.measurable_coe measurableSet_Ici).ennreal_toReal).sumElim
      measurable_const
  have hrT : ∀ y, F.targetReward 0 (Tm y) = F.targetReward T y := by
    rintro (⟨y1, y2⟩ | u)
    · show (F.predictive (y1 - T, y2) (Set.Ici 0)).toReal =
        (F.predictive (y1, y2) (Set.Ici T)).toReal
      have hps := p2mdb_pred_shift F hlik hprior y1 y2 (-T)
      rw [← sub_eq_add_neg] at hps
      rw [hps, Measure.map_apply (measurable_add_const (-T)) measurableSet_Ici]
      congr 2
      ext x
      simp only [Set.mem_preimage, Set.mem_Ici]
      constructor <;> intro h <;> linarith
    · rfl
  exact (p2mdb_gittins_eq (F.targetChain T) (F.targetChain 0) (F.targetReward T)
    (F.targetReward 0) hr0 a Tm Um hTm hUm hUT hrT _ _ hnat).symm
