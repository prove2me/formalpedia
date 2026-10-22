-- Prove2me | solution 1 for AllocationIndices.Targets.location_scale_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:32:51.62177+00:00
-- url     : https://prove2.me/submissions/a99f5e36-c20d-4c8b-bc85-2e06a9bd4258

import Definitions.Def_AllocationIndices_Targets_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm
open AllocationIndices AllocationIndices.Targets

section G70ALT
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma g70al_cp_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] (ρ : Measure A)
    [SFinite ρ] (κ : Kernel A X) [IsSFiniteKernel κ] (η : Kernel B Y) [IsSFiniteKernel η]
    (f : A → B) (hf : Measurable f) (g : X → Y) (hg : Measurable g)
    (h : ∀ᵐ z ∂ρ, η (f z) = (κ z).map g) :
    (ρ ⊗ₘ κ).map (Prod.map f g) = (ρ.map f) ⊗ₘ η := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap hg) hs, Measure.compProd_apply (hf.prodMap hg hs),
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with z hz
  rw [hz, Measure.map_apply hg (measurable_prodMk_left hs)]
  rfl

lemma g70al_marg0 (K : Kernel X X) [IsMarkovKernel K] (x : X) :
    (markovChainMeasure K x).map (Preorder.frestrictLe (π := fun _ : ℕ => X) 0) =
      Measure.dirac (fun _ => x) := by
  unfold markovChainMeasure Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe, Kernel.partialTraj_self,
    Measure.id_comp]
  ext s hs
  rw [Measure.map_apply (MeasurableEquiv.measurable _) hs,
    Measure.dirac_apply' _ (MeasurableEquiv.measurable _ hs), Measure.dirac_apply' _ hs]
  rfl


def g70al_J (a : ℕ) (p : (Π _i : Finset.Iic a, X) × X) : Π _i : Finset.Iic (a + 1), X :=
  fun i => if h : i.1 ≤ a then p.1 ⟨i.1, Finset.mem_Iic.2 h⟩ else p.2

lemma g70al_J_meas (a : ℕ) : Measurable (g70al_J (X := X) a) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i.1 ≤ a
  · simp only [g70al_J, dif_pos h]; exact (measurable_pi_apply _).comp measurable_fst
  · simp only [g70al_J, dif_neg h]; exact measurable_snd

lemma g70al_step (K : Kernel X X) [IsMarkovKernel K] (x : X) (a : ℕ) :
    (markovChainMeasure K x).map (Preorder.frestrictLe (π := fun _ : ℕ => X) (a + 1)) =
      ((markovChainMeasure K x).map (Preorder.frestrictLe (π := fun _ : ℕ => X) a) ⊗ₘ
        markovChainStep K a).map (g70al_J a) := by
  unfold markovChainMeasure
  rw [Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure, Measure.map_map
    (g70al_J_meas a) (by fun_prop)]
  congr 1
  funext ω i
  simp only [Function.comp, g70al_J]
  split_ifs with h
  · rfl
  · have : i.1 = a + 1 := by have := Finset.mem_Iic.1 i.2; omega
    simp [this]

lemma g70al_invG (K1 : Kernel X X) [IsMarkovKernel K1] (G : Set X) (hGm : MeasurableSet G)
    (hG : ∀ x ∈ G, K1 x Gᶜ = 0) (x : X) (hx : x ∈ G) (a : ℕ) :
    ∀ᵐ ω ∂markovChainMeasure K1 x, ω a ∈ G := by
  haveI : ∀ y, IsProbabilityMeasure (markovChainMeasure K1 y) := fun y => by
    unfold markovChainMeasure; infer_instance
  induction a with
  | zero =>
    have h0 : ∀ᵐ z ∂(markovChainMeasure K1 x).map (Preorder.frestrictLe (π := fun _ : ℕ => X) 0),
        z ⟨0, Finset.mem_Iic.2 le_rfl⟩ ∈ G := by
      rw [g70al_marg0, ae_dirac_iff (hGm.preimage (measurable_pi_apply _))]; exact hx
    exact ae_of_ae_map (f := Preorder.frestrictLe (π := fun _ : ℕ => X) 0) (by fun_prop) h0
  | succ a ih =>
    have hc := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => X) (μ₀ := Measure.dirac x) (κ := markovChainStep K1) (a := a)
    have h1 : ∀ᵐ p ∂((Kernel.trajMeasure (Measure.dirac x) (markovChainStep K1)).map
        (Preorder.frestrictLe (π := fun _ : ℕ => X) a) ⊗ₘ markovChainStep K1 a), p.2 ∈ G := by
      apply Measure.ae_compProd_of_ae_ae (hGm.preimage measurable_snd)
      have ih' : ∀ᵐ z ∂(Kernel.trajMeasure (Measure.dirac x) (markovChainStep K1)).map
          (Preorder.frestrictLe (π := fun _ : ℕ => X) a), z ⟨a, Finset.mem_Iic.2 le_rfl⟩ ∈ G := by
        rw [ae_map_iff (by fun_prop) (hGm.preimage (measurable_pi_apply _))]
        exact ih
      filter_upwards [ih'] with z hz
      simp only [markovChainStep, Kernel.comap_apply]
      rw [ae_iff]
      exact hG _ hz
    rw [hc, ae_map_iff (by fun_prop) (hGm.preimage measurable_snd)] at h1
    exact h1

lemma g70al_mc_mapG (K1 : Kernel X X) [IsMarkovKernel K1] (K2 : Kernel Y Y) [IsMarkovKernel K2]
    (e : X → Y) (he : Measurable e) (G : Set X) (hGm : MeasurableSet G)
    (hG : ∀ x ∈ G, K1 x Gᶜ = 0) (hK : ∀ x ∈ G, K2 (e x) = (K1 x).map e) (x : X) (hx : x ∈ G) :
    markovChainMeasure K2 (e x) = (markovChainMeasure K1 x).map (fun ω n => e (ω n)) := by
  have hΦ : Measurable (fun (ω : ℕ → X) n => e (ω n)) :=
    measurable_pi_lambda _ fun n => he.comp (measurable_pi_apply n)
  have hΦa : ∀ a : ℕ, Measurable (fun (z : Π _i : Finset.Iic a, X) (i : Finset.Iic a) => e (z i)) :=
    fun a => measurable_pi_lambda _ fun n => he.comp (measurable_pi_apply n)
  haveI : ∀ y, IsProbabilityMeasure (markovChainMeasure K2 y) := fun y => by
    unfold markovChainMeasure; infer_instance
  haveI : ∀ y, IsProbabilityMeasure (markovChainMeasure K1 y) := fun y => by
    unfold markovChainMeasure; infer_instance
  have hm : ∀ a : ℕ, (markovChainMeasure K2 (e x)).map
      (Preorder.frestrictLe (π := fun _ : ℕ => Y) a) =
      ((markovChainMeasure K1 x).map (Preorder.frestrictLe (π := fun _ : ℕ => X) a)).map
        (fun z i => e (z i)) := by
    intro a
    induction a with
    | zero =>
      rw [g70al_marg0, g70al_marg0]
      ext s hs
      rw [Measure.map_apply (hΦa 0) hs, Measure.dirac_apply' _ (hΦa 0 hs), Measure.dirac_apply' _ hs]
      rfl
    | succ a ih =>
      rw [g70al_step, g70al_step, ih, Measure.map_map (hΦa _) (g70al_J_meas a),
        ← g70al_cp_map _ (markovChainStep K1 a) (markovChainStep K2 a) _ (hΦa a) e he, Measure.map_map (g70al_J_meas a) ((hΦa a).prodMap he)]
      · congr 1
        funext p i
        simp only [Function.comp, g70al_J, Prod.map]
        split_ifs <;> rfl
      · have hinv := g70al_invG K1 G hGm hG x hx a
        have h' : ∀ᵐ z ∂(markovChainMeasure K1 x).map (Preorder.frestrictLe (π := fun _ : ℕ => X) a),
            z ⟨a, Finset.mem_Iic.2 le_rfl⟩ ∈ G := by
          rw [ae_map_iff (by fun_prop) (hGm.preimage (measurable_pi_apply _))]
          exact hinv
        filter_upwards [h'] with z hz
        simp only [markovChainStep, Kernel.comap_apply]
        exact hK _ hz
  have hproj : IsProjectiveMeasureFamily (fun I : Finset ℕ =>
      (markovChainMeasure K2 (e x)).map (fun ω => I.restrict ω)) := by
    intro I J hJI
    simp only
    rw [Measure.map_map (Finset.measurable_restrict₂ _) (Finset.measurable_restrict _)]; rfl
  have h2 : IsProjectiveLimit (markovChainMeasure K2 (e x))
      (fun I => (markovChainMeasure K2 (e x)).map (fun ω => I.restrict ω)) :=
    fun I => rfl
  have h1 : IsProjectiveLimit ((markovChainMeasure K1 x).map (fun ω n => e (ω n)))
      (fun I => (markovChainMeasure K2 (e x)).map (fun ω => I.restrict ω)) := by
    rw [isProjectiveLimit_nat_iff hproj]
    intro n
    have := hm n
    rw [Measure.map_map (by fun_prop) hΦ]
    change _ = (markovChainMeasure K2 (e x)).map (Preorder.frestrictLe (π := fun _ : ℕ => Y) n)
    rw [this, Measure.map_map (hΦa n) (by fun_prop)]
    rfl
  exact (h1.unique h2).symm


lemma g70al_mc_map (K1 : Kernel X X) [IsMarkovKernel K1] (K2 : Kernel Y Y) [IsMarkovKernel K2]
    (e : X → Y) (he : Measurable e) (hK : ∀ x, K2 (e x) = (K1 x).map e) (x : X) :
    markovChainMeasure K2 (e x) = (markovChainMeasure K1 x).map (fun ω n => e (ω n)) :=
  g70al_mc_mapG K1 K2 e he Set.univ MeasurableSet.univ (fun _ _ => by simp) (fun x _ => hK x) x trivial

lemma g70al_stop_comp (E : X → Y) (hE : Measurable E) (τ : (ℕ → Y) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) :
    IsTrajStoppingTime (fun ω : ℕ → X => τ (fun n => E (ω n))) := by
  intro n
  obtain ⟨B, hB, hBeq⟩ := (MeasurableSpace.measurableSet_comap).1 (hτ n)
  refine (MeasurableSpace.measurableSet_comap).2
    ⟨(fun (z : Π _i : Finset.Iic n, X) i => E (z i)) ⁻¹' B,
      (measurable_pi_lambda _ fun i => hE.comp (measurable_pi_apply i)) hB, ?_⟩
  ext ω
  have := congrArg (fun A : Set (ℕ → Y) => (fun k => E (ω k)) ∈ A) hBeq
  simpa using this

lemma g70al_int_map (E : X ≃ᵐ Y) (μ : Measure (ℕ → X)) (h : (ℕ → Y) → ℝ) :
    ∫ ω, h ω ∂(μ.map (fun ω n => E (ω n))) = ∫ ω, h (fun n => E (ω n)) ∂μ :=
  (MeasurableEquiv.piCongrRight (fun _ : ℕ => E)).measurableEmbedding.integral_map h

lemma g70al_gittins_transport (K1 : Kernel X X) [IsMarkovKernel K1] (K2 : Kernel Y Y)
    [IsMarkovKernel K2] (E : X ≃ᵐ Y) (r : Y → ℝ) (a : ℝ) (x : X)
    (hmc : markovChainMeasure K2 (E x) = (markovChainMeasure K1 x).map (fun ω n => E (ω n))) :
    gittinsIndex K2 r a (E x) = gittinsIndex K1 (fun z => r (E z)) a x := by
  unfold gittinsIndex
  rw [hmc]
  congr 1; ext g
  simp only [Set.mem_setOf_eq, g70al_int_map]
  constructor
  · rintro ⟨τ, hτ, h1, rfl⟩
    exact ⟨_, g70al_stop_comp E E.measurable τ hτ, fun ω => h1 _, rfl⟩
  · rintro ⟨τ, hτ, h1, rfl⟩
    refine ⟨_, g70al_stop_comp E.symm E.symm.measurable τ hτ, fun ω => h1 _, ?_⟩
    unfold discountedStoppedSum
    simp only [MeasurableEquiv.symm_apply_apply]

lemma g70al_cost_transport (K1 : Kernel X X) [IsMarkovKernel K1] (K2 : Kernel Y Y)
    [IsMarkovKernel K2] (E : X ≃ᵐ Y) (L1 : X → Bool)
    (L2 : Y → Bool) (hL : ∀ z, L2 (E z) = L1 z) (c : ENNReal) (x : X)
    (hmc : markovChainMeasure K2 (E x) = (markovChainMeasure K1 x).map (fun ω n => E (ω n))) :
    (⨅ τ : {τ : (ℕ → Y) → ℕ∞ // IsTrajStoppingTime τ},
      (∫⁻ ω, ∑' t : ℕ, (if (t : ℕ∞) < τ.1 ω ∧ L2 (ω t) then (1 : ENNReal) else 0)
        ∂markovChainMeasure K2 (E x)) +
      c * markovChainMeasure K2 (E x) {ω | ∃ m : ℕ, τ.1 ω = (m : ℕ∞) ∧ L2 (ω m)}) =
    (⨅ τ : {τ : (ℕ → X) → ℕ∞ // IsTrajStoppingTime τ},
      (∫⁻ ω, ∑' t : ℕ, (if (t : ℕ∞) < τ.1 ω ∧ L1 (ω t) then (1 : ENNReal) else 0)
        ∂markovChainMeasure K1 x) +
      c * markovChainMeasure K1 x {ω | ∃ m : ℕ, τ.1 ω = (m : ℕ∞) ∧ L1 (ω m)}) := by
  rw [hmc]
  set Φ := MeasurableEquiv.piCongrRight (fun _ : ℕ => E)
  have hmap : (markovChainMeasure K1 x).map (fun ω n => E (ω n)) = (markovChainMeasure K1 x).map Φ := rfl
  rw [hmap]
  have hΦ : ∀ ω t, Φ ω t = E (ω t) := fun _ _ => rfl
  have hval : ∀ τ : (ℕ → Y) → ℕ∞,
      (∫⁻ ω, ∑' t : ℕ, (if (t : ℕ∞) < τ ω ∧ L2 (ω t) then (1 : ENNReal) else 0)
        ∂(markovChainMeasure K1 x).map Φ) +
      c * ((markovChainMeasure K1 x).map Φ) {ω | ∃ m : ℕ, τ ω = (m : ℕ∞) ∧ L2 (ω m)} =
      (∫⁻ ω, ∑' t : ℕ, (if (t : ℕ∞) < τ (Φ ω) ∧ L1 (ω t) then (1 : ENNReal) else 0)
        ∂markovChainMeasure K1 x) +
      c * markovChainMeasure K1 x {ω | ∃ m : ℕ, τ (Φ ω) = (m : ℕ∞) ∧ L1 (ω m)} := by
    intro τ
    rw [lintegral_map_equiv, MeasurableEquiv.map_apply]
    simp only [Set.preimage_setOf_eq, hΦ, hL]
  apply le_antisymm
  · refine le_iInf fun τ => ?_
    refine (iInf_le _ ⟨fun ω => τ.1 (Φ.symm ω), g70al_stop_comp E.symm E.symm.measurable τ.1 τ.2⟩).trans ?_
    rw [hval]
    simp only [MeasurableEquiv.symm_apply_apply]
    exact le_rfl
  · refine le_iInf fun τ => ?_
    refine (iInf_le _ ⟨fun ω => τ.1 (Φ ω), g70al_stop_comp E E.measurable τ.1 τ.2⟩).trans ?_
    rw [hval]


end G70ALT

section G70ALS
variable {Θ Q : Type*} [MeasurableSpace Θ] [MeasurableSpace Q]

lemma g70al_targetStep_eq (F : SamplingModel Θ Q) (T : ℝ) (q : Q) :
    F.targetStep T q = (F.predictive q).map
      (fun x => if T ≤ x then (Sum.inr () : Q ⊕ Unit) else Sum.inl (F.update q x)) := by
  unfold SamplingModel.targetStep
  rw [Kernel.map_apply _ (F.measurable_targetStepFun T), Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map (F.measurable_targetStepFun T) measurable_prodMk_left]
  rfl

/-- generic chain equivariance for the target chain under a parameter map `ψ`. -/
lemma g70al_chain_equiv (F : SamplingModel Θ Q) (T T' : ℝ) (ψ : Q ≃ᵐ Q) (g : ℝ → ℝ)
    (hg : Measurable g)
    (hpred : ∀ q, F.predictive (ψ q) = (F.predictive q).map g)
    (hT : ∀ x, T' ≤ g x ↔ T ≤ x) (hup : ∀ q x, F.update (ψ q) (g x) = ψ (F.update q x))
    (z : Q ⊕ Unit) :
    F.targetChain T' (MeasurableEquiv.sumCongr ψ (MeasurableEquiv.refl Unit) z) =
      (F.targetChain T z).map (MeasurableEquiv.sumCongr ψ (MeasurableEquiv.refl Unit)) := by
  rcases z with q | u
  · change F.targetStep T' (ψ q) = (F.targetStep T q).map _
    rw [g70al_targetStep_eq, g70al_targetStep_eq, hpred, Measure.map_map _ hg,
      Measure.map_map (MeasurableEquiv.measurable _) _]
    · congr 1
      funext x
      simp only [Function.comp, hT, hup]
      split_ifs <;> rfl
    · exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
        (measurable_inl.comp (F.measurable_update.comp (measurable_const.prodMk measurable_id)))
    · exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
        (measurable_inl.comp (F.measurable_update.comp (measurable_const.prodMk measurable_id)))
  · change Measure.dirac (Sum.inr ()) = (Measure.dirac (Sum.inr ())).map _
    ext s hs
    rw [Measure.map_apply (MeasurableEquiv.measurable _) hs, Measure.dirac_apply' _ hs,
      Measure.dirac_apply' _ (MeasurableEquiv.measurable _ hs)]
    rfl

lemma g70al_reward_equiv (F : SamplingModel Θ Q) (T T' : ℝ) (ψ : Q ≃ᵐ Q) (g : ℝ → ℝ)
    (hg : Measurable g)
    (hpred : ∀ q, F.predictive (ψ q) = (F.predictive q).map g)
    (hT : ∀ x, T' ≤ g x ↔ T ≤ x) (z : Q ⊕ Unit) :
    F.targetReward T' (MeasurableEquiv.sumCongr ψ (MeasurableEquiv.refl Unit) z) =
      F.targetReward T z := by
  rcases z with q | u
  · change (F.predictive (ψ q) (Set.Ici T')).toReal = (F.predictive q (Set.Ici T)).toReal
    rw [hpred, Measure.map_apply hg measurableSet_Ici]
    congr 2
    ext x; simp [hT]
  · rfl


lemma g70al_chain_equivG (F : SamplingModel Θ Q) (T T' : ℝ) (ψ : Q ≃ᵐ Q) (g : ℝ → ℝ)
    (hg : Measurable g) (Gq : Set Q)
    (hpred : ∀ q, F.predictive (ψ q) = (F.predictive q).map g)
    (hT : ∀ x, T' ≤ g x ↔ T ≤ x) (hup : ∀ q ∈ Gq, ∀ x, F.update (ψ q) (g x) = ψ (F.update q x))
    (z : Q ⊕ Unit) (hz : z ∈ Sum.inl '' Gq ∪ Set.range Sum.inr) :
    F.targetChain T' (MeasurableEquiv.sumCongr ψ (MeasurableEquiv.refl Unit) z) =
      (F.targetChain T z).map (MeasurableEquiv.sumCongr ψ (MeasurableEquiv.refl Unit)) := by
  rcases z with q | u
  · have hq : q ∈ Gq := by
      rcases hz with ⟨q', hq', he⟩ | ⟨u, hu⟩
      · cases he; exact hq'
      · cases hu
    change F.targetStep T' (ψ q) = (F.targetStep T q).map _
    rw [g70al_targetStep_eq, g70al_targetStep_eq, hpred, Measure.map_map _ hg,
      Measure.map_map (MeasurableEquiv.measurable _) _]
    · congr 1
      funext x
      simp only [Function.comp, hT, hup q hq]
      split_ifs <;> rfl
    · exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
        (measurable_inl.comp (F.measurable_update.comp (measurable_const.prodMk measurable_id)))
    · exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
        (measurable_inl.comp (F.measurable_update.comp (measurable_const.prodMk measurable_id)))
  · change Measure.dirac (Sum.inr ()) = (Measure.dirac (Sum.inr ())).map _
    ext s hs
    rw [Measure.map_apply (MeasurableEquiv.measurable _) hs, Measure.dirac_apply' _ hs,
      Measure.dirac_apply' _ (MeasurableEquiv.measurable _ hs)]
    rfl

lemma g70al_chain_invG (F : SamplingModel Θ Q) (T : ℝ) (Gq : Set Q) (hGq : MeasurableSet Gq)
    (hupG : ∀ q ∈ Gq, ∀ x, F.update q x ∈ Gq) (z : Q ⊕ Unit)
    (hz : z ∈ Sum.inl '' Gq ∪ Set.range Sum.inr) :
    F.targetChain T z (Sum.inl '' Gq ∪ Set.range Sum.inr)ᶜ = 0 := by
  have hGm : MeasurableSet (Sum.inl '' Gq ∪ Set.range (Sum.inr : Unit → Q ⊕ Unit)) :=
    hGq.inl_image.union measurableSet_range_inr
  rcases z with q | u
  · have hq : q ∈ Gq := by
      rcases hz with ⟨q', hq', he⟩ | ⟨u, hu⟩
      · cases he; exact hq'
      · cases hu
    change F.targetStep T q _ = 0
    rw [g70al_targetStep_eq, Measure.map_apply _ hGm.compl]
    · convert measure_empty (μ := F.predictive q)
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_union, Set.mem_image,
        Set.mem_range, Set.mem_empty_iff_false, iff_false, not_not]
      split_ifs
      · exact Or.inr ⟨(), rfl⟩
      · exact Or.inl ⟨_, hupG q hq x, rfl⟩
    · exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
        (measurable_inl.comp (F.measurable_update.comp (measurable_const.prodMk measurable_id)))
  · change Measure.dirac (Sum.inr ()) _ = 0
    rw [Measure.dirac_apply' _ hGm.compl]
    simp

end G70ALS

section G70ALC
variable {X : Type*} [MeasurableSpace X]

lemma g70al_cfilt (n : ℕ) :
    trajectoryFiltration X n ≤ (inferInstance : MeasurableSpace (ℕ → X)) :=
  Measurable.comap_le (measurable_pi_lambda _ fun _ => measurable_pi_apply _)

lemma g70al_cτmeas (τ : (ℕ → X) → ℕ∞) (hτ : IsTrajStoppingTime τ) : Measurable τ := by
  have hle : ∀ k : ℕ, MeasurableSet {ω | τ ω ≤ (k : ℕ∞)} := fun k => g70al_cfilt k _ (hτ k)
  refine measurable_to_countable' fun m => ?_
  induction m using ENat.recTopCoe with
  | top =>
    have : τ ⁻¹' {⊤} = ⋂ k : ℕ, {ω | τ ω ≤ (k : ℕ∞)}ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff,
        Set.mem_setOf_eq]
      induction τ ω using ENat.recTopCoe with
      | top => simp
      | coe l => simp only [ENat.coe_ne_top, false_iff, not_forall, not_not]; exact ⟨l, le_rfl⟩
    rw [this]; exact MeasurableSet.iInter fun k => (hle k).compl
  | coe k =>
    have : τ ⁻¹' {(k : ℕ∞)} = {ω | τ ω ≤ (k : ℕ∞)} ∩
        ⋂ j ∈ Finset.range k, {ω | τ ω ≤ (j : ℕ∞)}ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_compl_iff, Set.mem_setOf_eq, Finset.mem_range]
      induction τ ω using ENat.recTopCoe with
      | top => simp
      | coe l =>
        simp only [Nat.cast_inj, Nat.cast_le]
        constructor
        · rintro rfl; exact ⟨le_rfl, fun j hj => by omega⟩
        · rintro ⟨h1, h2⟩; by_contra hne; exact h2 l (by omega) le_rfl
    rw [this]
    exact (hle k).inter (Finset.measurableSet_biInter _ fun j _ => (hle j).compl)

lemma g70al_cterm_meas (τ : (ℕ → X) → ℕ∞) (hτ : IsTrajStoppingTime τ) (a : ℝ) {g : X → ℝ}
    (hg : Measurable g) (t : ℕ) :
    Measurable (fun ω : ℕ → X => if (t : ℕ∞) < τ ω then a ^ t * g (ω t) else 0) := by
  have hs : MeasurableSet {ω : ℕ → X | (t : ℕ∞) < τ ω} := by
    have : {ω : ℕ → X | (t : ℕ∞) < τ ω} = {ω | τ ω ≤ (t : ℕ∞)}ᶜ := by ext ω; simp
    rw [this]; exact (g70al_cfilt t _ (hτ t)).compl
  exact Measurable.ite hs (measurable_const.mul (hg.comp (measurable_pi_apply t))) measurable_const

lemma g70al_cterm_bd (τ : (ℕ → X) → ℕ∞) {a : ℝ} (ha0 : 0 < a) (g : X → ℝ) (ω : ℕ → X) (t : ℕ) :
    ‖(if (t : ℕ∞) < τ ω then a ^ t * g (ω t) else 0)‖ ≤ a ^ t * |g (ω t)| := by
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos ha0 t)]
  · simp; positivity

lemma g70al_csumm_ae (K : Kernel X X) [IsMarkovKernel K] {r : X → ℝ} (hr : Measurable r) {a : ℝ}
    (ha0 : 0 < a) (hint : DiscountedRewardIntegrable K r a) (x : X) :
    ∀ᵐ ω ∂markovChainMeasure K x, Summable (fun t => a ^ t * |r (ω t)|) := by
  have hm : Measurable (fun ω : ℕ → X => ∑' t : ℕ, ENNReal.ofReal (a ^ t * |r (ω t)|)) :=
    Measurable.ennreal_tsum fun t => ENNReal.measurable_ofReal.comp
      (measurable_const.mul ((hr.comp (measurable_pi_apply t)).abs))
  filter_upwards [ae_lt_top hm (hint x).ne] with ω hω
  have := ENNReal.summable_toReal hω.ne
  refine this.congr fun t => ?_
  rw [ENNReal.toReal_ofReal (by positivity)]

lemma g70al_cdss_aesm (K : Kernel X X) [IsMarkovKernel K] (x : X) (τ : (ℕ → X) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) {a : ℝ} (ha0 : 0 < a) {g : X → ℝ} (hg : Measurable g)
    (hs : ∀ᵐ ω ∂markovChainMeasure K x, Summable (fun t => a ^ t * |g (ω t)|)) :
    AEStronglyMeasurable (discountedStoppedSum a g τ) (markovChainMeasure K x) := by
  refine aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop) (f := fun N ω => ∑ t ∈ Finset.range N,
      (if (t : ℕ∞) < τ ω then a ^ t * g (ω t) else 0))
    (fun N => (Finset.measurable_sum _ fun t _ => g70al_cterm_meas τ hτ a hg t).aestronglyMeasurable) ?_
  filter_upwards [hs] with ω hω
  exact (Summable.of_norm_bounded hω (g70al_cterm_bd τ ha0 g ω)).hasSum.tendsto_sum_nat

lemma g70al_cdss_enorm (τ : (ℕ → X) → ℕ∞) {a : ℝ} (ha0 : 0 < a) (g : X → ℝ) (ω : ℕ → X) :
    ‖discountedStoppedSum a g τ ω‖ₑ ≤ ∑' t : ℕ, ENNReal.ofReal (a ^ t * |g (ω t)|) := by
  by_cases h : Summable (fun t => a ^ t * |g (ω t)|)
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => by positivity) h, Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold discountedStoppedSum
    rw [← Real.norm_eq_abs]
    exact tsum_of_norm_bounded h.hasSum (g70al_cterm_bd τ ha0 g ω)
  · have : ∑' t : ℕ, ENNReal.ofReal (a ^ t * |g (ω t)|) = ⊤ := by
      by_contra hne
      exact h ((ENNReal.summable_toReal hne).congr fun t => ENNReal.toReal_ofReal (by positivity))
    rw [this]; exact le_top

lemma g70al_cdss_int (K : Kernel X X) [IsMarkovKernel K] {r : X → ℝ} (hr : Measurable r) {a : ℝ}
    (ha0 : 0 < a) (hint : DiscountedRewardIntegrable K r a) (x : X) (τ : (ℕ → X) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) :
    Integrable (discountedStoppedSum a r τ) (markovChainMeasure K x) := by
  refine ⟨g70al_cdss_aesm K x τ hτ ha0 hr (g70al_csumm_ae K hr ha0 hint x), ?_⟩
  unfold HasFiniteIntegral
  exact lt_of_le_of_lt (lintegral_mono fun ω => g70al_cdss_enorm τ ha0 r ω) (hint x)

lemma g70al_cdss1 (τ : (ℕ → X) → ℕ∞) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ω : ℕ → X) :
    discountedStoppedSum a (fun _ => (1 : ℝ)) τ ω =
      (1 - a)⁻¹ * (1 - (match τ ω with | (n : ℕ) => a ^ n | ⊤ => 0)) := by
  unfold discountedStoppedSum
  have hne : (1 - a) ≠ 0 := by linarith
  induction hτ : τ ω using ENat.recTopCoe with
  | top =>
    change _ = (1 - a)⁻¹ * (1 - 0)
    simp only [ENat.coe_lt_top, if_true, mul_one, sub_zero]
    rw [tsum_geometric_of_lt_one ha0.le ha1]
  | coe k =>
    change _ = (1 - a)⁻¹ * (1 - a ^ k)
    simp only [Nat.cast_lt, mul_one]
    rw [tsum_eq_sum (s := Finset.range k) (fun t ht => by simp at ht; rw [if_neg (by omega)])]
    rw [Finset.sum_congr rfl (fun t ht => if_pos (Finset.mem_range.1 ht)), geom_sum_eq ha1.ne]
    have h2 : a - 1 ≠ 0 := by linarith
    field_simp
    ring

lemma g70al_cD_meas (τ : (ℕ → X) → ℕ∞) (hτ : IsTrajStoppingTime τ) (a : ℝ) :
    Measurable (fun ω => (match τ ω with | (n : ℕ) => a ^ n | ⊤ => (0 : ℝ))) := by
  change Measurable ((fun m : ℕ∞ => (match m with | (n : ℕ) => a ^ n | ⊤ => (0 : ℝ))) ∘ τ)
  exact (measurable_of_countable (fun m : ℕ∞ => (match m with | (n : ℕ) => a ^ n | ⊤ => (0 : ℝ)))).comp
    (g70al_cτmeas τ hτ)

lemma g70al_cD_bd (τ : (ℕ → X) → ℕ∞) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ω : ℕ → X) :
    ‖(match τ ω with | (n : ℕ) => a ^ n | ⊤ => (0 : ℝ))‖ ≤ 1 := by
  induction τ ω using ENat.recTopCoe with
  | top => change ‖(0 : ℝ)‖ ≤ 1; simp
  | coe k =>
    change ‖a ^ k‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (pow_pos ha0 k)]
    exact pow_le_one₀ ha0.le ha1.le


lemma g70al_clin (τ : (ℕ → X) → ℕ∞) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (r : X → ℝ) (b c : ℝ)
    (ω : ℕ → X) (h : Summable (fun t => a ^ t * |r (ω t)|)) :
    discountedStoppedSum a (fun s => b * r s + c) τ ω =
      b * discountedStoppedSum a r τ ω + c * discountedStoppedSum a (fun _ => (1 : ℝ)) τ ω := by
  unfold discountedStoppedSum
  have h1 : Summable (fun t : ℕ => if (t : ℕ∞) < τ ω then a ^ t * r (ω t) else 0) :=
    Summable.of_norm_bounded h (g70al_cterm_bd τ ha0 r ω)
  have h2 : Summable (fun t : ℕ => if (t : ℕ∞) < τ ω then a ^ t * (fun _ => (1 : ℝ)) (ω t) else 0) :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one ha0.le ha1) (fun t => by
      have := g70al_cterm_bd τ ha0 (fun _ => (1 : ℝ)) ω t; simpa using this)
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (h1.mul_left b) (h2.mul_left c)]
  congr 1; ext t; split_ifs <;> ring

variable (K : Kernel X X) [IsMarkovKernel K]

lemma g70al_cD_int (x : X) (τ : (ℕ → X) → ℕ∞) (hτ : IsTrajStoppingTime τ) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1) :
    Integrable (fun ω => (match τ ω with | (n : ℕ) => a ^ n | ⊤ => (0 : ℝ)))
      (markovChainMeasure K x) := by
  haveI : IsProbabilityMeasure (markovChainMeasure K x) := by
    unfold markovChainMeasure; infer_instance
  exact Integrable.of_bound (C := 1) (g70al_cD_meas τ hτ a).aestronglyMeasurable
    (Filter.Eventually.of_forall (g70al_cD_bd τ ha0 ha1))

lemma g70al_cW (x : X) (τ : (ℕ → X) → ℕ∞) (hτ : IsTrajStoppingTime τ) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1) :
    stoppedTime K a τ x = (1 - a)⁻¹ * (1 - discountAtStop K a τ x) := by
  haveI : IsProbabilityMeasure (markovChainMeasure K x) := by
    unfold markovChainMeasure; infer_instance
  unfold stoppedTime discountAtStop
  simp_rw [g70al_cdss1 τ ha0 ha1]
  rw [integral_const_mul, integral_sub (integrable_const _) (g70al_cD_int K x τ hτ ha0 ha1)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rfl

/-- affine transport of stopped rewards. -/
lemma g70al_cR (r : X → ℝ) (hr : Measurable r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hint : DiscountedRewardIntegrable K r a) (E : X ≃ᵐ X) (b c : ℝ)
    (hrE : ∀ z, r (E z) = b * r z + c) (x : X)
    (hmc : markovChainMeasure K (E x) = (markovChainMeasure K x).map (fun ω n => E (ω n)))
    (τ : (ℕ → X) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    stoppedReward K r a τ (E x) =
      b * stoppedReward K r a (fun ω => τ (fun n => E (ω n))) x +
        c * stoppedTime K a (fun ω => τ (fun n => E (ω n))) x := by
  haveI : IsProbabilityMeasure (markovChainMeasure K x) := by
    unfold markovChainMeasure; infer_instance
  have hτ1 := g70al_stop_comp E E.measurable τ hτ
  unfold stoppedReward stoppedTime
  rw [hmc, g70al_int_map]
  have hpt : ∀ ω : ℕ → X, discountedStoppedSum a r τ (fun n => E (ω n)) =
      discountedStoppedSum a (fun s => b * r s + c) (fun ω => τ (fun n => E (ω n))) ω := by
    intro ω; unfold discountedStoppedSum; simp only [hrE]
  simp_rw [hpt]
  rw [integral_congr_ae (g70al_csumm_ae K hr ha0 hint x |>.mono fun ω hω =>
    g70al_clin _ ha0 ha1 r b c ω hω)]
  have hW : Integrable (discountedStoppedSum a (fun _ => (1 : ℝ)) (fun ω => τ (fun n => E (ω n))))
      (markovChainMeasure K x) := by
    refine (g70al_cD_int K x _ hτ1 ha0 ha1).const_mul (-(1 - a)⁻¹) |>.add
      (integrable_const ((1 - a)⁻¹)) |>.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    rw [g70al_cdss1 _ ha0 ha1]; ring
  rw [integral_add ((g70al_cdss_int K hr ha0 hint x _ hτ1).const_mul b) (hW.const_mul c),
    integral_const_mul, integral_const_mul]

lemma g70al_cDtr {a : ℝ} (E : X ≃ᵐ X) (x : X)
    (hmc : markovChainMeasure K (E x) = (markovChainMeasure K x).map (fun ω n => E (ω n)))
    (τ : (ℕ → X) → ℕ∞) :
    discountAtStop K a τ (E x) = discountAtStop K a (fun ω => τ (fun n => E (ω n))) x := by
  unfold discountAtStop
  rw [hmc, g70al_int_map]

lemma g70al_cRbd (r : X → ℝ) (hr : Measurable r) {a : ℝ} (ha0 : 0 < a)
    (hint : DiscountedRewardIntegrable K r a) (x : X) (τ : (ℕ → X) → ℕ∞)
    (hτ : IsTrajStoppingTime τ) :
    |stoppedReward K r a τ x| ≤
      (∫⁻ ω, ∑' t : ℕ, ENNReal.ofReal (a ^ t * |r (ω t)|) ∂markovChainMeasure K x).toReal := by
  unfold stoppedReward
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [integral_norm_eq_lintegral_enorm (g70al_cdss_int K hr ha0 hint x τ hτ).aestronglyMeasurable]
  exact ENNReal.toReal_mono (hint x).ne (lintegral_mono fun ω => g70al_cdss_enorm τ ha0 r ω)

lemma g70al_cDbd (x : X) (τ : (ℕ → X) → ℕ∞) (hτ : IsTrajStoppingTime τ) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1) : |discountAtStop K a τ x| ≤ 1 := by
  haveI : IsProbabilityMeasure (markovChainMeasure K x) := by
    unfold markovChainMeasure; infer_instance
  unfold discountAtStop
  rw [← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := markovChainMeasure K x)
    (Filter.Eventually.of_forall (g70al_cD_bd τ ha0 ha1))
  simp only [probReal_univ, mul_one] at this
  exact this

theorem g70al_calib (r : X → ℝ) (hr : Measurable r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hint : DiscountedRewardIntegrable K r a) (E : X ≃ᵐ X) (b c : ℝ) (hb : 0 < b)
    (hrE : ∀ z, r (E z) = b * r z + c) (x : X)
    (hmc : markovChainMeasure K (E x) = (markovChainMeasure K x).map (fun ω n => E (ω n)))
    (lam : ℝ) :
    calibrationPayoff K r a (b * lam + c) (E x) =
      c * (1 - a)⁻¹ + b * calibrationPayoff K r a lam x := by
  unfold calibrationPayoff
  set V : {τ : (ℕ → X) → ℕ∞ // IsTrajStoppingTime τ} → ℝ := fun τ =>
    stoppedReward K r a τ.1 x + lam * (1 - a)⁻¹ * discountAtStop K a τ.1 x with hV
  set T : {τ : (ℕ → X) → ℕ∞ // IsTrajStoppingTime τ} → {τ : (ℕ → X) → ℕ∞ // IsTrajStoppingTime τ} :=
    fun τ => ⟨fun ω => τ.1 (fun n => E (ω n)), g70al_stop_comp E E.measurable τ.1 τ.2⟩
  have hT : Function.Surjective T := by
    intro τ
    refine ⟨⟨fun ω => τ.1 (fun n => E.symm (ω n)), g70al_stop_comp E.symm E.symm.measurable τ.1 τ.2⟩, ?_⟩
    apply Subtype.ext; funext ω; simp [T]
  set f : ℝ → ℝ := fun v => c * (1 - a)⁻¹ + b * v
  have hval : ∀ τ : {τ : (ℕ → X) → ℕ∞ // IsTrajStoppingTime τ},
      stoppedReward K r a τ.1 (E x) + (b * lam + c) * (1 - a)⁻¹ * discountAtStop K a τ.1 (E x) =
        f (V (T τ)) := by
    intro τ
    simp only [hV, T, f]
    rw [g70al_cR K r hr ha0 ha1 hint E b c hrE x hmc τ.1 τ.2, g70al_cDtr K E x hmc,
      g70al_cW K x _ (g70al_stop_comp E E.measurable τ.1 τ.2) ha0 ha1]
    ring
  simp_rw [hval]
  have hne : Nonempty {τ : (ℕ → X) → ℕ∞ // IsTrajStoppingTime τ} :=
    ⟨⟨fun _ => ⊤, fun n => by simp⟩⟩
  have hbdd : BddAbove (Set.range V) := by
    refine ⟨(∫⁻ ω, ∑' t : ℕ, ENNReal.ofReal (a ^ t * |r (ω t)|) ∂markovChainMeasure K x).toReal +
      |lam| * (1 - a)⁻¹, ?_⟩
    rintro _ ⟨τ, rfl⟩
    simp only [hV]
    have h1 := g70al_cRbd K r hr ha0 hint x τ.1 τ.2
    have h2 := g70al_cDbd K x τ.1 τ.2 ha0 ha1
    have h3 : lam * (1 - a)⁻¹ * discountAtStop K a τ.1 x ≤ |lam| * (1 - a)⁻¹ := by
      have hpos : 0 < (1 - a)⁻¹ := inv_pos.2 (by linarith)
      calc lam * (1 - a)⁻¹ * discountAtStop K a τ.1 x ≤ |lam * (1 - a)⁻¹ * discountAtStop K a τ.1 x| :=
            le_abs_self _
        _ = |lam| * (1 - a)⁻¹ * |discountAtStop K a τ.1 x| := by
            rw [abs_mul, abs_mul, abs_of_pos hpos]
        _ ≤ |lam| * (1 - a)⁻¹ * 1 := by gcongr
        _ = _ := by ring
    linarith [le_abs_self (stoppedReward K r a τ.1 x)]
  have hcomp : (⨆ τ, f (V (T τ))) = ⨆ τ, f (V τ) := by
    unfold iSup
    congr 1
    exact hT.range_comp (fun τ => f (V τ))
  rw [hcomp]
  exact (Monotone.map_ciSup_of_continuousAt (f := f) (by fun_prop)
    (fun u v huv => by simp only [f]; nlinarith) hbdd).symm


lemma g70al_cgit_def (r : X → ℝ) (a : ℝ) (y : X) :
    gittinsIndex K r a y = sSup {g : ℝ | ∃ τ : (ℕ → X) → ℕ∞, IsTrajStoppingTime τ ∧
      (∀ ω, 1 ≤ τ ω) ∧ g = stoppedReward K r a τ y / stoppedTime K a τ y} := rfl

lemma g70al_cWtr {a : ℝ} (E : X ≃ᵐ X) (x : X)
    (hmc : markovChainMeasure K (E x) = (markovChainMeasure K x).map (fun ω n => E (ω n)))
    (τ : (ℕ → X) → ℕ∞) :
    stoppedTime K a τ (E x) = stoppedTime K a (fun ω => τ (fun n => E (ω n))) x := by
  unfold stoppedTime
  rw [hmc, g70al_int_map]
  rfl

lemma g70al_cW_ge (x : X) (τ : (ℕ → X) → ℕ∞) (hτ : IsTrajStoppingTime τ) (h1 : ∀ ω, 1 ≤ τ ω)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 1 ≤ stoppedTime K a τ x := by
  haveI : IsProbabilityMeasure (markovChainMeasure K x) := by
    unfold markovChainMeasure; infer_instance
  rw [g70al_cW K x τ hτ ha0 ha1]
  have hD : discountAtStop K a τ x ≤ a := by
    unfold discountAtStop
    calc _ ≤ ∫ _ω, a ∂markovChainMeasure K x :=
          integral_mono (g70al_cD_int K x τ hτ ha0 ha1) (integrable_const _) (fun ω => by
            have := h1 ω
            induction hτω : τ ω using ENat.recTopCoe with
            | top => change (0 : ℝ) ≤ a; exact ha0.le
            | coe k =>
              change a ^ k ≤ a
              rw [hτω] at this
              exact pow_le_of_le_one ha0.le ha1.le (by
                intro hk; subst hk; simp at this))
      _ = a := by simp
  have hpos : 0 < 1 - a := by linarith
  rw [inv_mul_eq_div, le_div_iff₀ hpos]; linarith

theorem g70al_cgitt (r : X → ℝ) (hr : Measurable r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hint : DiscountedRewardIntegrable K r a) (E : X ≃ᵐ X) (b c : ℝ) (hb : 0 < b)
    (hrE : ∀ z, r (E z) = b * r z + c) (x : X)
    (hmc : markovChainMeasure K (E x) = (markovChainMeasure K x).map (fun ω n => E (ω n))) :
    gittinsIndex K r a (E x) = c + b * gittinsIndex K r a x := by
  rw [g70al_cgit_def, g70al_cgit_def]
  set S := {g : ℝ | ∃ τ : (ℕ → X) → ℕ∞, IsTrajStoppingTime τ ∧
      (∀ ω, 1 ≤ τ ω) ∧ g = stoppedReward K r a τ x / stoppedTime K a τ x}
  set f : ℝ → ℝ := fun v => c + b * v
  have hratio : ∀ τ : (ℕ → X) → ℕ∞, IsTrajStoppingTime τ → (∀ ω, 1 ≤ τ ω) →
      stoppedReward K r a τ (E x) / stoppedTime K a τ (E x) =
        f (stoppedReward K r a (fun ω => τ (fun n => E (ω n))) x /
          stoppedTime K a (fun ω => τ (fun n => E (ω n))) x) := by
    intro τ hτ h1
    have hτ1 := g70al_stop_comp E E.measurable τ hτ
    have hW := g70al_cW_ge K x _ hτ1 (fun ω => h1 _) ha0 ha1
    rw [g70al_cR K r hr ha0 ha1 hint E b c hrE x hmc τ hτ, g70al_cWtr K E x hmc]
    simp only [f]
    field_simp
    ring
  have hset : {g : ℝ | ∃ τ : (ℕ → X) → ℕ∞, IsTrajStoppingTime τ ∧
      (∀ ω, 1 ≤ τ ω) ∧ g = stoppedReward K r a τ (E x) / stoppedTime K a τ (E x)} = f '' S := by
    ext g
    constructor
    · rintro ⟨τ, hτ, h1, rfl⟩
      exact ⟨_, ⟨_, g70al_stop_comp E E.measurable τ hτ, fun ω => h1 _, rfl⟩,
        (hratio τ hτ h1).symm⟩
    · rintro ⟨_, ⟨τ, hτ, h1, rfl⟩, rfl⟩
      refine ⟨fun ω => τ (fun n => E.symm (ω n)), g70al_stop_comp E.symm E.symm.measurable τ hτ,
        fun ω => h1 _, ?_⟩
      rw [hratio _ (g70al_stop_comp E.symm E.symm.measurable τ hτ) (fun ω => h1 _)]
      simp only [MeasurableEquiv.symm_apply_apply]
  rw [hset]
  have hne : S.Nonempty := ⟨_, fun _ => ⊤, fun n => by simp, fun _ => le_top, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨(∫⁻ ω, ∑' t : ℕ, ENNReal.ofReal (a ^ t * |r (ω t)|) ∂markovChainMeasure K x).toReal, ?_⟩
    rintro _ ⟨τ, hτ, h1, rfl⟩
    have hW := g70al_cW_ge K x τ hτ h1 ha0 ha1
    have hR := g70al_cRbd K r hr ha0 hint x τ hτ
    calc stoppedReward K r a τ x / stoppedTime K a τ x
        ≤ |stoppedReward K r a τ x / stoppedTime K a τ x| := le_abs_self _
      _ = |stoppedReward K r a τ x| / stoppedTime K a τ x := by
          rw [abs_div, abs_of_pos (show (0:ℝ) < stoppedTime K a τ x by linarith)]
      _ ≤ |stoppedReward K r a τ x| := div_le_self (abs_nonneg _) hW
      _ ≤ _ := hR
  exact (Monotone.map_csSup_of_continuousAt (f := f) (by fun_prop)
    (fun u v huv => by simp only [f]; nlinarith) hne hbdd).symm

end G70ALC

noncomputable def g70al_ls (b c : ℝ) (hb : b ≠ 0) : (ℝ × ℝ × ℝ) ≃ᵐ (ℝ × ℝ × ℝ) where
  toFun p := (b * p.1 + c, b * p.2.1, p.2.2)
  invFun p := (b⁻¹ * (p.1 - c), b⁻¹ * p.2.1, p.2.2)
  left_inv p := by simp [hb]
  right_inv p := by simp [hb]
  measurable_toFun := by
    change Measurable (fun p : ℝ × ℝ × ℝ => (b * p.1 + c, b * p.2.1, p.2.2)); fun_prop
  measurable_invFun := by
    change Measurable (fun p : ℝ × ℝ × ℝ => (b⁻¹ * (p.1 - c), b⁻¹ * p.2.1, p.2.2)); fun_prop

lemma g70al_rc_eq {Θ Q : Type*} [MeasurableSpace Θ] [MeasurableSpace Q] (F : SamplingModel Θ Q)
    (q : Q) : F.rewardChain q = (F.predictive q).map (F.update q) := by
  unfold SamplingModel.rewardChain
  rw [Kernel.map_apply _ F.measurable_update, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map F.measurable_update measurable_prodMk_left]
  rfl

open AllocationIndices.Targets

theorem solution (F : SamplingModel (ℝ × ℝ) (ℝ × ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2.1 ∧ 1 < p.2.2})
    (hlik : HasJointLocationScale F.likelihood) (hprior : PriorHasJointLocationScale F.prior)
    (hupd : F.update = meanSdUpdate) (hmean : ∀ p, Integrable (fun x : ℝ ↦ x) (F.predictive p))
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hint : DiscountedRewardIntegrable F.rewardChain F.rewardOf a)
    (xb s n : ℝ) (hs : 0 < s) (hn : 1 < n) :
    (∀ lam b c : ℝ, 0 < b →
      calibrationPayoff F.rewardChain F.rewardOf a (b * lam + c) (b * xb + c, b * s, n) =
        c * (1 - a)⁻¹ + b * calibrationPayoff F.rewardChain F.rewardOf a lam (xb, s, n)) ∧
    gittinsIndex F.rewardChain F.rewardOf a (xb, s, n) =
      xb + s * gittinsIndex F.rewardChain F.rewardOf a (0, 1, n) := by

  have hpred : ∀ b c : ℝ, ∀ hb : 0 < b, ∀ q, F.predictive (g70al_ls b c hb.ne' q) =
      (F.predictive q).map (fun x => b * x + c) := by
    intro b c hb q
    have hgm : Measurable (fun x : ℝ => b * x + c) := by fun_prop
    ext S hS
    unfold SamplingModel.predictive
    rw [Kernel.comp_apply' _ _ _ hS, Measure.map_apply hgm hS, Kernel.comp_apply' _ _ _ (hgm hS)]
    change ∫⁻ θ, F.likelihood θ S ∂F.prior (b * q.1 + c, b * q.2.1, q.2.2) = _
    rw [hprior q.1 q.2.1 q.2.2 b c hb, lintegral_map (Kernel.measurable_coe _ hS) (by fun_prop)]
    congr 1; ext θ
    rw [hlik θ.1 θ.2 b c hb, Measure.map_apply hgm hS]
  set Gq : Set (ℝ × ℝ × ℝ) := {q | 1 < q.2.2} with hGq
  have hGqm : MeasurableSet Gq := measurableSet_lt measurable_const (by fun_prop)
  have hup : ∀ b c : ℝ, ∀ hb : 0 < b, ∀ q ∈ Gq, ∀ x, F.update (g70al_ls b c hb.ne' q) (b * x + c) =
      g70al_ls b c hb.ne' (F.update q x) := by
    intro b c hb q hq x
    simp only [hGq, Set.mem_setOf_eq] at hq
    have hn1 : q.2.2 + 1 ≠ 0 := by linarith
    rw [hupd]
    change meanSdUpdate (b * q.1 + c, b * q.2.1, q.2.2) (b * x + c) =
      (b * (meanSdUpdate q x).1 + c, b * (meanSdUpdate q x).2.1, (meanSdUpdate q x).2.2)
    simp only [meanSdUpdate]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · simp only; field_simp; ring
    · simp only
      have : ((q.2.2 - 1) * (b * q.2.1) ^ 2 + q.2.2 * (b * x + c - (b * q.1 + c)) ^ 2 /
          (q.2.2 + 1)) / q.2.2 = b ^ 2 * (((q.2.2 - 1) * q.2.1 ^ 2 + q.2.2 * (x - q.1) ^ 2 /
          (q.2.2 + 1)) / q.2.2) := by ring
      rw [this, Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le]
  have hupm : ∀ q, Measurable (F.update q) := fun q =>
    F.measurable_update.comp (measurable_const.prodMk measurable_id)
  have hr : Measurable F.rewardOf :=
    (StronglyMeasurable.integral_kernel (κ := F.predictive) stronglyMeasurable_id).measurable
  have hrE : ∀ b c : ℝ, ∀ hb : 0 < b, ∀ q, F.rewardOf (g70al_ls b c hb.ne' q) =
      b * F.rewardOf q + c := by
    intro b c hb q
    unfold SamplingModel.rewardOf
    rw [hpred b c hb q, integral_map (φ := fun x : ℝ => b * x + c) (f := fun x : ℝ => x)
      (by fun_prop) (by fun_prop),
      integral_add ((hmean q).const_mul b) (integrable_const c), integral_const_mul]
    simp
  have hmc : ∀ b c : ℝ, ∀ hb : 0 < b, ∀ q ∈ Gq,
      markovChainMeasure F.rewardChain (g70al_ls b c hb.ne' q) =
      (markovChainMeasure F.rewardChain q).map (fun ω k => g70al_ls b c hb.ne' (ω k)) := by
    intro b c hb q hq
    refine g70al_mc_mapG _ _ _ (MeasurableEquiv.measurable _) Gq hGqm ?_ ?_ q hq
    · intro z hz
      rw [g70al_rc_eq, Measure.map_apply (hupm z) hGqm.compl]
      convert measure_empty (μ := F.predictive z)
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, hGq, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_not]
      simp only [hGq, Set.mem_setOf_eq] at hz
      rw [hupd]; simp only [meanSdUpdate]; linarith
    · intro z hz
      rw [g70al_rc_eq, g70al_rc_eq, hpred b c hb z, Measure.map_map (hupm _) (by fun_prop),
        Measure.map_map (MeasurableEquiv.measurable _) (hupm z)]
      congr 1
      funext x
      exact hup b c hb z hz x
  have hG0 : (xb, s, n) ∈ Gq := hn
  refine ⟨fun lam b c hb => ?_, ?_⟩
  · exact g70al_calib F.rewardChain F.rewardOf hr ha0 ha1 hint (g70al_ls b c hb.ne') b c hb
      (hrE b c hb) (xb, s, n) (hmc b c hb _ hn) lam
  · have := g70al_cgitt F.rewardChain F.rewardOf hr ha0 ha1 hint (g70al_ls s xb hs.ne') s xb hs
      (hrE s xb hs) (0, 1, n) (hmc s xb hs _ hn)
    have he : g70al_ls s xb hs.ne' (0, 1, n) = (xb, s, n) := by
      change (s * 0 + xb, s * 1, n) = (xb, s, n)
      simp
    rw [he] at this
    exact this
