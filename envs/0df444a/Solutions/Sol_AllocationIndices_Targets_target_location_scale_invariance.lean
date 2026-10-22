-- Prove2me | solution 1 for AllocationIndices.Targets.target_location_scale_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:00:11.331787+00:00
-- url     : https://prove2.me/submissions/4b9fb0e0-7a70-4329-91d6-be23b9b7160c

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

noncomputable def g70al_ls (b c : ℝ) (hb : b ≠ 0) : (ℝ × ℝ × ℝ) ≃ᵐ (ℝ × ℝ × ℝ) where
  toFun p := (b * p.1 + c, b * p.2.1, p.2.2)
  invFun p := (b⁻¹ * (p.1 - c), b⁻¹ * p.2.1, p.2.2)
  left_inv p := by simp [hb]
  right_inv p := by simp [hb]
  measurable_toFun := by
    change Measurable (fun p : ℝ × ℝ × ℝ => (b * p.1 + c, b * p.2.1, p.2.2)); fun_prop
  measurable_invFun := by
    change Measurable (fun p : ℝ × ℝ × ℝ => (b⁻¹ * (p.1 - c), b⁻¹ * p.2.1, p.2.2)); fun_prop

open AllocationIndices.Targets

theorem solution (F : SamplingModel (ℝ × ℝ) (ℝ × ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2.1 ∧ 1 < p.2.2})
    (hlik : HasJointLocationScale F.likelihood) (hprior : PriorHasJointLocationScale F.prior)
    (hupd : F.update = meanSdUpdate) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (xb s n T : ℝ) (hs : 0 < s) (hn : 1 < n) :
    (∀ φ b c : ℝ, 0 < φ → φ ≤ 1 → 0 < b →
      targetCost F T φ (xb, s, n) = targetCost F (b * T + c) φ (b * xb + c, b * s, n)) ∧
    gittinsIndex (F.targetChain T) (F.targetReward T) a (Sum.inl (xb, s, n)) =
      gittinsIndex (F.targetChain 0) (F.targetReward 0) a (Sum.inl ((xb - T) / s, 1, n)) := by

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
  have hT' : ∀ b c : ℝ, 0 < b → ∀ T x : ℝ, b * T + c ≤ b * x + c ↔ T ≤ x := fun b c hb T x => by
    constructor <;> intro h <;> nlinarith
  set Gq : Set (ℝ × ℝ × ℝ) := {q | 1 < q.2.2} with hGq
  have hGqm : MeasurableSet Gq := measurableSet_lt measurable_const (by fun_prop)
  have hupG : ∀ q ∈ Gq, ∀ x, F.update q x ∈ Gq := by
    intro q hq x
    rw [hupd]; simp only [hGq, Set.mem_setOf_eq, meanSdUpdate] at hq ⊢; linarith
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
  have hmc : ∀ b c : ℝ, ∀ hb : 0 < b, ∀ T : ℝ,
      markovChainMeasure (F.targetChain (b * T + c))
        (MeasurableEquiv.sumCongr (g70al_ls b c hb.ne') (MeasurableEquiv.refl Unit)
          (Sum.inl (xb, s, n))) =
      (markovChainMeasure (F.targetChain T) (Sum.inl (xb, s, n))).map
        (fun ω k => MeasurableEquiv.sumCongr (g70al_ls b c hb.ne') (MeasurableEquiv.refl Unit)
          (ω k)) := by
    intro b c hb T
    exact g70al_mc_mapG _ _ _ (MeasurableEquiv.measurable _) _
      (hGqm.inl_image.union measurableSet_range_inr)
      (fun z hz => g70al_chain_invG F T Gq hGqm hupG z hz)
      (fun z hz => g70al_chain_equivG F T (b * T + c) (g70al_ls b c hb.ne') (fun x => b * x + c)
        (by fun_prop) Gq (hpred b c hb) (hT' b c hb T) (hup b c hb) z hz)
      _ (Or.inl ⟨_, hn, rfl⟩)
  refine ⟨fun φ b c hφ hφ1 hb => ?_, ?_⟩
  · unfold targetCost
    exact (g70al_cost_transport (F.targetChain T) (F.targetChain (b * T + c)) _
      (fun z => z.isLeft) (fun z => z.isLeft) (fun z => by cases z <;> rfl) (ENNReal.ofReal φ⁻¹)
      (Sum.inl (xb, s, n)) (hmc b c hb T)).symm
  · have hsi : 0 < s⁻¹ := inv_pos.2 hs
    have := g70al_gittins_transport (F.targetChain T) (F.targetChain (s⁻¹ * T + -(s⁻¹ * T))) _
      (F.targetReward (s⁻¹ * T + -(s⁻¹ * T))) a (Sum.inl (xb, s, n)) (hmc s⁻¹ (-(s⁻¹ * T)) hsi T)
    have hr : (fun z => F.targetReward (s⁻¹ * T + -(s⁻¹ * T))
        (MeasurableEquiv.sumCongr (g70al_ls s⁻¹ (-(s⁻¹ * T)) hsi.ne') (MeasurableEquiv.refl Unit) z)) =
        F.targetReward T :=
      funext (g70al_reward_equiv F T _ (g70al_ls s⁻¹ (-(s⁻¹ * T)) hsi.ne')
        (fun x => s⁻¹ * x + -(s⁻¹ * T)) (by fun_prop) (hpred _ _ hsi) (hT' _ _ hsi T))
    rw [hr] at this
    have h2 : (MeasurableEquiv.sumCongr (g70al_ls s⁻¹ (-(s⁻¹ * T)) hsi.ne') (MeasurableEquiv.refl Unit))
        (Sum.inl (xb, s, n)) = Sum.inl ((xb - T) / s, 1, n) := by
      change Sum.inl (s⁻¹ * xb + -(s⁻¹ * T), s⁻¹ * s, n) = Sum.inl ((xb - T) / s, 1, n)
      rw [inv_mul_cancel₀ hs.ne']
      congr 2; ring
    rw [h2, add_neg_cancel] at this
    exact this.symm
