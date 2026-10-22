-- Prove2me | solution 1 for AllocationIndices.Targets.target_location_scale_invariance_known_scale
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:15:55.943433+00:00
-- url     : https://prove2.me/submissions/c402f2f4-60c3-45f4-85e4-5e95e0c4c834

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
noncomputable def g70al_M : SamplingModel (ℝ × ℝ) (ℝ × ℝ × ℝ) where
  likelihood := Kernel.deterministic Prod.fst measurable_fst
  likelihood_markov := inferInstance
  prior := Kernel.deterministic (fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) (by fun_prop)
  prior_markov := inferInstance
  update := knownScaleUpdate
  measurable_update := measurable_knownScaleUpdate

lemma g70al_M_pred (q : ℝ × ℝ × ℝ) : g70al_M.predictive q = Measure.dirac q.1 := by
  unfold SamplingModel.predictive
  rw [Kernel.comp_apply]
  simp only [g70al_M, Kernel.deterministic_apply]
  rw [Measure.dirac_bind (Kernel.measurable _), Kernel.deterministic_apply]

lemma g70al_M_lik : HasJointLocationScale g70al_M.likelihood := by
  intro μ σ b c hb
  simp only [g70al_M, Kernel.deterministic_apply]
  rw [Measure.map_dirac' (by fun_prop)]

lemma g70al_M_prior : PriorHasJointLocationScaleKnown g70al_M.prior := by
  intro xb n σ b c hb
  simp only [g70al_M, Kernel.deterministic_apply]
  rw [Measure.map_dirac' (by fun_prop)]

lemma g70al_M_known : ∀ p : ℝ × ℝ × ℝ, 0 < p.2.1 → 0 < p.2.2 →
    g70al_M.prior p {θ | θ.2 ≠ p.2.2} = 0 := by
  intro p _ _
  simp only [g70al_M, Kernel.deterministic_apply]
  have : {θ : ℝ × ℝ | θ.2 ≠ p.2.2} = {θ | θ.2 = p.2.2}ᶜ := by ext; simp
  rw [this, Measure.dirac_apply' _ (measurableSet_eq_fun measurable_snd measurable_const).compl]
  simp

lemma g70al_M_conj : g70al_M.IsConjugateOn {p | 0 < p.2.1 ∧ 0 < p.2.2} := by
  intro p hp
  have hn : p.2.1 + 1 ≠ 0 := by have := hp.1; linarith
  set θ0 : ℝ × ℝ := (p.1, p.2.2)
  have hprior : g70al_M.prior p = Measure.dirac θ0 := by
    simp only [g70al_M, Kernel.deterministic_apply]; rfl
  have hcp : (g70al_M.likelihood ∘ₘ g70al_M.prior p) ⊗ₘ Kernel.const ℝ (Measure.dirac θ0) =
      (g70al_M.prior p ⊗ₘ g70al_M.likelihood).map Prod.swap := by
    rw [hprior]
    have h1 : g70al_M.likelihood ∘ₘ Measure.dirac θ0 = Measure.dirac θ0.1 := by
      show (Measure.dirac θ0).bind _ = _
      rw [Measure.dirac_bind (Kernel.measurable _)]
      simp only [g70al_M, Kernel.deterministic_apply]
    have h2 : Measure.dirac θ0 ⊗ₘ g70al_M.likelihood = Measure.dirac (θ0, θ0.1) := by
      ext s hs
      rw [Measure.compProd_apply hs, lintegral_dirac,
        Measure.dirac_apply' _ hs]
      simp only [g70al_M, Kernel.deterministic_apply]
      rw [Measure.dirac_apply' _ (measurable_prodMk_left hs)]
      rfl
    rw [h1, h2, Measure.compProd_const, Measure.dirac_prod_dirac, Measure.map_dirac' measurable_swap]
    rfl
  have hpost := ae_eq_posterior_of_compProd_eq hcp
  have hpred : g70al_M.likelihood ∘ₘ g70al_M.prior p = Measure.dirac p.1 := by
    rw [← g70al_M_pred p]; rfl
  rw [hpred] at hpost
  rw [g70al_M_pred p]
  have hx : ∀ᵐ x ∂(Measure.dirac p.1), x = p.1 := by
    rw [ae_dirac_eq]; exact Filter.eventually_pure.2 rfl
  filter_upwards [hpost, hx] with x h1 h2
  rw [← h1, h2, Kernel.const_apply]
  simp only [g70al_M, Kernel.deterministic_apply, knownScaleUpdate, θ0]
  congr 2
  field_simp

lemma g70al_step1 {X : Type*} [MeasurableSpace X] (K : Kernel X X) [IsMarkovKernel K] (x : X) :
    (markovChainMeasure K x).map (fun ω => ω 1) = K x := by
  unfold markovChainMeasure Kernel.trajMeasure
  rw [Measure.map_comp _ _ (by fun_prop)]
  have := Kernel.map_traj_succ_self (X := fun _ : ℕ => X) (κ := markovChainStep K) (a := 0)
  simp only [zero_add] at this
  rw [this]
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_map (Kernel.measurable_coe _ hs)
    (MeasurableEquiv.measurable _)]
  exact lintegral_dirac' (α := X) x
    ((Kernel.measurable_coe _ hs).comp (MeasurableEquiv.measurable _))

lemma g70al_A_le : targetCost g70al_M 1 (1 / 2) (1, 1, 1) ≤ 1 := by
  haveI : IsProbabilityMeasure (markovChainMeasure (g70al_M.targetChain 1) (Sum.inl (1, 1, 1))) := by
    unfold markovChainMeasure; infer_instance
  unfold targetCost
  refine (iInf_le _ ⟨fun _ => (1 : ℕ∞), fun n => by
    by_cases h : (1 : ℕ∞) ≤ n
    · simp [h]
    · simp [h]⟩).trans ?_
  have hstep : markovChainMeasure (g70al_M.targetChain 1) (Sum.inl (1, 1, 1))
      {ω | ∃ m : ℕ, (1 : ℕ∞) = (m : ℕ∞) ∧ (ω m).isLeft} = 0 := by
    have hset : {ω : ℕ → (ℝ × ℝ × ℝ) ⊕ Unit | ∃ m : ℕ, (1 : ℕ∞) = (m : ℕ∞) ∧ (ω m).isLeft} =
        (fun ω => ω 1) ⁻¹' {z | z.isLeft} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · rintro ⟨m, hm, h⟩
        have : m = 1 := by exact_mod_cast hm.symm
        subst this; exact h
      · intro h; exact ⟨1, by simp, h⟩
    have hmeas : MeasurableSet {z : (ℝ × ℝ × ℝ) ⊕ Unit | z.isLeft} := by
      have : {z : (ℝ × ℝ × ℝ) ⊕ Unit | z.isLeft} = Set.range Sum.inl := by
        ext z; cases z <;> simp
      rw [this]; exact measurableSet_range_inl
    rw [hset, ← Measure.map_apply (by fun_prop) hmeas, g70al_step1]
    change g70al_M.targetStep 1 (1, 1, 1) _ = 0
    rw [g70al_targetStep_eq, g70al_M_pred, Measure.map_dirac' (by
      exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
        (measurable_inl.comp (g70al_M.measurable_update.comp (measurable_const.prodMk measurable_id))))]
    rw [Measure.dirac_apply' _ hmeas]
    simp
  rw [hstep, mul_zero, add_zero]
  calc _ ≤ ∫⁻ _ω, (1 : ENNReal) ∂markovChainMeasure (g70al_M.targetChain 1) (Sum.inl (1, 1, 1)) := by
        refine lintegral_mono fun ω => ?_
        rw [tsum_eq_single 0]
        · split_ifs <;> simp
        · intro t ht
          rw [if_neg]
          rintro ⟨h1, _⟩
          have h1' : (t : ℕ∞) < 1 := h1
          have : t < 1 := by exact_mod_cast h1'
          omega
    _ = 1 := by simp

lemma g70al_B_ge : ENNReal.ofReal (1 / 2 : ℝ)⁻¹ ≤ targetCost g70al_M 2 (1 / 2) (1, 1, 2) := by
  set μ := markovChainMeasure (g70al_M.targetChain 2) (Sum.inl ((1 : ℝ), (1 : ℝ), (2 : ℝ)))
  haveI : IsProbabilityMeasure μ := by unfold μ markovChainMeasure; infer_instance
  set Gq : Set (ℝ × ℝ × ℝ) := {q | q.1 < 2} with hGq
  have hGm : MeasurableSet (Sum.inl '' Gq : Set ((ℝ × ℝ × ℝ) ⊕ Unit)) :=
    (measurableSet_lt measurable_fst measurable_const).inl_image
  have hinv : ∀ z ∈ (Sum.inl '' Gq : Set ((ℝ × ℝ × ℝ) ⊕ Unit)),
      g70al_M.targetChain 2 z (Sum.inl '' Gq)ᶜ = 0 := by
    rintro _ ⟨q, hq, rfl⟩
    simp only [hGq, Set.mem_setOf_eq] at hq
    change g70al_M.targetStep 2 q _ = 0
    rw [g70al_targetStep_eq, g70al_M_pred, Measure.map_dirac' (by
      exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
        (measurable_inl.comp (g70al_M.measurable_update.comp (measurable_const.prodMk measurable_id)))),
      Measure.dirac_apply' _ hGm.compl, if_neg (by linarith)]
    simp only [Set.indicator_apply_eq_zero, Set.mem_compl_iff, not_not, Pi.one_apply, one_ne_zero,
      imp_false]
    refine ⟨_, ?_, rfl⟩
    simp only [hGq, Set.mem_setOf_eq, g70al_M, knownScaleUpdate]
    by_cases hn : q.2.1 + 1 = 0
    · rw [hn, div_zero]; norm_num
    · rw [show q.2.1 * q.1 + q.1 = q.1 * (q.2.1 + 1) by ring, mul_div_cancel_right₀ _ hn]
      exact hq
  have hall : ∀ᵐ ω ∂μ, ∀ t, (ω t).isLeft = true := by
    rw [ae_all_iff]
    intro t
    filter_upwards [g70al_invG _ _ hGm hinv _ ⟨_, by simp [hGq], rfl⟩ t] with ω hω
    obtain ⟨q, _, hq⟩ := hω
    rw [← hq]; rfl
  unfold targetCost
  refine le_iInf fun τ => ?_
  have hτm : ∀ n : ℕ, MeasurableSet {ω : ℕ → (ℝ × ℝ × ℝ) ⊕ Unit | τ.1 ω ≤ (n : ℕ∞)} := fun n =>
    Measurable.comap_le (measurable_pi_lambda _ fun i => measurable_pi_apply _) _ (τ.2 n)
  set S := {ω : ℕ → (ℝ × ℝ × ℝ) ⊕ Unit | τ.1 ω = ⊤}
  have hSm : MeasurableSet S := by
    have : S = ⋂ n : ℕ, {ω | τ.1 ω ≤ (n : ℕ∞)}ᶜ := by
      ext ω; simp only [S, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff, not_le]
      constructor
      · intro h n; rw [h]; exact ENat.coe_lt_top n
      · intro h
        by_contra hne
        obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
        exact absurd (h k) (by rw [← hk]; exact lt_irrefl _)
    rw [this]; exact MeasurableSet.iInter fun n => (hτm n).compl
  by_cases hS : μ S = 0
  · refine le_add_left ?_
    set A := {ω : ℕ → (ℝ × ℝ × ℝ) ⊕ Unit | ∃ m : ℕ, τ.1 ω = (m : ℕ∞) ∧ (ω m).isLeft} with hAdef
    have hA : 1 ≤ μ A := by
      have hae : ∀ᵐ ω ∂μ, ω ∈ A := by
        have hS' : ∀ᵐ ω ∂μ, ω ∉ S := by rw [ae_iff]; simpa using hS
        filter_upwards [hS', hall] with ω h1 h2
        simp only [S, Set.mem_setOf_eq] at h1
        obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h1
        exact ⟨k, hk.symm, h2 k⟩
      have hc : μ Aᶜ = 0 := ae_iff.1 hae
      calc (1 : ENNReal) = μ Set.univ := measure_univ.symm
        _ ≤ μ A + μ Aᶜ := measure_univ_le_add_compl A
        _ = μ A := by rw [hc, add_zero]
    calc ENNReal.ofReal (1 / 2 : ℝ)⁻¹ = ENNReal.ofReal (1 / 2 : ℝ)⁻¹ * 1 := (mul_one _).symm
      _ ≤ _ := by gcongr
  · refine le_add_right ?_
    refine le_trans le_top ?_
    calc (⊤ : ENNReal) = ∫⁻ ω, S.indicator (fun _ => (⊤ : ENNReal)) ω ∂μ := by
          rw [lintegral_indicator_const hSm, ENNReal.top_mul hS]
      _ ≤ _ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hall] with ω h2
          by_cases hω : ω ∈ S
          · rw [Set.indicator_of_mem hω]
            simp only [S, Set.mem_setOf_eq] at hω
            have : ∀ t : ℕ, (if (t : ℕ∞) < τ.1 ω ∧ (ω t).isLeft = true then (1 : ENNReal) else 0) = 1 :=
              fun t => by rw [if_pos ⟨by rw [hω]; exact ENat.coe_lt_top t, h2 t⟩]
            simp_rw [this]
            exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).ge
          · rw [Set.indicator_of_notMem hω]; exact bot_le

theorem solution : ¬ (∀ (F : SamplingModel (ℝ × ℝ) (ℝ × ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2.1 ∧ 0 < p.2.2})
    (hlik : HasJointLocationScale F.likelihood) (hprior : PriorHasJointLocationScaleKnown F.prior)
    (hknown : ∀ p : ℝ × ℝ × ℝ, 0 < p.2.1 → 0 < p.2.2 → F.prior p {θ | θ.2 ≠ p.2.2} = 0)
    (hupd : F.update = knownScaleUpdate) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (xb n σ T : ℝ) (hn : 0 < n) (hσ : 0 < σ),
    (∀ φ b c : ℝ, 0 < φ → φ ≤ 1 → 0 < b →
      targetCost F T φ (xb, n, σ) = targetCost F (b * T + c) φ (xb + c, n, b * σ)) ∧
    gittinsIndex (F.targetChain T) (F.targetReward T) a (Sum.inl (xb, n, σ)) =
      gittinsIndex (F.targetChain 0) (F.targetReward 0) a (Sum.inl ((xb - T) / σ, n, 1))) := by
  intro h
  have := (h g70al_M g70al_M_conj g70al_M_lik g70al_M_prior g70al_M_known rfl (a := 1 / 2)
    (by norm_num) (by norm_num) 1 1 1 1 one_pos one_pos).1 (1 / 2) 2 0 (by norm_num) (by norm_num)
    (by norm_num)
  rw [show (2 : ℝ) * 1 + 0 = 2 by norm_num, show (1 : ℝ) + 0 = 1 by norm_num,
    show (2 : ℝ) * 1 = 2 by norm_num] at this
  have hA := g70al_A_le
  have hB := g70al_B_ge
  rw [this] at hA
  have := hB.trans hA
  rw [ENNReal.ofReal_le_one] at this
  norm_num at this
