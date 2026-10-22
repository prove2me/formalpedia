-- Prove2me | solution 1 for AllocationIndices.Targets.target_scale_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:52:56.182683+00:00
-- url     : https://prove2.me/submissions/d14672eb-f1e0-4cd7-9cdc-3327234e3ea0

import Definitions.Def_AllocationIndices_Targets_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm
open AllocationIndices AllocationIndices.Targets

section G70ALT
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma g70al_cp_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] (ρ : Measure A)
    [SFinite ρ] (κ : Kernel A X) [IsSFiniteKernel κ] (η : Kernel B Y) [IsSFiniteKernel η]
    (f : A → B) (hf : Measurable f) (g : X → Y) (hg : Measurable g)
    (h : ∀ z, η (f z) = (κ z).map g) :
    (ρ ⊗ₘ κ).map (Prod.map f g) = (ρ.map f) ⊗ₘ η := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap hg) hs, Measure.compProd_apply (hf.prodMap hg hs),
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  refine lintegral_congr fun z => ?_
  rw [h z, Measure.map_apply hg (measurable_prodMk_left hs)]
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

lemma g70al_mc_map (K1 : Kernel X X) [IsMarkovKernel K1] (K2 : Kernel Y Y) [IsMarkovKernel K2]
    (e : X → Y) (he : Measurable e) (hK : ∀ x, K2 (e x) = (K1 x).map e) (x : X) :
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
      · intro z
        simp only [markovChainStep, Kernel.comap_apply]
        exact hK _
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
    [IsMarkovKernel K2] (E : X ≃ᵐ Y) (hK : ∀ x, K2 (E x) = (K1 x).map E) (r : Y → ℝ) (a : ℝ)
    (x : X) : gittinsIndex K2 r a (E x) = gittinsIndex K1 (fun z => r (E z)) a x := by
  unfold gittinsIndex
  rw [g70al_mc_map K1 K2 E E.measurable hK x]
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
    [IsMarkovKernel K2] (E : X ≃ᵐ Y) (hK : ∀ x, K2 (E x) = (K1 x).map E) (L1 : X → Bool)
    (L2 : Y → Bool) (hL : ∀ z, L2 (E z) = L1 z) (c : ENNReal) (x : X) :
    (⨅ τ : {τ : (ℕ → Y) → ℕ∞ // IsTrajStoppingTime τ},
      (∫⁻ ω, ∑' t : ℕ, (if (t : ℕ∞) < τ.1 ω ∧ L2 (ω t) then (1 : ENNReal) else 0)
        ∂markovChainMeasure K2 (E x)) +
      c * markovChainMeasure K2 (E x) {ω | ∃ m : ℕ, τ.1 ω = (m : ℕ∞) ∧ L2 (ω m)}) =
    (⨅ τ : {τ : (ℕ → X) → ℕ∞ // IsTrajStoppingTime τ},
      (∫⁻ ω, ∑' t : ℕ, (if (t : ℕ∞) < τ.1 ω ∧ L1 (ω t) then (1 : ENNReal) else 0)
        ∂markovChainMeasure K1 x) +
      c * markovChainMeasure K1 x {ω | ∃ m : ℕ, τ.1 ω = (m : ℕ∞) ∧ L1 (ω m)}) := by
  rw [g70al_mc_map K1 K2 E E.measurable hK x]
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

end G70ALS

noncomputable def g70al_sc (b : ℝ) (hb : b ≠ 0) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun p := (b * p.1, p.2)
  invFun p := (b⁻¹ * p.1, p.2)
  left_inv p := by simp [hb]
  right_inv p := by simp [hb]
  measurable_toFun := by change Measurable (fun p : ℝ × ℝ => (b * p.1, p.2)); fun_prop
  measurable_invFun := by change Measurable (fun p : ℝ × ℝ => (b⁻¹ * p.1, p.2)); fun_prop

lemma g70al_sc_pred (F : SamplingModel ℝ (ℝ × ℝ)) (hlik : HasScaleParameter F.likelihood)
    (hprior : PriorHasScaleParameter F.prior) (b : ℝ) (hb : 0 < b) (q : ℝ × ℝ) :
    F.predictive (g70al_sc b hb.ne' q) = (F.predictive q).map (b * ·) := by
  ext s hs
  unfold SamplingModel.predictive
  rw [Kernel.comp_apply' _ _ _ hs, Measure.map_apply (measurable_const_mul b) hs,
    Kernel.comp_apply' _ _ _ (measurable_const_mul b hs)]
  change ∫⁻ θ, F.likelihood θ s ∂F.prior (b * q.1, q.2) = _
  rw [hprior q.1 q.2 b hb, lintegral_map (Kernel.measurable_coe _ hs) (measurable_const_mul b)]
  congr 1; ext θ
  rw [hlik θ b hb, Measure.map_apply (measurable_const_mul b) hs]

open AllocationIndices.Targets

theorem solution (F : SamplingModel ℝ (ℝ × ℝ))
    (hconj : F.IsConjugateOn {p | 0 < p.2})
    (hlik : HasScaleParameter F.likelihood) (hprior : PriorHasScaleParameter F.prior)
    (hupd : F.update = meanUpdate) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (xb n T : ℝ)
    (hn : 0 < n) :
    (∀ φ b : ℝ, 0 < φ → φ ≤ 1 → 0 < b →
      targetCost F T φ (xb, n) = targetCost F (b * T) φ (b * xb, n)) ∧
    (0 < T →
      gittinsIndex (F.targetChain T) (F.targetReward T) a (Sum.inl (xb, n)) =
        gittinsIndex (F.targetChain 1) (F.targetReward 1) a (Sum.inl (xb / T, n))) := by

  have hT' : ∀ b : ℝ, 0 < b → ∀ T x : ℝ, b * T ≤ b * x ↔ T ≤ x := fun b hb T x => by
    constructor <;> intro h <;> nlinarith
  have hup : ∀ b : ℝ, ∀ hb : 0 < b, ∀ q x, F.update (g70al_sc b hb.ne' q) (b * x) =
      g70al_sc b hb.ne' (F.update q x) := by
    intro b hb q x
    rw [hupd]
    change meanUpdate (b * q.1, q.2) (b * x) = (b * (meanUpdate q x).1, (meanUpdate q x).2)
    simp only [meanUpdate]
    congr 1; ring
  have hE : ∀ b : ℝ, ∀ hb : 0 < b, ∀ T : ℝ, ∀ z, F.targetChain (b * T)
      (MeasurableEquiv.sumCongr (g70al_sc b hb.ne') (MeasurableEquiv.refl Unit) z) =
      (F.targetChain T z).map (MeasurableEquiv.sumCongr (g70al_sc b hb.ne') (MeasurableEquiv.refl Unit)) :=
    fun b hb T => g70al_chain_equiv F T (b * T) (g70al_sc b hb.ne') (b * ·) (measurable_const_mul b)
      (g70al_sc_pred F hlik hprior b hb) (hT' b hb T) (hup b hb)
  refine ⟨fun φ b hφ hφ1 hb => ?_, fun hT => ?_⟩
  · unfold targetCost
    exact (g70al_cost_transport (F.targetChain T) (F.targetChain (b * T)) _ (hE b hb T)
      (fun z => z.isLeft) (fun z => z.isLeft) (fun z => by cases z <;> rfl) (ENNReal.ofReal φ⁻¹)
      (Sum.inl (xb, n))).symm
  · have hTi : 0 < T⁻¹ := inv_pos.2 hT
    have := g70al_gittins_transport (F.targetChain T) (F.targetChain (T⁻¹ * T)) _ (hE T⁻¹ hTi T)
      (F.targetReward (T⁻¹ * T)) a (Sum.inl (xb, n))
    have hr : (fun z => F.targetReward (T⁻¹ * T)
        (MeasurableEquiv.sumCongr (g70al_sc T⁻¹ hTi.ne') (MeasurableEquiv.refl Unit) z)) =
        F.targetReward T :=
      funext (g70al_reward_equiv F T (T⁻¹ * T) (g70al_sc T⁻¹ hTi.ne') (T⁻¹ * ·)
        (measurable_const_mul _) (g70al_sc_pred F hlik hprior T⁻¹ hTi) (hT' T⁻¹ hTi T))
    rw [hr] at this
    have h2 : (MeasurableEquiv.sumCongr (g70al_sc T⁻¹ hTi.ne') (MeasurableEquiv.refl Unit))
        (Sum.inl (xb, n)) = Sum.inl (xb / T, n) := by
      change Sum.inl (T⁻¹ * xb, n) = Sum.inl (xb / T, n)
      rw [div_eq_inv_mul]
    rw [h2, inv_mul_cancel₀ hT.ne'] at this
    exact this.symm
