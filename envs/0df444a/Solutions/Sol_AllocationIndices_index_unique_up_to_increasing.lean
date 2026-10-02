-- Prove2me | solution 1 for AllocationIndices.index_unique_up_to_increasing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T12:04:31.967097+00:00
-- url     : https://prove2.me/submissions/e745f227-f844-4bde-bb6f-fb379f316685

import Mathlib
import Definitions.Def_AllocationIndices_Superprocess

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ENNReal Finset Preorder BanditAlgorithm AllocationIndices

namespace P2M2a63

section Gen

variable {S : Type*} [MeasurableSpace S]

lemma chain_eq (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    markovChainMeasure P x = Kernel.traj (markovChainStep P) 0 (fun _ => x) := by
  have h0 : (MeasurableEquiv.piUnique (fun _ : Iic 0 => S)).symm x = fun _ => x := by
    funext i
    have hi : i = default := Subsingleton.elim _ _
    subst hi; rfl
  rw [markovChainMeasure, Kernel.trajMeasure, Measure.map_dirac' (MeasurableEquiv.measurable _), h0,
    Measure.dirac_bind (Kernel.measurable _)]

instance chain_prob (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    IsProbabilityMeasure (markovChainMeasure P x) := by
  rw [chain_eq]; infer_instance

lemma step_apply (P : Kernel S S) (m : ℕ) (z : Π _i : Iic m, S) :
    markovChainStep P m z = P (z ⟨m, mem_Iic.2 le_rfl⟩) := by
  rw [markovChainStep, Kernel.comap_apply]

lemma markov_step0 (P : Kernel S S) [IsMarkovKernel P] (x : S) (m : ℕ)
    (φ : (Π _i : Iic m, S) × S → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ ω, φ (frestrictLe m ω, ω (m+1)) ∂(markovChainMeasure P x) =
      ∫⁻ ω, ∫⁻ y, φ (frestrictLe m ω, y) ∂(P (ω m)) ∂(markovChainMeasure P x) := by
  rw [chain_eq]
  have h1 := Kernel.partialTraj_compProd_eq_map_traj (X := fun _ => S) (κ := markovChainStep P)
    (Nat.zero_le m) (x₀ := fun _ => x)
  have h2 := Kernel.traj_map_frestrictLe (X := fun _ => S) (κ := markovChainStep P) 0 m
  rw [← lintegral_map hφ (by fun_prop), ← h1, Measure.lintegral_compProd hφ]
  simp_rw [step_apply]
  have hF : Measurable (fun z : Π _i : Iic m, S => ∫⁻ y, φ (z, y) ∂(P (z ⟨m, mem_Iic.2 le_rfl⟩))) := by
    have := Measurable.lintegral_kernel_prod_right' (κ := markovChainStep P m) hφ
    simpa only [step_apply] using this
  rw [← h2, Kernel.map_apply _ (measurable_frestrictLe m), lintegral_map hF (measurable_frestrictLe m)]
  rfl

/-- one-step Markov property, general dependence form. -/
lemma markov_step (P : Kernel S S) [IsMarkovKernel P] (x : S) (m : ℕ)
    (Φ : (ℕ → S) → S → ℝ≥0∞) (hΦ : Measurable (Function.uncurry Φ))
    (hdep : ∀ ω ω' y, (∀ v ≤ m, ω v = ω' v) → Φ ω y = Φ ω' y) :
    ∫⁻ ω, Φ ω (ω (m+1)) ∂(markovChainMeasure P x) =
      ∫⁻ ω, ∫⁻ y, Φ ω y ∂(P (ω m)) ∂(markovChainMeasure P x) := by
  let ext : (Π _i : Iic m, S) → ℕ → S := fun z v => z ⟨min v m, mem_Iic.2 (min_le_right _ _)⟩
  have hext : Measurable ext := by
    refine measurable_pi_lambda _ (fun v => measurable_pi_apply _)
  have hre : ∀ ω : ℕ → S, ∀ v ≤ m, ext (frestrictLe m ω) v = ω v := by
    intro ω v hv
    simp [ext, frestrictLe_apply, min_eq_left hv]
  have key := markov_step0 P x m (fun p => Φ (ext p.1) p.2)
    (hΦ.comp ((hext.comp measurable_fst).prodMk measurable_snd))
  have e1 : ∀ ω y, Φ (ext (frestrictLe m ω)) y = Φ ω y := fun ω y => hdep _ _ y (hre ω)
  simp only [e1] at key
  exact key

lemma ae_zero [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    ∀ᵐ ω ∂(markovChainMeasure P x), ω 0 = x := by
  rw [chain_eq]
  have h2 := Kernel.traj_map_frestrictLe (X := fun _ => S) (κ := markovChainStep P) 0 0
  have hm : (Kernel.traj (markovChainStep P) 0 (fun _ => x)).map (frestrictLe (π := fun _ => S) 0) =
      Measure.dirac (fun _ : Iic 0 => x) := by
    rw [← Kernel.map_apply _ (measurable_frestrictLe 0), h2, Kernel.partialTraj_self, Kernel.id_apply]
  have : ∀ᵐ z ∂(Measure.dirac (fun _ : Iic 0 => x)), z ⟨0, mem_Iic.2 le_rfl⟩ = x := by
    rw [ae_dirac_eq]; exact Filter.eventually_pure.2 rfl
  rw [← hm] at this
  exact ae_of_ae_map (measurable_frestrictLe 0).aemeasurable this


lemma stop_meas {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (n : ℕ) :
    MeasurableSet {ω : ℕ → S | τ ω ≤ n} :=
  Measurable.comap_le (measurable_pi_lambda (fun ω (i : Iic n) => ω i.1)
    fun i => measurable_pi_apply _) _ (hτ n)

lemma stop_lt_meas {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (t : ℕ) :
    MeasurableSet {ω : ℕ → S | (t : ℕ∞) < τ ω} := by
  have := (stop_meas hτ t).compl
  simpa only [Set.compl_setOf, not_le] using this

lemma stop_dep {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (n : ℕ) {ω ω' : ℕ → S}
    (h : ∀ v ≤ n, ω v = ω' v) : (τ ω ≤ n ↔ τ ω' ≤ n) := by
  obtain ⟨s, -, hs⟩ := hτ n
  have e : (fun (i : Iic n) => ω i.1) = (fun (i : Iic n) => ω' i.1) :=
    funext fun i => h i.1 (mem_Iic.1 i.2)
  have h1 : ω ∈ (fun ω : ℕ → S => fun (i : Iic n) => ω i.1) ⁻¹' s ↔
      ω' ∈ (fun ω : ℕ → S => fun (i : Iic n) => ω i.1) ⁻¹' s := by
    simp only [Set.mem_preimage, e]
  rw [hs] at h1
  exact h1

lemma disc_trunc (α : ℝ) (f : S → ℝ) (τ : (ℕ → S) → ℕ∞) (n : ℕ) (ω : ℕ → S) :
    discountedStoppedSum α f (fun ω => min (τ ω) n) ω =
      ∑ t ∈ Finset.range n, if (t : ℕ∞) < τ ω then α ^ t * f (ω t) else 0 := by
  unfold discountedStoppedSum
  rw [tsum_eq_sum (s := Finset.range n) (fun t ht => by
    have : ¬ ((t : ℕ∞) < n) := by
      rw [Finset.mem_range] at ht; exact_mod_cast ht
    simp only [lt_min_iff, this, and_false, if_false])]
  refine Finset.sum_congr rfl fun t ht => ?_
  have : (t : ℕ∞) < n := by exact_mod_cast Finset.mem_range.1 ht
  simp only [lt_min_iff, this, and_true]

lemma disc_fin (α : ℝ) (f : S → ℝ) {σ : (ℕ → S) → ℕ∞} {H : ℕ} (hH : ∀ ω, σ ω ≤ H) (ω : ℕ → S) :
    discountedStoppedSum α f σ ω =
      ∑ t ∈ Finset.range H, (if (t : ℕ∞) < σ ω then (1:ℝ) else 0) * α ^ t * f (ω t) := by
  have e : discountedStoppedSum α f σ ω = discountedStoppedSum α f (fun ω => min (σ ω) H) ω := by
    congr 1; exact funext fun ω => (min_eq_left (hH ω)).symm
  rw [e, disc_trunc]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> ring

lemma pw_disc {α : ℝ} (hα0 : 0 < α) (f : S → ℝ) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S)
    (hS : ∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|) ≠ ⊤) :
    (∀ n : ℕ, ‖discountedStoppedSum α f (fun ω => min (τ ω) n) ω‖ ≤
        (∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|)).toReal) ∧
    ‖discountedStoppedSum α f τ ω‖ ≤ (∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|)).toReal ∧
    Filter.Tendsto (fun n : ℕ => discountedStoppedSum α f (fun ω => min (τ ω) n) ω) Filter.atTop
      (nhds (discountedStoppedSum α f τ ω)) := by
  have hnn : ∀ t : ℕ, 0 ≤ α ^ t * |f (ω t)| := fun t => mul_nonneg (pow_pos hα0 t).le (abs_nonneg _)
  have hs : Summable (fun t : ℕ => α ^ t * |f (ω t)|) :=
    (ENNReal.summable_toReal hS).congr fun t => ENNReal.toReal_ofReal (hnn t)
  have hT : (∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|)).toReal = ∑' t, α ^ t * |f (ω t)| := by
    rw [ENNReal.tsum_toReal_eq (fun t => ENNReal.ofReal_ne_top)]
    exact tsum_congr fun t => ENNReal.toReal_ofReal (hnn t)
  let b : ℕ → ℝ := fun t => if (t : ℕ∞) < τ ω then α ^ t * f (ω t) else 0
  have hbn : ∀ t, ‖b t‖ ≤ α ^ t * |f (ω t)| := by
    intro t
    simp only [b]
    split_ifs
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hα0 t)]
    · simpa using hnn t
  have hbs : Summable b := Summable.of_norm_bounded hs hbn
  have hbsn : Summable (fun t => ‖b t‖) := Summable.of_nonneg_of_le (fun t => norm_nonneg _) hbn hs
  rw [hT]
  refine ⟨fun n => ?_, ?_, ?_⟩
  · rw [disc_trunc]
    calc ‖∑ t ∈ Finset.range n, b t‖ ≤ ∑ t ∈ Finset.range n, α ^ t * |f (ω t)| :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => hbn t)
      _ ≤ ∑' t, α ^ t * |f (ω t)| := hs.sum_le_tsum _ (fun t _ => hnn t)
  · exact (norm_tsum_le_tsum_norm hbsn).trans (Summable.tsum_le_tsum hbn hbsn hs)
  · simp only [disc_trunc]
    exact hbs.hasSum.tendsto_sum_nat

lemma dct_disc (P : Kernel S S) [IsMarkovKernel P] {α : ℝ} (hα0 : 0 < α) {f : S → ℝ}
    (hf : Measurable f) (y : S)
    (hfin : ∫⁻ ω, ∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|) ∂(markovChainMeasure P y) < ⊤)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    (∀ n : ℕ, Integrable (fun ω => discountedStoppedSum α f (fun ω => min (τ ω) n) ω)
      (markovChainMeasure P y)) ∧
    Filter.Tendsto (fun n : ℕ => ∫ ω, discountedStoppedSum α f (fun ω => min (τ ω) n) ω
      ∂(markovChainMeasure P y)) Filter.atTop
      (nhds (∫ ω, discountedStoppedSum α f τ ω ∂(markovChainMeasure P y))) ∧
    ‖∫ ω, discountedStoppedSum α f τ ω ∂(markovChainMeasure P y)‖ ≤
      ∫ ω, (∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|)).toReal ∂(markovChainMeasure P y) := by
  have hSm : Measurable (fun ω : ℕ → S => ∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|)) :=
    Measurable.ennreal_tsum fun t => ENNReal.measurable_ofReal.comp
      (measurable_const.mul (hf.comp (measurable_pi_apply t)).abs)
  have hB : Integrable (fun ω : ℕ → S => (∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|)).toReal)
      (markovChainMeasure P y) :=
    integrable_toReal_of_lintegral_ne_top hSm.aemeasurable hfin.ne
  have hae : ∀ᵐ ω ∂(markovChainMeasure P y), ∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|) ≠ ⊤ :=
    (ae_lt_top hSm hfin.ne).mono fun ω h => h.ne
  have hFm : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => discountedStoppedSum α f (fun ω => min (τ ω) n) ω) (markovChainMeasure P y) := by
    intro n
    simp only [disc_trunc]
    refine (Finset.measurable_sum _ fun t _ => ?_).aestronglyMeasurable
    exact Measurable.ite (stop_lt_meas hτ t)
      (measurable_const.mul (hf.comp (measurable_pi_apply t))) measurable_const
  have hbd : ∀ n : ℕ, ∀ᵐ ω ∂(markovChainMeasure P y),
      ‖discountedStoppedSum α f (fun ω => min (τ ω) n) ω‖ ≤
        (∑' t, ENNReal.ofReal (α ^ t * |f (ω t)|)).toReal := fun n =>
    hae.mono fun ω h => (pw_disc hα0 f τ ω h).1 n
  refine ⟨fun n => hB.mono' (hFm n) (hbd n), ?_, ?_⟩
  · exact tendsto_integral_of_dominated_convergence _ hFm hB hbd
      (hae.mono fun ω h => (pw_disc hα0 f τ ω h).2.2)
  · exact norm_integral_le_of_norm_le hB (hae.mono fun ω h => (pw_disc hα0 f τ ω h).2.1)

lemma hfin_one (P : Kernel S S) [IsMarkovKernel P] {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (y : S) :
    ∫⁻ ω, ∑' t, ENNReal.ofReal (α ^ t * |(fun _ : S => (1:ℝ)) (ω t)|)
      ∂(markovChainMeasure P y) < ⊤ := by
  simp only [abs_one, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => (pow_pos hα0 t).le)
    (summable_geometric_of_lt_one hα0.le hα1), lintegral_const, measure_univ, mul_one]
  exact ENNReal.ofReal_lt_top

lemma D_ge_one (P : Kernel S S) [IsMarkovKernel P] {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (y : S)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ) (h1 : ∀ ω, 1 ≤ τ ω) :
    1 ≤ ∫ ω, discountedStoppedSum α (fun _ => 1) τ ω ∂(markovChainMeasure P y) := by
  obtain ⟨hI, hT, -⟩ := dct_disc P hα0 measurable_const y (hfin_one P hα0 hα1 y) hτ
  refine ge_of_tendsto hT (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hpt : ∀ ω, (1:ℝ) ≤ discountedStoppedSum α (fun _ => (1:ℝ)) (fun ω => min (τ ω) n) ω := by
    intro ω
    rw [disc_trunc]
    have h0 : (0:ℕ) ∈ Finset.range n := Finset.mem_range.2 (by omega)
    have hτ0 : ((0:ℕ) : ℕ∞) < τ ω := lt_of_lt_of_le (by norm_num) (h1 ω)
    calc (1:ℝ) = if ((0:ℕ):ℕ∞) < τ ω then α ^ 0 * 1 else 0 := by rw [if_pos hτ0]; simp
      _ ≤ ∑ t ∈ Finset.range n, if (t : ℕ∞) < τ ω then α ^ t * 1 else 0 :=
          Finset.single_le_sum (f := fun t : ℕ => if (t:ℕ∞) < τ ω then α ^ t * 1 else 0)
            (fun t _ => by split_ifs <;> positivity) h0
  calc (1:ℝ) = ∫ _ω, (1:ℝ) ∂(markovChainMeasure P y) := by simp
    _ ≤ _ := integral_mono (integrable_const 1) (hI n) hpt

lemma gi_bdd (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hint : DiscountedRewardIntegrable P r α) (y : S) :
    BddAbove {g : ℝ | ∃ τ : (ℕ → S) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      g = (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)} := by
  refine ⟨∫ ω, (∑' t, ENNReal.ofReal (α ^ t * |r (ω t)|)).toReal ∂(markovChainMeasure P y), ?_⟩
  rintro _ ⟨τ, hτ, h1, rfl⟩
  have hD := D_ge_one P hα0 hα1 y hτ h1
  have hN := (dct_disc P hα0 hr y (hint y) hτ).2.2
  rw [Real.norm_eq_abs] at hN
  calc _ ≤ |∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y| /
        (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω ∂markovChainMeasure P y) := by
        gcongr; exact le_abs_self _
    _ ≤ |∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y| := div_le_self (abs_nonneg _) hD
    _ ≤ _ := hN


end Gen

instance instMSCSum {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) := by
  constructor
  rintro (a | b)
  · rw [← Set.image_singleton]; exact (measurableSet_singleton a).inl_image
  · rw [← Set.image_singleton]; exact (measurableSet_singleton b).inr_image

section Main

variable {T : Type} [MeasurableSpace T] [Countable T] [MeasurableSingletonClass T]

/-! ### Stop-then-switch histories -/

noncomputable def st (σ : (ℕ → T) → ℕ∞) : ℕ → (ℕ → T) → (Fin 2 → T ⊕ Unit)
  | 0, ω => twoStates (ω 0) ()
  | n + 1, ω => if (n : ℕ∞) < σ ω then twoStates (ω (n + 1)) () else st σ n ω

noncomputable def act (σ : (ℕ → T) → ℕ∞) (n : ℕ) (ω : ℕ → T) : Fin 2 :=
  if (n : ℕ∞) < σ ω then 0 else 1

noncomputable def phi (σ : (ℕ → T) → ℕ∞) (n : ℕ) (ω : ℕ → T) :
    MarkovBanditHistory 2 (T ⊕ Unit) n :=
  (fun u : Fin n => (st σ u ω, act σ u ω), st σ n ω)

noncomputable def phi' (σ : (ℕ → T) → ℕ∞) (n : ℕ) (ω : ℕ → T) (y : T) :
    MarkovBanditHistory 2 (T ⊕ Unit) (n + 1) :=
  (Fin.snoc (α := fun _ => (Fin 2 → T ⊕ Unit) × Fin 2) (phi σ n ω).1 ((phi σ n ω).2, act σ n ω),
    if (n : ℕ∞) < σ ω then twoStates y () else st σ n ω)

noncomputable def mkPol (f : ∀ n, MarkovBanditHistory 2 (T ⊕ Unit) n → Fin 2) :
    MarkovBanditPolicy 2 (T ⊕ Unit) :=
  ⟨fun n => Kernel.deterministic (f n) Measurable.of_discrete, fun _ => inferInstance⟩

lemma st_one (σ : (ℕ → T) → ℕ∞) (n : ℕ) (ω : ℕ → T) : st σ n ω 1 = Sum.inr () := by
  induction n with
  | zero => simp [st, twoStates]
  | succ n ih =>
    simp only [st]
    split_ifs
    · simp [twoStates]
    · exact ih

lemma st_eq (σ : (ℕ → T) → ℕ∞) (n : ℕ) (ω : ℕ → T) (h : (n : ℕ∞) ≤ σ ω) :
    st σ n ω = twoStates (ω n) () := by
  cases n with
  | zero => rfl
  | succ n =>
    have h' : (n : ℕ∞) < σ ω := by
      have : ((n : ℕ) : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self n
      exact lt_of_lt_of_le this h
    simp only [st, if_pos h']

lemma st_frozen (σ : (ℕ → T) → ℕ∞) (ω : ℕ → T) (s : ℕ) (hs : σ ω = s) :
    ∀ n, s ≤ n → st σ n ω = st σ s ω := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have : ¬ ((n : ℕ∞) < σ ω) := by rw [hs, not_lt]; exact_mod_cast hn
    simp only [st, if_neg this]; exact ih

lemma meas_two : Measurable (fun y : T => (twoStates y () : Fin 2 → T ⊕ Unit)) :=
  Measurable.of_discrete

lemma st_meas {σ : (ℕ → T) → ℕ∞} (hσ : IsTrajStoppingTime σ) (n : ℕ) :
    Measurable (st σ n) := by
  induction n with
  | zero =>
    have e : st σ 0 = fun ω : ℕ → T => twoStates (ω 0) () := by funext ω; rfl
    rw [e]; exact meas_two.comp (measurable_pi_apply 0)
  | succ n ih =>
    have e : st σ (n + 1) = fun ω : ℕ → T =>
        if (n : ℕ∞) < σ ω then twoStates (ω (n + 1)) () else st σ n ω := by funext ω; rfl
    rw [e]
    exact Measurable.ite (stop_lt_meas hσ n) (meas_two.comp (measurable_pi_apply (n + 1))) ih

lemma act_meas {σ : (ℕ → T) → ℕ∞} (hσ : IsTrajStoppingTime σ) (n : ℕ) :
    Measurable (act σ n) := by
  have e : act σ n = fun ω : ℕ → T => if (n : ℕ∞) < σ ω then (0 : Fin 2) else 1 := by
    funext ω; rfl
  rw [e]
  exact Measurable.ite (stop_lt_meas hσ n) measurable_const measurable_const

lemma phi_meas {σ : (ℕ → T) → ℕ∞} (hσ : IsTrajStoppingTime σ) (n : ℕ) :
    Measurable (phi σ n) := by
  have e : phi σ n = fun ω : ℕ → T =>
      ((fun u : Fin n => (st σ u ω, act σ u ω)), st σ n ω) := by funext ω; rfl
  rw [e]
  exact (measurable_pi_lambda (fun ω (u : Fin n) => (st σ u ω, act σ u ω))
    fun u => (st_meas hσ u).prodMk (act_meas hσ u)).prodMk (st_meas hσ n)

lemma phi'_meas {σ : (ℕ → T) → ℕ∞} (hσ : IsTrajStoppingTime σ) (n : ℕ) :
    Measurable (fun p : (ℕ → T) × T => phi' σ n p.1 p.2) := by
  unfold phi'
  refine Measurable.prodMk ?_ ?_
  · exact measurable_finSnoc.comp
      (((measurable_fst.comp (phi_meas hσ n)).comp measurable_fst).prodMk
        (((measurable_snd.comp (phi_meas hσ n)).comp measurable_fst).prodMk
          ((act_meas hσ n).comp measurable_fst)))
  · have hs : MeasurableSet {p : (ℕ → T) × T | (n : ℕ∞) < σ p.1} :=
      measurable_fst (stop_lt_meas hσ n)
    exact Measurable.ite hs (meas_two.comp measurable_snd) ((st_meas hσ n).comp measurable_fst)

lemma lt_dep {σ : (ℕ → T) → ℕ∞} (hσ : IsTrajStoppingTime σ) {n : ℕ} {ω ω' : ℕ → T}
    (h : ∀ v ≤ n, ω v = ω' v) : ((n : ℕ∞) < σ ω ↔ (n : ℕ∞) < σ ω') := by
  rw [← not_le, ← not_le, stop_dep hσ n h]

lemma st_dep {σ : (ℕ → T) → ℕ∞} (hσ : IsTrajStoppingTime σ) {n : ℕ} {ω ω' : ℕ → T}
    (h : ∀ v ≤ n, ω v = ω' v) : ∀ u ≤ n, st σ u ω = st σ u ω' := by
  intro u hu
  induction u with
  | zero => simp only [st, h 0 (Nat.zero_le _)]
  | succ u ih =>
    simp only [st]
    rw [if_congr (lt_dep hσ (n := u) (fun v hv => h v (by omega))) rfl rfl, h (u + 1) hu,
      ih (by omega)]

lemma phi'_dep {σ : (ℕ → T) → ℕ∞} (hσ : IsTrajStoppingTime σ) {n : ℕ} {ω ω' : ℕ → T}
    (h : ∀ v ≤ n, ω v = ω' v) (y : T) : phi' σ n ω y = phi' σ n ω' y := by
  have hs : ∀ u ≤ n, st σ u ω = st σ u ω' := st_dep hσ h
  have ha : ∀ u ≤ n, act σ u ω = act σ u ω' := fun u hu => by
    unfold act; rw [if_congr (lt_dep hσ (fun v hv => h v (hv.trans hu))) rfl rfl]
  have hl := lt_dep hσ h
  have hphi : phi σ n ω = phi σ n ω' := by
    unfold phi
    rw [hs n le_rfl]
    congr 1
    funext u
    rw [hs u u.2.le, ha u u.2.le]
  unfold phi'
  rw [hphi, ha n le_rfl, if_congr hl rfl rfl, hs n le_rfl]

lemma phi_succ (σ : (ℕ → T) → ℕ∞) (n : ℕ) (ω : ℕ → T) :
    phi σ (n + 1) ω = phi' σ n ω (ω (n + 1)) := by
  unfold phi' phi
  refine Prod.ext ?_ rfl
  dsimp only
  funext u
  induction u using Fin.lastCases with
  | last => simp only [Fin.snoc_last, Fin.val_last]
  | cast i => simp only [Fin.snoc_castSucc, Fin.coe_castSucc]

lemma upd0 (z y : T) :
    Function.update (twoStates z () : Fin 2 → T ⊕ Unit) 0 (Sum.inl y) = twoStates y () := by
  funext i; fin_cases i <;> simp [twoStates]

lemma gg_lt (σ : (ℕ → T) → ℕ∞) (n : ℕ) (ω : ℕ → T) (hlt : (n : ℕ∞) < σ ω) (y : T) :
    ((Fin.snoc (α := fun _ => (Fin 2 → T ⊕ Unit) × Fin 2) (phi σ n ω).1
        ((phi σ n ω).2, act σ n ω),
      Function.update (phi σ n ω).2 (act σ n ω) (Sum.inl y)) :
        MarkovBanditHistory 2 (T ⊕ Unit) (n + 1)) = phi' σ n ω y := by
  have hact : act σ n ω = 0 := by simp [act, hlt]
  have h2 : (phi σ n ω).2 = twoStates (ω n) () := st_eq σ n ω hlt.le
  unfold phi'
  rw [if_pos hlt, hact, h2, upd0]

lemma gg_ge (σ : (ℕ → T) → ℕ∞) (n : ℕ) (ω : ℕ → T) (hlt : ¬ (n : ℕ∞) < σ ω) (y : T) :
    phi' σ n ω y =
    ((Fin.snoc (α := fun _ => (Fin 2 → T ⊕ Unit) × Fin 2) (phi σ n ω).1
        ((phi σ n ω).2, act σ n ω),
      Function.update (phi σ n ω).2 (act σ n ω) (Sum.inr ())) :
        MarkovBanditHistory 2 (T ⊕ Unit) (n + 1)) := by
  have hact : act σ n ω = 1 := by simp [act, hlt]
  unfold phi'
  rw [if_neg hlt, hact]
  congr 1
  have h1 : (phi σ n ω).2 1 = Sum.inr () := st_one σ n ω
  rw [← h1, Function.update_eq_self]
  rfl

lemma Q_inl (P : Kernel T T) (z : T) :
    sumKernel P standardKernel (Sum.inl z) = (P z).map Sum.inl := by
  show (P.map Sum.inl) z = _
  rw [Kernel.map_apply _ measurable_inl]

lemma Q_inr (P : Kernel T T) :
    sumKernel P standardKernel (Sum.inr ()) = Measure.dirac (Sum.inr () : T ⊕ Unit) := by
  show (standardKernel.map Sum.inr) () = _
  rw [Kernel.map_apply _ measurable_inr, standardKernel, Kernel.const_apply,
    Measure.map_dirac' (measurable_inr (α := T) (β := Unit)) ()]

/-! ### The law of a stop-then-switch policy -/

theorem law (P : Kernel T T) [IsMarkovKernel P] {σ : (ℕ → T) → ℕ∞} (hσ : IsTrajStoppingTime σ)
    (x : T) (f : ∀ n, MarkovBanditHistory 2 (T ⊕ Unit) n → Fin 2)
    (hf : ∀ n ω, ω 0 = x → f n (phi σ n ω) = act σ n ω) (n : ℕ) :
    markovBanditMeasure (sumKernel P standardKernel) (mkPol f) (twoStates x ()) n =
      (markovChainMeasure P x).map (phi σ n) := by
  induction n with
  | zero =>
    have hae : phi σ 0 =ᵐ[markovChainMeasure P x]
        fun _ => ((fun t => t.elim0), (twoStates x () : Fin 2 → T ⊕ Unit)) := by
      filter_upwards [ae_zero P x] with ω hω
      refine Prod.ext (funext fun t => t.elim0) ?_
      show st σ 0 ω = twoStates x ()
      simp only [st, hω]
    rw [markovBanditMeasure, Measure.map_congr hae, Measure.map_const, measure_univ, one_smul]
  | succ n ih =>
    rw [markovBanditMeasure, ih]
    ext A hA
    rw [Measure.map_apply measurable_markovBanditSnoc hA,
      Measure.compProd_apply (measurable_markovBanditSnoc hA),
      lintegral_map Measurable.of_discrete (phi_meas hσ n), Measure.map_apply (phi_meas hσ (n + 1)) hA]
    have hR : markovChainMeasure P x (phi σ (n + 1) ⁻¹' A) =
        ∫⁻ ω, A.indicator 1 (phi' σ n ω (ω (n + 1))) ∂markovChainMeasure P x := by
      rw [← lintegral_indicator_one ((phi_meas hσ (n + 1)) hA)]
      refine lintegral_congr fun ω => ?_
      rw [← phi_succ]; rfl
    rw [hR]
    refine Eq.trans ?_ (markov_step P x n (fun ω y => A.indicator 1 (phi' σ n ω y))
      ((measurable_one.indicator hA).comp (phi'_meas hσ n)) (fun ω ω' y h => by
        rw [phi'_dep hσ h])).symm
    refine lintegral_congr_ae ?_
    filter_upwards [ae_zero P x] with ω hω
    rw [markovBanditStepKernel, Kernel.compProd_apply MeasurableSet.of_discrete]
    simp only [mkPol, Kernel.deterministic_apply, lintegral_dirac, Kernel.comap_apply]
    rw [hf n ω hω]
    by_cases hlt : (n : ℕ∞) < σ ω
    · have hz : (phi σ n ω).2 (act σ n ω) = Sum.inl (ω n) := by
        have hact : act σ n ω = 0 := by simp [act, hlt]
        rw [hact]
        show st σ n ω 0 = _
        rw [st_eq σ n ω hlt.le]; rfl
      rw [hz, Q_inl, Measure.map_apply measurable_inl MeasurableSet.of_discrete,
        ← lintegral_indicator_one MeasurableSet.of_discrete]
      refine lintegral_congr fun y => ?_
      rw [← gg_lt σ n ω hlt y]
      rfl
    · have hz : (phi σ n ω).2 (act σ n ω) = Sum.inr () := by
        have hact : act σ n ω = 1 := by simp [act, hlt]
        rw [hact]
        exact st_one σ n ω
      rw [hz, Q_inr, Measure.dirac_apply]
      simp_rw [gg_ge σ n ω hlt]
      rw [lintegral_const, measure_univ, mul_one]
      rfl

theorem round_eq (P : Kernel T T) [IsMarkovKernel P] {σ : (ℕ → T) → ℕ∞}
    (hσ : IsTrajStoppingTime σ) (x : T) (f : ∀ n, MarkovBanditHistory 2 (T ⊕ Unit) n → Fin 2)
    (hf : ∀ n ω, ω 0 = x → f n (phi σ n ω) = act σ n ω) (r : T → ℝ) (lam : ℝ) (t : ℕ) :
    markovBanditRoundReward (sumKernel P standardKernel) (sumReward r (fun _ : Unit => lam))
        (mkPol f) (twoStates x ()) t =
      ∫ ω, (if (t : ℕ∞) < σ ω then r (ω t) else lam) ∂markovChainMeasure P x := by
  rw [markovBanditRoundReward, law P hσ x f hf (t + 1),
    integral_map (phi_meas hσ (t + 1)).aemeasurable Measurable.of_discrete.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [phi, Fin.val_last]
  by_cases h : (t : ℕ∞) < σ ω
  · simp only [act, if_pos h, st_eq σ t ω h.le]; rfl
  · simp only [act, if_neg h, st_one]; rfl

/-! ### Values -/

lemma ite_bound {σ : (ℕ → T) → ℕ∞} {g : T → ℝ} {C : ℝ} (hC : ∀ y, |g y| ≤ C) (t : ℕ)
    (ω : ℕ → T) : ‖(if (t : ℕ∞) < σ ω then g (ω t) else 0)‖ ≤ C := by
  have h0 : 0 ≤ C := (abs_nonneg _).trans (hC (ω 0))
  split_ifs
  · rw [Real.norm_eq_abs]; exact hC _
  · simpa using h0

lemma ite_int (P : Kernel T T) [IsMarkovKernel P] (x : T) {σ : (ℕ → T) → ℕ∞}
    (hσ : IsTrajStoppingTime σ) {g : T → ℝ} {C : ℝ} (hC : ∀ y, |g y| ≤ C) (t : ℕ) :
    Integrable (fun ω : ℕ → T => if (t : ℕ∞) < σ ω then g (ω t) else 0)
      (markovChainMeasure P x) :=
  Integrable.of_bound (Measurable.ite (stop_lt_meas hσ t)
    ((Measurable.of_discrete : Measurable g).comp (measurable_pi_apply t))
    measurable_const).aestronglyMeasurable C (Filter.Eventually.of_forall (ite_bound hC t))

lemma ite_abs (P : Kernel T T) [IsMarkovKernel P] (x : T) {σ : (ℕ → T) → ℕ∞}
    {g : T → ℝ} {C : ℝ} (hC : ∀ y, |g y| ≤ C) (t : ℕ) :
    ‖∫ ω, (if (t : ℕ∞) < σ ω then g (ω t) else 0) ∂markovChainMeasure P x‖ ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := markovChainMeasure P x)
    (Filter.Eventually.of_forall (ite_bound (σ := σ) hC t))
  simpa using this

lemma int_dss (P : Kernel T T) [IsMarkovKernel P] {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {g : T → ℝ} {C : ℝ} (hC : ∀ y, |g y| ≤ C) {σ : (ℕ → T) → ℕ∞}
    (hσ : IsTrajStoppingTime σ) (x : T) :
    ∫ ω, discountedStoppedSum a g σ ω ∂markovChainMeasure P x =
      ∑' t : ℕ, a ^ t * ∫ ω, (if (t : ℕ∞) < σ ω then g (ω t) else 0) ∂markovChainMeasure P x := by
  have hint := ite_int P x hσ hC
  unfold discountedStoppedSum
  have e : ∀ t : ℕ, ∀ ω : ℕ → T, (if (t : ℕ∞) < σ ω then a ^ t * g (ω t) else 0) =
      a ^ t * (if (t : ℕ∞) < σ ω then g (ω t) else 0) := by
    intro t ω; split_ifs <;> simp
  simp_rw [e]
  rw [← integral_tsum_of_summable_integral_norm (fun t => (hint t).const_mul (a ^ t)) ?_]
  · simp_rw [integral_const_mul]
  · refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun ω => norm_nonneg _)
      (fun t => ?_) ((summable_geometric_of_lt_one ha0.le ha1).mul_right C)
    calc ∫ ω, ‖a ^ t * (if (t : ℕ∞) < σ ω then g (ω t) else 0)‖ ∂markovChainMeasure P x
        ≤ ∫ ω, a ^ t * C ∂markovChainMeasure P x := by
          refine integral_mono ((hint t).const_mul (a ^ t)).norm (integrable_const _) fun ω => ?_
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos (pow_pos ha0 t)]
          exact mul_le_mul_of_nonneg_left (ite_bound hC t ω) (pow_pos ha0 t).le
      _ = a ^ t * C := by simp

theorem value_eq (P : Kernel T T) [IsMarkovKernel P] {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {r : T → ℝ} {M : ℝ} (hM : ∀ y, |r y| ≤ M) (lam : ℝ) {σ : (ℕ → T) → ℕ∞}
    (hσ : IsTrajStoppingTime σ) (x : T) (f : ∀ n, MarkovBanditHistory 2 (T ⊕ Unit) n → Fin 2)
    (hf : ∀ n ω, ω 0 = x → f n (phi σ n ω) = act σ n ω) :
    markovBanditDiscountedValue (sumKernel P standardKernel) (sumReward r (fun _ : Unit => lam)) a
        (mkPol f) (twoStates x ()) =
      (∫ ω, discountedStoppedSum a r σ ω ∂markovChainMeasure P x) + lam * (1 - a)⁻¹ -
        lam * ∫ ω, discountedStoppedSum a (fun _ => (1 : ℝ)) σ ω ∂markovChainMeasure P x := by
  have h1 : ∀ y : T, |(fun _ : T => (1 : ℝ)) y| ≤ 1 := fun _ => by simp
  rw [int_dss P ha0 ha1 hM hσ x, int_dss P ha0 ha1 h1 hσ x]
  unfold markovBanditDiscountedValue
  simp_rw [round_eq P hσ x f hf r lam]
  set A : ℕ → ℝ := fun t => ∫ ω, (if (t : ℕ∞) < σ ω then r (ω t) else 0) ∂markovChainMeasure P x
    with hAdef
  set B : ℕ → ℝ := fun t => ∫ ω, (if (t : ℕ∞) < σ ω then (fun _ : T => (1 : ℝ)) (ω t) else 0)
    ∂markovChainMeasure P x with hBdef
  have hsplit : ∀ t : ℕ, ∫ ω, (if (t : ℕ∞) < σ ω then r (ω t) else lam) ∂markovChainMeasure P x =
      A t + lam - lam * B t := by
    intro t
    have e : (fun ω : ℕ → T => if (t : ℕ∞) < σ ω then r (ω t) else lam) =
        fun ω => (if (t : ℕ∞) < σ ω then r (ω t) else 0) +
          (lam - lam * (if (t : ℕ∞) < σ ω then (fun _ : T => (1 : ℝ)) (ω t) else 0)) := by
      funext ω; split_ifs <;> simp
    have i2 : Integrable (fun ω : ℕ → T => lam - lam *
        (if (t : ℕ∞) < σ ω then (fun _ : T => (1 : ℝ)) (ω t) else 0)) (markovChainMeasure P x) :=
      (integrable_const lam).sub ((ite_int P x hσ h1 t).const_mul lam)
    rw [e, integral_add (ite_int P x hσ hM t) i2,
      integral_sub (integrable_const lam) ((ite_int P x hσ h1 t).const_mul lam),
      integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul, smul_eq_mul, one_mul, hAdef, hBdef]
    ring
  simp_rw [hsplit]
  have hgeo := summable_geometric_of_lt_one ha0.le ha1
  have hsA : Summable (fun t => a ^ t * A t) := by
    refine Summable.of_norm_bounded (hgeo.mul_right M) (fun t => ?_)
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (pow_pos ha0 t)]
    exact mul_le_mul_of_nonneg_left (ite_abs P x hM t) (pow_pos ha0 t).le
  have hsB : Summable (fun t => a ^ t * B t) := by
    refine Summable.of_norm_bounded (hgeo.mul_right 1) (fun t => ?_)
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (pow_pos ha0 t)]
    exact mul_le_mul_of_nonneg_left (ite_abs P x h1 t) (pow_pos ha0 t).le
  have e2 : (fun t => a ^ t * (A t + lam - lam * B t)) =
      fun t => (a ^ t * A t + lam * a ^ t) - lam * (a ^ t * B t) := by
    funext t; ring
  rw [e2, Summable.tsum_sub (hsA.add (hgeo.mul_left lam)) (hsB.mul_left lam),
    Summable.tsum_add hsA (hgeo.mul_left lam), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one ha0.le ha1]

lemma val_abs_le {S : Type*} [MeasurableSpace S] (Q : Kernel S S) [IsMarkovKernel Q]
    (ρ : S → ℝ) {C : ℝ} (hC : ∀ s, |ρ s| ≤ C) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (π : MarkovBanditPolicy 2 S) (y : Fin 2 → S) :
    |markovBanditDiscountedValue Q ρ a π y| ≤ C * (1 - a)⁻¹ := by
  have hR : ∀ t, |markovBanditRoundReward Q ρ π y t| ≤ C := by
    intro t
    have := norm_integral_le_of_norm_le_const (μ := markovBanditMeasure Q π y (t + 1))
      (f := fun h => ρ ((h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2))) (C := C)
      (Filter.Eventually.of_forall fun h => by rw [Real.norm_eq_abs]; exact hC _)
    simpa [markovBanditRoundReward, Real.norm_eq_abs] using this
  have hs : Summable (fun t : ℕ => a ^ t * C) :=
    (summable_geometric_of_lt_one ha0.le ha1).mul_right C
  have hb : ∀ t, ‖a ^ t * markovBanditRoundReward Q ρ π y t‖ ≤ a ^ t * C := by
    intro t
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos ha0 t)]
    exact mul_le_mul_of_nonneg_left (hR t) (pow_pos ha0 t).le
  have hsn : Summable (fun t => ‖a ^ t * markovBanditRoundReward Q ρ π y t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs
  rw [← Real.norm_eq_abs]
  unfold markovBanditDiscountedValue
  calc _ ≤ ∑' t, ‖a ^ t * markovBanditRoundReward Q ρ π y t‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' t, a ^ t * C := Summable.tsum_le_tsum hb hsn hs
    _ = C * (1 - a)⁻¹ := by rw [tsum_mul_right, tsum_geometric_of_lt_one ha0.le ha1, mul_comm]

lemma bdd_vals (P : Kernel T T) [IsMarkovKernel P] {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {r : T → ℝ} {M : ℝ} (hM : ∀ y, |r y| ≤ M) (lam : ℝ) (y : Fin 2 → T ⊕ Unit) :
    BddAbove (Set.range fun π' : MarkovBanditPolicy 2 (T ⊕ Unit) =>
      markovBanditDiscountedValue (sumKernel P standardKernel) (sumReward r (fun _ : Unit => lam))
        a π' y) := by
  have hC : ∀ s : T ⊕ Unit, |sumReward r (fun _ : Unit => lam) s| ≤ max M |lam| := by
    rintro (z | u)
    · exact (hM z).trans (le_max_left _ _)
    · exact le_max_right _ _
  refine ⟨max M |lam| * (1 - a)⁻¹, ?_⟩
  rintro _ ⟨π, rfl⟩
  exact (le_abs_self _).trans (val_abs_le _ _ hC ha0 ha1 π y)

lemma hint_of_bdd (P : Kernel T T) [IsMarkovKernel P] {r : T → ℝ} {M : ℝ} (hM : ∀ y, |r y| ≤ M)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : DiscountedRewardIntegrable P r a := by
  intro y
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM y)
  calc ∫⁻ ω, ∑' t : ℕ, ENNReal.ofReal (a ^ t * |r (ω t)|) ∂markovChainMeasure P y
      ≤ ∫⁻ ω, ∑' t : ℕ, ENNReal.ofReal (a ^ t * M) ∂markovChainMeasure P y :=
        lintegral_mono fun ω => ENNReal.tsum_le_tsum fun t =>
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hM _) (pow_pos ha0 t).le)
    _ = ∑' t : ℕ, ENNReal.ofReal (a ^ t * M) := by rw [lintegral_const, measure_univ, mul_one]
    _ < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => mul_nonneg (pow_pos ha0 t).le hM0)
          ((summable_geometric_of_lt_one ha0.le ha1).mul_right M)]
        exact ENNReal.ofReal_lt_top

lemma dss_zero (μ : Measure (ℕ → T)) (a : ℝ) (g : T → ℝ) :
    ∫ ω, discountedStoppedSum a g (fun _ => (0 : ℕ∞)) ω ∂μ = 0 := by
  simp [discountedStoppedSum]

lemma stop0 : IsTrajStoppingTime (fun _ : ℕ → T => (0 : ℕ∞)) := fun _ => MeasurableSet.const _

lemma stop1 : IsTrajStoppingTime (fun _ : ℕ → T => (1 : ℕ∞)) := fun _ => MeasurableSet.const _

lemma hf1 (x : T) : ∀ n (ω : ℕ → T), ω 0 = x →
    (fun n (_ : MarkovBanditHistory 2 (T ⊕ Unit) n) => (1 : Fin 2)) n
      (phi (fun _ => (0 : ℕ∞)) n ω) = act (fun _ => (0 : ℕ∞)) n ω := by
  intro n ω _
  simp [act]

/-! ### Hitting times -/

noncomputable def hitT (s : Set T) (ω : ℕ → T) : ℕ∞ :=
  sInf ((fun t : ℕ => (t : ℕ∞)) '' {t | 1 ≤ t ∧ ω t ∈ s})

lemma hitT_one (s : Set T) (ω : ℕ → T) : 1 ≤ hitT s ω :=
  le_sInf (by rintro _ ⟨t, ⟨ht, -⟩, rfl⟩; show (1 : ℕ∞) ≤ (t : ℕ∞); exact_mod_cast ht)

lemma hitT_le_of (s : Set T) (ω : ℕ → T) (t : ℕ) (h1 : 1 ≤ t) (hs : ω t ∈ s) :
    hitT s ω ≤ t :=
  sInf_le (show (t : ℕ∞) ∈ (fun t : ℕ => (t : ℕ∞)) '' {t | 1 ≤ t ∧ ω t ∈ s} from
    ⟨t, ⟨h1, hs⟩, rfl⟩)

lemma hitT_le_iff (s : Set T) (ω : ℕ → T) (n : ℕ) :
    hitT s ω ≤ n ↔ ∃ t, t ≤ n ∧ 1 ≤ t ∧ ω t ∈ s := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have h2 : ((n + 1 : ℕ) : ℕ∞) ≤ hitT s ω := le_sInf (by
      rintro _ ⟨t, ⟨ht1, hts⟩, rfl⟩
      have : n < t := by
        by_contra hc
        exact hne t (by omega) ht1 hts
      show ((n + 1 : ℕ) : ℕ∞) ≤ (t : ℕ∞)
      exact_mod_cast this)
    have h3 : ((n + 1 : ℕ) : ℕ∞) ≤ n := h2.trans h
    have : n + 1 ≤ n := by exact_mod_cast h3
    omega
  · rintro ⟨t, htn, ht1, hts⟩
    exact (hitT_le_of s ω t ht1 hts).trans (by exact_mod_cast htn)

lemma hitT_stop (s : Set T) : IsTrajStoppingTime (hitT s) := by
  intro n
  refine MeasurableSpace.measurableSet_comap.2
    ⟨{z : (Finset.Iic n) → T | ∃ i : Finset.Iic n, 1 ≤ (i : ℕ) ∧ z i ∈ s},
      MeasurableSet.of_discrete, ?_⟩
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq, hitT_le_iff]
  constructor
  · rintro ⟨i, hi1, his⟩; exact ⟨i, Finset.mem_Iic.1 i.2, hi1, his⟩
  · rintro ⟨t, htn, ht1, hts⟩; exact ⟨⟨t, Finset.mem_Iic.2 htn⟩, ht1, hts⟩

lemma hitT_lt (s : Set T) (ω : ℕ → T) (n : ℕ) (hlt : (n : ℕ∞) < hitT s ω) (hn : 1 ≤ n) :
    ω n ∉ s := fun hs => (not_le.2 hlt) ((hitT_le_iff s ω n).2 ⟨n, le_rfl, hn, hs⟩)

lemma hitT_val (s : Set T) (ω : ℕ → T) (s0 : ℕ) (h : hitT s ω = s0) : ω s0 ∈ s := by
  obtain ⟨t, hts0, ht1, hts⟩ := (hitT_le_iff s ω s0).1 h.le
  have h1 : hitT s ω ≤ t := hitT_le_of s ω t ht1 hts
  rw [h] at h1
  have h2 : s0 ≤ t := by exact_mod_cast h1
  have h3 : t = s0 := by omega
  rwa [h3] at hts

/-! ### The three policies -/

noncomputable def fA (v : T ⊕ Unit → ℝ) (n : ℕ) (h : MarkovBanditHistory 2 (T ⊕ Unit) n) :
    Fin 2 :=
  if v (h.2 1) ≤ v (h.2 0) then 0 else 1

noncomputable def fB (v : T ⊕ Unit → ℝ) (n : ℕ) (h : MarkovBanditHistory 2 (T ⊕ Unit) n) :
    Fin 2 :=
  if v (h.2 0) ≤ v (h.2 1) then 1 else 0

noncomputable def extH (x : T) (n : ℕ) (h : MarkovBanditHistory 2 (T ⊕ Unit) n) : ℕ → T :=
  fun t => if ht : t < n then Sum.elim id (fun _ => x) ((h.1 ⟨t, ht⟩).1 0)
    else Sum.elim id (fun _ => x) (h.2 0)

open Classical in
noncomputable def fT (τ : (ℕ → T) → ℕ∞) (x : T) (n : ℕ)
    (h : MarkovBanditHistory 2 (T ⊕ Unit) n) : Fin 2 :=
  if (∀ u : Fin n, (h.1 u).2 = 0) ∧ ¬ (τ (extH x n h) ≤ n) then 0 else 1

lemma idxA (v : T ⊕ Unit → ℝ) : ∀ t (h : MarkovBanditHistory 2 (T ⊕ Unit) t),
    ((mkPol (fA v)).select t) h {i | ∀ j, v (h.2 j) ≤ v (h.2 i)} = 1 := by
  intro t h
  simp only [mkPol, Kernel.deterministic_apply]
  apply Measure.dirac_apply_of_mem
  simp only [Set.mem_setOf_eq, Fin.forall_fin_two, fA]
  split_ifs with hc
  · exact ⟨le_rfl, hc⟩
  · push_neg at hc; exact ⟨hc.le, le_rfl⟩

lemma idxB (v : T ⊕ Unit → ℝ) : ∀ t (h : MarkovBanditHistory 2 (T ⊕ Unit) t),
    ((mkPol (fB v)).select t) h {i | ∀ j, v (h.2 j) ≤ v (h.2 i)} = 1 := by
  intro t h
  simp only [mkPol, Kernel.deterministic_apply]
  apply Measure.dirac_apply_of_mem
  simp only [Set.mem_setOf_eq, Fin.forall_fin_two, fB]
  split_ifs with hc
  · exact ⟨hc, le_rfl⟩
  · push_neg at hc; exact ⟨le_rfl, hc.le⟩

lemma hfA (v0 : T → ℝ) (m : ℝ) (x : T) (hx : m ≤ v0 x) : ∀ n (ω : ℕ → T), ω 0 = x →
    fA (Sum.elim v0 (fun _ => m)) n (phi (hitT {y | v0 y < m}) n ω) =
      act (hitT {y | v0 y < m}) n ω := by
  intro n ω hω
  have hv1 : Sum.elim v0 (fun _ => m) ((phi (hitT {y | v0 y < m}) n ω).2 1) = m := by
    show Sum.elim v0 (fun _ => m) (st _ n ω 1) = m
    rw [st_one]; rfl
  unfold fA
  rw [hv1]
  by_cases hlt : (n : ℕ∞) < hitT {y | v0 y < m} ω
  · have hv0 : Sum.elim v0 (fun _ => m) ((phi (hitT {y | v0 y < m}) n ω).2 0) = v0 (ω n) := by
      show Sum.elim v0 (fun _ => m) (st _ n ω 0) = _
      rw [st_eq _ n ω hlt.le]; rfl
    rw [hv0, act, if_pos hlt, if_pos]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [hω]; exact hx
    · have := hitT_lt _ ω n hlt hn
      simpa [Set.mem_setOf_eq, not_lt] using this
  · obtain ⟨s0, hs0⟩ := ENat.ne_top_iff_exists.1
      (ne_top_of_le_ne_top (ENat.coe_ne_top n) (not_lt.1 hlt))
    have hs0n : s0 ≤ n := by
      have := not_lt.1 hlt; rw [← hs0] at this; exact_mod_cast this
    have hv0 : Sum.elim v0 (fun _ => m) ((phi (hitT {y | v0 y < m}) n ω).2 0) = v0 (ω s0) := by
      show Sum.elim v0 (fun _ => m) (st _ n ω 0) = _
      rw [st_frozen _ ω s0 hs0.symm n hs0n, st_eq _ s0 ω (le_of_eq hs0)]; rfl
    have hlt0 : v0 (ω s0) < m := hitT_val _ ω s0 hs0.symm
    rw [hv0, act, if_neg hlt, if_neg (not_le.2 hlt0)]

lemma hfB (v0 : T → ℝ) (m : ℝ) (x : T) (hx : v0 x ≤ m) : ∀ n (ω : ℕ → T), ω 0 = x →
    fB (Sum.elim v0 (fun _ => m)) n (phi (fun _ => (0 : ℕ∞)) n ω) =
      act (fun _ => (0 : ℕ∞)) n ω := by
  intro n ω hω
  have hst : st (fun _ => (0 : ℕ∞)) n ω = twoStates x () := by
    rw [st_frozen _ ω 0 (by simp) n (Nat.zero_le n)]
    simp only [st, hω]
  have e : (phi (fun _ => (0 : ℕ∞)) n ω).2 = twoStates x () := hst
  unfold fB
  rw [e]
  have h1 : act (fun _ : ℕ → T => (0 : ℕ∞)) n ω = 1 := by simp [act]
  rw [h1, if_pos]
  exact hx

lemma extH_phi (τ : (ℕ → T) → ℕ∞) (x : T) (n : ℕ) (ω : ℕ → T) (hn : (n : ℕ∞) ≤ τ ω) :
    ∀ v ≤ n, extH x n (phi τ n ω) v = ω v := by
  intro v hv
  unfold extH
  split_ifs with hvn
  · show Sum.elim id (fun _ => x) (st τ v ω 0) = ω v
    rw [st_eq τ v ω (le_trans (by exact_mod_cast hv) hn)]; rfl
  · have : v = n := by omega
    subst this
    show Sum.elim id (fun _ => x) (st τ v ω 0) = ω v
    rw [st_eq τ v ω hn]; rfl

lemma fT_spec {τ : (ℕ → T) → ℕ∞} (hτ : IsTrajStoppingTime τ) (x : T) (n : ℕ) (ω : ℕ → T) :
    fT τ x n (phi τ n ω) = act τ n ω := by
  unfold fT
  by_cases hlt : (n : ℕ∞) < τ ω
  · rw [if_pos]
    · simp [act, hlt]
    refine ⟨fun u => ?_, ?_⟩
    · show act τ u ω = 0
      have : ((u : ℕ) : ℕ∞) < τ ω := lt_trans (by exact_mod_cast u.2) hlt
      simp [act, this]
    · rw [stop_dep hτ n (extH_phi τ x n ω hlt.le)]; exact not_le.2 hlt
  · rw [if_neg]
    · simp [act, hlt]
    rintro ⟨hall, hnot⟩
    apply hnot
    have hle : (n : ℕ∞) ≤ τ ω := by
      by_contra hc
      push_neg at hc
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hc)
      have hkn : k < n := by rw [← hk] at hc; exact_mod_cast hc
      have := hall ⟨k, hkn⟩
      change act τ k ω = 0 at this
      simp [act, ← hk] at this
    rw [stop_dep hτ n (extH_phi τ x n ω hle)]; exact not_lt.1 hlt

/-! ### The two halves of Theorem 4.8 -/

theorem caseA (μ : IndexFunction) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hμ : IsIndexForStandardPairs μ a)
    (P : Kernel T T) [IsMarkovKernel P] {r : T → ℝ} (hr : BoundedReward r) (x : T) {lam : ℝ}
    (hlam : gittinsIndex P r a x < lam) :
    μ T P r x < μ Unit standardKernel (fun _ => lam) () := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨M, hM⟩ := hr
  have hσ := hitT_stop (T := T) {y | μ T P r y < μ Unit standardKernel (fun _ => lam) ()}
  have hσ1 := hitT_one (T := T) {y | μ T P r y < μ Unit standardKernel (fun _ => lam) ()}
  have hf := hfA (μ T P r) (μ Unit standardKernel (fun _ => lam) ()) x hcon
  have hopt := hμ T P r ⟨M, hM⟩ lam (mkPol (fA (sumIndexValue μ P r lam))) (idxA _) x
  rw [value_eq P ha0 ha1 hM lam hσ x (fA (sumIndexValue μ P r lam)) hf] at hopt
  have hle := le_ciSup (bdd_vals P ha0 ha1 hM lam (twoStates x ()))
    (mkPol (fun n (_ : MarkovBanditHistory 2 (T ⊕ Unit) n) => (1 : Fin 2)))
  rw [value_eq P ha0 ha1 hM lam stop0 x _ (hf1 x), ← hopt, dss_zero, dss_zero] at hle
  have hD := D_ge_one P ha0 ha1 x hσ hσ1
  have hratio : (∫ ω, discountedStoppedSum a r
        (hitT {y | μ T P r y < μ Unit standardKernel (fun _ => lam) ()}) ω
        ∂markovChainMeasure P x) /
      (∫ ω, discountedStoppedSum a (fun _ => (1 : ℝ))
        (hitT {y | μ T P r y < μ Unit standardKernel (fun _ => lam) ()}) ω
        ∂markovChainMeasure P x) ≤ gittinsIndex P r a x :=
    le_csSup (gi_bdd P Measurable.of_discrete ha0 ha1 (hint_of_bdd P hM ha0 ha1) x)
      ⟨_, hσ, hσ1, rfl⟩
  rw [div_le_iff₀ (by linarith)] at hratio
  have := mul_lt_mul_of_pos_right hlam (by linarith : (0 : ℝ) < ∫ ω, discountedStoppedSum a
    (fun _ => (1 : ℝ)) (hitT {y | μ T P r y < μ Unit standardKernel (fun _ => lam) ()}) ω
    ∂markovChainMeasure P x)
  linarith

theorem caseB (μ : IndexFunction) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hμ : IsIndexForStandardPairs μ a)
    (P : Kernel T T) [IsMarkovKernel P] {r : T → ℝ} (hr : BoundedReward r) (x : T) {lam : ℝ}
    (hlam : lam < gittinsIndex P r a x) :
    μ Unit standardKernel (fun _ => lam) () < μ T P r x := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨M, hM⟩ := hr
  have hf := hfB (μ T P r) (μ Unit standardKernel (fun _ => lam) ()) x hcon
  have hopt := hμ T P r ⟨M, hM⟩ lam (mkPol (fB (sumIndexValue μ P r lam))) (idxB _) x
  rw [value_eq P ha0 ha1 hM lam stop0 x (fB (sumIndexValue μ P r lam)) hf, dss_zero,
    dss_zero] at hopt
  unfold gittinsIndex at hlam
  obtain ⟨g, ⟨τ, hτ, hτ1, rfl⟩, hg⟩ := exists_lt_of_lt_csSup
    (by exact ⟨_, fun _ => 1, stop1, fun _ => le_rfl, rfl⟩) hlam
  have hle := le_ciSup (bdd_vals P ha0 ha1 hM lam (twoStates x ())) (mkPol (fT τ x))
  rw [value_eq P ha0 ha1 hM lam hτ x _ (fun n ω _ => fT_spec hτ x n ω), ← hopt] at hle
  have hD := D_ge_one P ha0 ha1 x hτ hτ1
  rw [lt_div_iff₀ (by linarith)] at hg
  linarith

end Main

end P2M2a63

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
theorem solution (μ : IndexFunction) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hμ : IsIndexForStandardPairs μ a)
    {T : Type} [MeasurableSpace T] [Countable T] [MeasurableSingletonClass T]
    (P : Kernel T T) [IsMarkovKernel P] {r : T → ℝ} (hr : BoundedReward r) (x : T)
    {T' : Type} [MeasurableSpace T'] [Countable T'] [MeasurableSingletonClass T']
    (P' : Kernel T' T') [IsMarkovKernel P'] {r' : T' → ℝ} (hr' : BoundedReward r') (x' : T')
    (hlt : gittinsIndex P r a x < gittinsIndex P' r' a x') :
    μ T P r x < μ T' P' r' x' := by
  obtain ⟨lam, hl1, hl2⟩ := exists_between hlt
  exact (P2M2a63.caseA μ ha0 ha1 hμ P hr x hl1).trans (P2M2a63.caseB μ ha0 ha1 hμ P' hr' x' hl2)
