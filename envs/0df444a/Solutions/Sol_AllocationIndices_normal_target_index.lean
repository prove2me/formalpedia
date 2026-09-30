-- Prove2me | solution 1 for AllocationIndices.normal_target_index
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T07:54:44.782609+00:00
-- url     : https://prove2.me/submissions/9f802fe6-4738-41f8-914e-dc61e859594a

import Mathlib
import Definitions.Def_AllocationIndices_Sampling

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pff_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pff_marg0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : (markovChainMeasure P x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pff_int0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) (F : S → ℝ) (hF : Measurable F) :
    ∫ ω, F (ω 0) ∂markovChainMeasure P x = F x := by
  have hFm : Measurable (fun h : (Π _i : Finset.Iic 0, S) ↦ F (h ⟨0, Finset.mem_Iic.2 le_rfl⟩)) :=
    hF.comp (measurable_pi_apply _)
  have h1 := integral_map (μ := markovChainMeasure P x) (Preorder.measurable_frestrictLe 0).aemeasurable
    hFm.aestronglyMeasurable
  rw [pff_marg0, integral_dirac' _ _ hFm.stronglyMeasurable] at h1
  exact h1.symm

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pff_meas_lt {S : Type*} [MeasurableSpace S] (τ : (ℕ → S) → ℕ∞)
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
private lemma pff_int_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pff_term_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (f : S → ℝ) (Bf : ℝ)
    (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) (t : ℕ) :
    ‖(if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)‖ ≤ Bf * a ^ t := by
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hf _) (pow_nonneg ha0 t)
  · simp only [norm_zero]; positivity

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pff_summable {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_left Bf)
    (pff_term_bound a ha0 f Bf hBf hf τ ω)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pff_dss_bound {S : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (f : S → ℝ)
    (Bf : ℝ) (hBf : 0 ≤ Bf) (hf : ∀ y, |f y| ≤ Bf) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    |discountedStoppedSum a f τ ω| ≤ Bf / (1 - a) := by
  unfold discountedStoppedSum
  have hg : HasSum (fun t : ℕ ↦ Bf * a ^ t) (Bf * (1 - a)⁻¹) :=
    (hasSum_geometric_of_lt_one ha0 ha1).mul_left Bf
  have := tsum_of_norm_bounded hg (pff_term_bound a ha0 f Bf hBf hf τ ω)
  rw [Real.norm_eq_abs] at this
  rwa [div_eq_mul_inv]

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pff_dss_meas {S : Type*} [MeasurableSpace S] (a : ℝ) (f : S → ℝ)
    (hf : Measurable f) (τ : (ℕ → S) → ℕ∞) (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum a f τ) := by
  unfold discountedStoppedSum
  exact Measurable.tsum fun t ↦ Measurable.ite (pff_meas_lt τ hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t))) measurable_const

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma pff_inv {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (G : Set S) (hG : MeasurableSet G) (hPG : ∀ y ∈ G, P y Gᶜ = 0) (x : S) (hx : x ∈ G) :
    ∀ t : ℕ, (markovChainMeasure P x) {ω | ω t ∉ G} = 0 := by
  haveI := pff_prob P x
  intro t
  induction t with
  | zero =>
    have hm : MeasurableSet {h : (Π _i : Finset.Iic 0, S) |
        h ⟨0, Finset.mem_Iic.2 le_rfl⟩ ∈ Gᶜ} :=
      (measurable_pi_apply (X := fun _ : Finset.Iic 0 ↦ S) ⟨0, Finset.mem_Iic.2 le_rfl⟩) hG.compl
    have h1 := Measure.map_apply (μ := markovChainMeasure P x)
      (Preorder.measurable_frestrictLe 0) hm
    rw [pff_marg0, Measure.dirac_apply' _ hm] at h1
    have h2 : Set.indicator {h : (Π _i : Finset.Iic 0, S) |
        h ⟨0, Finset.mem_Iic.2 le_rfl⟩ ∈ Gᶜ} (1 : (Π _i : Finset.Iic 0, S) → ENNReal)
        (fun _ ↦ x) = 0 := by
      rw [Set.indicator_of_notMem]
      intro hh; exact hh hx
    rw [h2] at h1
    exact h1.symm
  | succ t ih =>
    have hmap : (markovChainMeasure P x).map (Preorder.frestrictLe t) ⊗ₘ markovChainStep P t =
        (markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe t ω, ω (t + 1))) :=
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (X := fun _ : ℕ ↦ S)
        (μ₀ := Measure.dirac x) (κ := markovChainStep P) (a := t)
    have hΦ : Measurable (fun ω : ℕ → S ↦ (Preorder.frestrictLe t ω, ω (t + 1))) :=
      (Preorder.measurable_frestrictLe t).prodMk (measurable_pi_apply (t + 1))
    have hs : MeasurableSet ((Set.univ : Set (Π _i : Finset.Iic t, S)) ×ˢ Gᶜ) :=
      MeasurableSet.univ.prod hG.compl
    have h1 : (markovChainMeasure P x) {ω | ω (t + 1) ∉ G} =
        ((markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe t ω, ω (t + 1))))
          ((Set.univ : Set (Π _i : Finset.Iic t, S)) ×ˢ Gᶜ) := by
      rw [Measure.map_apply hΦ hs]; congr 1; ext ω; simp
    rw [h1, ← hmap, Measure.compProd_apply hs]
    have hmeasf : Measurable (fun h : (Π _i : Finset.Iic t, S) ↦
        P (h ⟨t, Finset.mem_Iic.2 le_rfl⟩) Gᶜ) :=
      (Kernel.measurable_coe P hG.compl).comp (measurable_pi_apply _)
    have heq : ∀ h : (Π _i : Finset.Iic t, S),
        markovChainStep P t h (Prod.mk h ⁻¹' ((Set.univ : Set (Π _i : Finset.Iic t, S)) ×ˢ Gᶜ)) =
          P (h ⟨t, Finset.mem_Iic.2 le_rfl⟩) Gᶜ := by
      intro h
      rw [markovChainStep, Kernel.comap_apply]
      congr 1
      ext y; simp
    simp_rw [heq]
    rw [lintegral_map hmeasf (Preorder.measurable_frestrictLe t)]
    have hae : ∀ᵐ ω ∂markovChainMeasure P x, P (ω t) Gᶜ = 0 := by
      rw [ae_iff]
      refine measure_mono_null (fun ω hω ↦ ?_) ih
      intro hωG
      exact hω (hPG _ hωG)
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae] with ω hω
    exact hω

open AllocationIndices in
private def pffInv (xb n : ℝ) (q : ℝ × ℝ) : Prop :=
  0 < q.2 ∧ q.1 * Real.sqrt (1 + 1 / n) ≤ xb * Real.sqrt (1 + 1 / q.2)

private def pffG (xb n : ℝ) : Set ((ℝ × ℝ) ⊕ Unit) :=
  {s | Sum.elim (pffInv xb n) (fun _ ↦ True) s}

private lemma pffG_meas (xb n : ℝ) : MeasurableSet (pffG xb n) := by
  rw [measurableSet_sum_iff]
  constructor
  · show MeasurableSet {q : ℝ × ℝ | 0 < q.2 ∧
      q.1 * Real.sqrt (1 + 1 / n) ≤ xb * Real.sqrt (1 + 1 / q.2)}
    exact (measurableSet_lt (f := fun _ : ℝ × ℝ ↦ (0 : ℝ)) (g := fun q : ℝ × ℝ ↦ q.2)
      measurable_const measurable_snd).inter
      (measurableSet_le (f := fun q : ℝ × ℝ ↦ q.1 * Real.sqrt (1 + 1 / n))
        (g := fun q : ℝ × ℝ ↦ xb * Real.sqrt (1 + 1 / q.2)) (by fun_prop) (by fun_prop))
  · show MeasurableSet {_u : Unit | True}
    exact MeasurableSet.univ

private lemma pff_sqrt_step (k : ℝ) (hk : 0 < k) :
    k * Real.sqrt (1 + 1 / k) ≤ (k + 1) * Real.sqrt (1 + 1 / (k + 1)) := by
  have hu := Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 + 1 / k by positivity)
  have hv := Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 + 1 / (k + 1) by positivity)
  have hu0 := Real.sqrt_nonneg (1 + 1 / k)
  have hv0 := Real.sqrt_nonneg (1 + 1 / (k + 1))
  set u := Real.sqrt (1 + 1 / k)
  set v := Real.sqrt (1 + 1 / (k + 1))
  have hu2 : (k * u) * (k * u) = k * (k + 1) := by
    rw [mul_mul_mul_comm, hu]; field_simp
  have hv2 : ((k + 1) * v) * ((k + 1) * v) = (k + 1) * (k + 2) := by
    rw [mul_mul_mul_comm, hv]; field_simp; ring
  by_contra hlt
  push_neg at hlt
  have := mul_lt_mul'' hlt hlt (by positivity) (by positivity)
  nlinarith

open MeasureTheory ProbabilityTheory AllocationIndices in
private lemma pff_step_closed (xb n : ℝ) (hxb : 0 ≤ xb) (hn : 0 < n) (q : ℝ × ℝ)
    (hq : pffInv xb n q) : normalTargetChain (Sum.inl q) (pffG xb n)ᶜ = 0 := by
  have hG := pffG_meas xb n
  show normalTargetStep q (pffG xb n)ᶜ = 0
  rw [normalTargetStep, Kernel.map_apply' _ measurable_normalTargetFun _ hG.compl,
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left (measurable_normalTargetFun hG.compl)]
  convert measure_empty (μ := gaussianReal 0 1)
  ext z
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
  split_ifs with h
  · exact trivial
  · show pffInv xb n (meanUpdate q (q.1 + Real.sqrt (1 + 1 / q.2) * z))
    obtain ⟨hk, hm⟩ := hq
    obtain ⟨m, k⟩ := q
    simp only at hk hm h ⊢
    push_neg at h
    set u := Real.sqrt (1 + 1 / k)
    set x := m + u * z
    have hs0 : 0 < Real.sqrt (1 + 1 / n) := Real.sqrt_pos.2 (by positivity)
    set s0 := Real.sqrt (1 + 1 / n)
    have hstep := pff_sqrt_step k hk
    set v := Real.sqrt (1 + 1 / (k + 1))
    refine ⟨by simp [meanUpdate]; linarith, ?_⟩
    simp only [meanUpdate]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have h1 : k * (m * s0) ≤ k * (xb * u) := mul_le_mul_of_nonneg_left hm hk.le
    have h2 : x * s0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h.le hs0.le
    have h3 : xb * (k * u) ≤ xb * ((k + 1) * v) := mul_le_mul_of_nonneg_left hstep hxb
    nlinarith

open MeasureTheory ProbabilityTheory AllocationIndices in
private lemma pff_closed (xb n : ℝ) (hxb : 0 ≤ xb) (hn : 0 < n) :
    ∀ y ∈ pffG xb n, normalTargetChain y (pffG xb n)ᶜ = 0 := by
  rintro (q | u) hy
  · exact pff_step_closed xb n hxb hn q hy
  · show Measure.dirac (Sum.inr ()) (pffG xb n)ᶜ = 0
    rw [Measure.dirac_apply' _ (pffG_meas xb n).compl, Set.indicator_of_notMem]
    intro hh; exact hh trivial

open MeasureTheory ProbabilityTheory AllocationIndices in
private lemma pff_rew_le (xb n : ℝ) (hn : 0 < n) :
    ∀ y ∈ pffG xb n, normalTargetReward y ≤
      ((gaussianReal 0 1) {z | 0 ≤ xb + Real.sqrt (1 + 1 / n) * z}).toReal := by
  rintro (q | u) hy
  · obtain ⟨hk, hm⟩ := hy
    show ((gaussianReal 0 1) {z | 0 ≤ q.1 + Real.sqrt (1 + 1 / q.2) * z}).toReal ≤ _
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    have hs0 : 0 < Real.sqrt (1 + 1 / n) := Real.sqrt_pos.2 (by positivity)
    have hu : 0 < Real.sqrt (1 + 1 / q.2) := Real.sqrt_pos.2 (by positivity)
    have h1 := mul_nonneg hs0.le hz
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_pos_of_neg hu hneg
    nlinarith
  · exact ENNReal.toReal_nonneg

open MeasureTheory ProbabilityTheory AllocationIndices in
private lemma pff_rew_meas : Measurable normalTargetReward := by
  have hs : MeasurableSet {w : (ℝ × ℝ) × ℝ | 0 ≤ w.1.1 + Real.sqrt (1 + 1 / w.1.2) * w.2} :=
    measurableSet_le measurable_const (by fun_prop)
  have h : Measurable (fun p : ℝ × ℝ ↦
      ((gaussianReal 0 1) {z | 0 ≤ p.1 + Real.sqrt (1 + 1 / p.2) * z}).toReal) :=
    (measurable_measure_prodMk_left (ν := gaussianReal 0 1) hs).ennreal_toReal
  exact h.sumElim measurable_const

open MeasureTheory ProbabilityTheory AllocationIndices in
private lemma pff_rew_bound : ∀ y, |normalTargetReward y| ≤ 1 := by
  rintro (q | u)
  · show |((gaussianReal 0 1) {z | 0 ≤ q.1 + Real.sqrt (1 + 1 / q.2) * z}).toReal| ≤ 1
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  · show |(0 : ℝ)| ≤ 1
    simp

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
theorem solution {xb n : ℝ} (hxb : 0 ≤ xb) (hn : 0 < n) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1) :
    gittinsIndex normalTargetChain normalTargetReward a (Sum.inl (xb, n)) =
      ((gaussianReal 0 1) {z | 0 ≤ xb + Real.sqrt (1 + 1 / n) * z}).toReal := by
  haveI := pff_prob normalTargetChain (Sum.inl (xb, n))
  have hr0 : 0 ≤ ((gaussianReal 0 1) {z | 0 ≤ xb + Real.sqrt (1 + 1 / n) * z}).toReal :=
    ENNReal.toReal_nonneg
  have hx : (Sum.inl (xb, n) : (ℝ × ℝ) ⊕ Unit) ∈ pffG xb n := ⟨hn, le_rfl⟩
  have hinv := pff_inv normalTargetChain (pffG xb n) (pffG_meas xb n) (pff_closed xb n hxb hn)
    _ hx
  have hall : ∀ᵐ ω ∂markovChainMeasure normalTargetChain (Sum.inl (xb, n)),
      ∀ t, ω t ∈ pffG xb n := by
    rw [ae_all_iff]
    intro t
    rw [ae_iff]
    exact hinv t
  unfold gittinsIndex
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun _ ↦ 1, fun k ↦ MeasurableSet.const _, fun _ ↦ le_rfl, ?_⟩
    have hd : ∀ (f : (ℝ × ℝ) ⊕ Unit → ℝ) (ω : ℕ → (ℝ × ℝ) ⊕ Unit),
        discountedStoppedSum a f (fun _ ↦ 1) ω = f (ω 0) := by
      intro f ω
      unfold discountedStoppedSum
      rw [tsum_eq_single 0]
      · simp
      · intro t ht
        have : ¬ ((t : ℕ∞) < 1) := by
          intro h
          have : t < 1 := by exact_mod_cast h
          omega
        simp [this]
    simp only [hd]
    rw [pff_int0 _ _ _ pff_rew_meas, integral_const]
    simp only [probReal_univ, smul_eq_mul, mul_one, div_one]
    rfl
  · rintro g ⟨τ, hτ, hτ1, rfl⟩
    have hW0 : 0 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω
        ∂markovChainMeasure normalTargetChain (Sum.inl (xb, n)) := by
      refine integral_nonneg (fun ω ↦ ?_)
      unfold discountedStoppedSum
      refine tsum_nonneg (fun t ↦ ?_)
      split_ifs
      · positivity
      · exact le_rfl
    have hWint : Integrable (discountedStoppedSum a (fun _ ↦ (1 : ℝ)) τ)
        (markovChainMeasure normalTargetChain (Sum.inl (xb, n))) :=
      pff_int_of_bound _ _ (pff_dss_meas a _ measurable_const τ hτ) (1 / (1 - a))
        (pff_dss_bound a ha0.le ha1 _ 1 zero_le_one (fun _ ↦ by simp) τ)
    by_cases hR : Integrable (discountedStoppedSum a normalTargetReward τ)
        (markovChainMeasure normalTargetChain (Sum.inl (xb, n)))
    · have hle := integral_mono_ae hR (hWint.const_mul
        ((gaussianReal 0 1) {z | 0 ≤ xb + Real.sqrt (1 + 1 / n) * z}).toReal) (by
          filter_upwards [hall] with ω hω
          unfold discountedStoppedSum
          rw [← tsum_mul_left]
          refine Summable.tsum_le_tsum (fun t ↦ ?_)
            (pff_summable a ha0.le ha1 _ 1 zero_le_one pff_rew_bound τ ω)
            ((pff_summable a ha0.le ha1 (fun _ ↦ (1 : ℝ)) 1 zero_le_one
              (fun _ ↦ by simp) τ ω).mul_left _)
          split_ifs
          · have := pff_rew_le xb n hn (ω t) (hω t)
            have hat : 0 ≤ a ^ t := pow_nonneg ha0.le t
            nlinarith
          · simp)
      rw [integral_const_mul] at hle
      rcases hW0.eq_or_lt with h | h
      · rw [← h, div_zero]; exact hr0
      · rw [div_le_iff₀ h]; linarith
    · rw [integral_undef hR, zero_div]; exact hr0
