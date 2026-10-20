-- Prove2me | solution 1 for ArapostathisAC.VanishingDiscount.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T17:53:12.274632+00:00
-- url     : https://prove2.me/submissions/f304f7eb-c479-4aba-b33e-81f151b6635f

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_DPMaps

set_option autoImplicit false
open Filter Topology MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace ArapostathisAC.VanishingDiscount
variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

lemma prob_nonneg' (M : CMP A) (i : ℕ) (a : A) (j : ℕ) : 0 ≤ prob M i a j :=
  ENNReal.toReal_nonneg

lemma prob_hasSum (M : CMP A) (i : ℕ) (a : A) : HasSum (fun j => prob M i a j) 1 := by
  have h := (M.P (i, a)).tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
  simp only [Set.indicator_univ, measure_univ] at h
  have hne : ∀ j, M.P (i, a) {j} ≠ ⊤ := fun j => measure_ne_top _ _
  have hs : Summable (fun j => prob M i a j) :=
    ENNReal.summable_toReal (by rw [h]; exact ENNReal.one_ne_top)
  refine hs.hasSum_iff.mpr ?_
  unfold prob
  rw [← ENNReal.tsum_toReal_eq hne, h, ENNReal.toReal_one]

lemma prob_tsum (M : CMP A) (i : ℕ) (a : A) : ∑' j, prob M i a j = 1 :=
  (prob_hasSum M i a).tsum_eq

/-! ### The path measure: one-step structure -/

instance initMeasure_isProb (M : CMP A) (π : Policy M) (i : ℕ) :
    IsProbabilityMeasure (initMeasure π i) := by
  unfold initMeasure
  exact Measure.isProbabilityMeasure_map (measurable_const.prodMk measurable_id).aemeasurable

lemma pm_map_zero (M : CMP A) (π : Policy M) (i : ℕ) :
    (pathMeasure M π i).map (fun ω => ω 0) = initMeasure π i := by
  have hf : (fun ω : ℕ → ℕ × A => ω 0) =
      (fun y : (Π _ : Finset.Iic 0, ℕ × A) => y ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
        frestrictLe 0 := rfl
  unfold pathMeasure Kernel.trajMeasure
  rw [hf, ← Measure.map_map (g := fun y : (Π _ : Finset.Iic 0, ℕ × A) =>
      y ⟨0, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _) (measurable_frestrictLe 0),
    Measure.map_comp _ _ (measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_map (measurable_pi_apply _)
    (MeasurableEquiv.measurable _)]
  exact Measure.map_id

instance pathMeasure_isProb (M : CMP A) (π : Policy M) (i : ℕ) :
    IsProbabilityMeasure (pathMeasure M π i) := by
  unfold pathMeasure; infer_instance

lemma stepKernel_eq (M : CMP A) (π : Policy M) (t : ℕ) :
    stepKernel M π t = (M.P.comap (lastPair t) (measurable_pi_apply _)) ⊗ₖ
      ((π.rule (t + 1)).comap (fun p => (histFin t p.1, p.2))
        (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) := rfl

instance comapP_markov (M : CMP A) (t : ℕ) :
    IsMarkovKernel (M.P.comap (lastPair (A := A) t) (measurable_pi_apply _)) :=
  Kernel.IsMarkovKernel.comap _ _

instance comapRule_markov (M : CMP A) (π : Policy M) (t : ℕ) :
    IsMarkovKernel ((π.rule (t + 1)).comap (fun p : (Π _ : Finset.Iic t, ℕ × A) × ℕ =>
      (histFin t p.1, p.2)) (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) :=
  Kernel.IsMarkovKernel.comap _ _

lemma lintegral_step (M : CMP A) (π : Policy M) (i t : ℕ)
    (F : (Π _ : Finset.Iic t, ℕ × A) × (ℕ × A) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F (frestrictLe t ω, ω (t + 1)) ∂(pathMeasure M π i) =
      ∫⁻ h, ∫⁻ y, F (h, y) ∂(stepKernel M π t h) ∂((pathMeasure M π i).map (frestrictLe t)) := by
  have key := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => ℕ × A) (μ₀ := initMeasure π i) (κ := stepKernel M π) (a := t)
  unfold pathMeasure
  rw [← Measure.lintegral_compProd hF, key, lintegral_map hF (by fun_prop)]

lemma lintegral_next (M : CMP A) (π : Policy M) (i t : ℕ) (v : ℕ → ℝ≥0∞) :
    ∫⁻ ω, v (ω (t + 1)).1 ∂(pathMeasure M π i) =
      ∫⁻ ω, ∑' j, M.P (ω t) {j} * v j ∂(pathMeasure M π i) := by
  have hv : Measurable v := measurable_of_countable v
  have h1 := lintegral_step M π i t (fun p => v p.2.1) (hv.comp (measurable_fst.comp measurable_snd))
  simp only at h1
  rw [h1]
  have hinner : ∀ h, ∫⁻ y, v y.1 ∂(stepKernel M π t h) = ∑' j, M.P (lastPair t h) {j} * v j := by
    intro h
    rw [stepKernel_eq, Kernel.lintegral_compProd (f := fun y : ℕ × A => v y.1) _ _ _
      (hv.comp measurable_fst)]
    simp only [lintegral_const, measure_univ, mul_one, Kernel.comap_apply]
    rw [lintegral_countable']
    congr 1; funext j; rw [mul_comm]; rfl
  simp_rw [hinner]
  rw [lintegral_map _ (measurable_frestrictLe t)]
  · rfl
  · exact Measurable.ennreal_tsum (fun j =>
      ((M.P.measurable_coe (measurableSet_singleton j)).comp (measurable_pi_apply _)).mul_const _)

lemma ae_mem (M : CMP A) (π : Policy M) (i : ℕ) (V : ℕ → Set A) (hVm : ∀ x, MeasurableSet (V x))
    (hV : ∀ t hist, π.rule t hist (V hist.2)ᶜ = 0) (t : ℕ) :
    ∀ᵐ ω ∂(pathMeasure M π i), (ω t).2 ∈ V (ω t).1 := by
  have hB : MeasurableSet {p : ℕ × A | p.2 ∈ V p.1} := by
    have : {p : ℕ × A | p.2 ∈ V p.1} = ⋃ x : ℕ, ({x} : Set ℕ) ×ˢ V x := by
      ext ⟨x, a⟩; simp
    rw [this]; exact MeasurableSet.iUnion (fun x => (measurableSet_singleton x).prod (hVm x))
  cases t with
  | zero =>
    have h0 : ∀ᵐ p ∂(initMeasure π i), p.2 ∈ V p.1 := by
      unfold initMeasure
      rw [ae_map_iff (show Measurable (fun a : A => (i, a)) from
        measurable_const.prodMk measurable_id).aemeasurable hB]
      rw [ae_iff]
      exact hV 0 (fun j => j.elim0, i)
    rw [← pm_map_zero M π i] at h0
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable h0
  | succ t =>
    have hBc : MeasurableSet {p : ℕ × A | p.2 ∈ V p.1}ᶜ := hB.compl
    have hk : ∀ h, stepKernel M π t h {p : ℕ × A | p.2 ∈ V p.1}ᶜ = 0 := by
      intro h
      rw [stepKernel_eq, Kernel.compProd_apply hBc]
      have : ∀ x : ℕ, (π.rule (t + 1)) (histFin t h, x)
          (Prod.mk x ⁻¹' {p : ℕ × A | p.2 ∈ V p.1}ᶜ) = 0 :=
        fun x => hV (t + 1) (histFin t h, x)
      simp only [Kernel.comap_apply, this, lintegral_zero]
    have e : (pathMeasure M π i) {ω | ¬ (ω (t + 1)).2 ∈ V (ω (t + 1)).1} =
        ∫⁻ ω, ({p : ℕ × A | p.2 ∈ V p.1}ᶜ).indicator 1 (ω (t + 1)) ∂(pathMeasure M π i) := by
      rw [← lintegral_map (measurable_one.indicator hBc) (measurable_pi_apply (t + 1)),
        lintegral_indicator_one hBc, Measure.map_apply (measurable_pi_apply (t + 1)) hBc]
      rfl
    rw [ae_iff, e]
    have h1 := lintegral_step M π i t (fun p => ({p : ℕ × A | p.2 ∈ V p.1}ᶜ).indicator 1 p.2)
      ((measurable_one.indicator hBc).comp measurable_snd)
    simp only at h1
    rw [h1]
    simp only [lintegral_indicator_one hBc, hk, lintegral_zero]

/-! ### Telescoping -/

lemma step_identity (M : CMP A) (π : Policy M) (i : ℕ) (β : ℝ) (hβ : 0 ≤ β) (v : ℕ → ℝ≥0∞)
    (t : ℕ) :
    ∫⁻ ω, (∑ s ∈ Finset.range (t + 1), ENNReal.ofReal (β ^ s * M.c (ω s).1 (ω s).2) +
        ENNReal.ofReal (β ^ (t + 1)) * v (ω (t + 1)).1) ∂(pathMeasure M π i) =
    ∫⁻ ω, (∑ s ∈ Finset.range t, ENNReal.ofReal (β ^ s * M.c (ω s).1 (ω s).2) +
        ENNReal.ofReal (β ^ t) * (ENNReal.ofReal (M.c (ω t).1 (ω t).2) +
          ENNReal.ofReal β * ∑' j, M.P (ω t) {j} * v j)) ∂(pathMeasure M π i) := by
  have hc : ∀ s, Measurable (fun ω : ℕ → ℕ × A =>
      ENNReal.ofReal (β ^ s * M.c (ω s).1 (ω s).2)) :=
    fun s => ENNReal.measurable_ofReal.comp
      (measurable_const.mul (M.c_meas.comp (measurable_pi_apply s)))
  have hS : ∀ n, Measurable (fun ω : ℕ → ℕ × A =>
      ∑ s ∈ Finset.range n, ENNReal.ofReal (β ^ s * M.c (ω s).1 (ω s).2)) :=
    fun n => Finset.measurable_sum _ (fun s _ => hc s)
  have hsum : Measurable (fun ω : ℕ → ℕ × A => ∑' j, M.P (ω t) {j} * v j) :=
    Measurable.ennreal_tsum (fun j =>
      ((M.P.measurable_coe (measurableSet_singleton j)).comp (measurable_pi_apply t)).mul_const _)
  have hpt : ∀ ω : ℕ → ℕ × A, ENNReal.ofReal (β ^ t) * (ENNReal.ofReal (M.c (ω t).1 (ω t).2) +
        ENNReal.ofReal β * ∑' j, M.P (ω t) {j} * v j) =
      ENNReal.ofReal (β ^ t * M.c (ω t).1 (ω t).2) +
        ENNReal.ofReal (β ^ (t + 1)) * ∑' j, M.P (ω t) {j} * v j := by
    intro ω
    rw [mul_add, ← ENNReal.ofReal_mul (pow_nonneg hβ t), ← mul_assoc,
      ← ENNReal.ofReal_mul (pow_nonneg hβ t), pow_succ]
  simp_rw [hpt, Finset.sum_range_succ, add_assoc]
  rw [lintegral_add_left (hS t), lintegral_add_left (hS t), lintegral_add_left (hc t),
    lintegral_add_left (hc t),
    lintegral_const_mul _ (show Measurable (fun ω : ℕ → ℕ × A => v (ω (t + 1)).1) from
      (measurable_of_countable v).comp (measurable_fst.comp (measurable_pi_apply (t + 1)))),
    lintegral_const_mul _ hsum, lintegral_next]

lemma lintegral_at_zero (M : CMP A) (π : Policy M) (i : ℕ) (g : ℕ → ℝ≥0∞) :
    ∫⁻ ω, g (ω 0).1 ∂(pathMeasure M π i) = g i := by
  have hg : Measurable (fun p : ℕ × A => g p.1) := (measurable_of_countable g).comp measurable_fst
  have e1 : ∫⁻ ω, g (ω 0).1 ∂(pathMeasure M π i) =
      ∫⁻ p, g p.1 ∂((pathMeasure M π i).map (fun ω => ω 0)) :=
    (lintegral_map hg (measurable_pi_apply 0)).symm
  rw [e1, pm_map_zero]
  unfold initMeasure
  rw [lintegral_map hg (show Measurable (fun a : A => (i, a)) from
    measurable_const.prodMk measurable_id)]
  simp

lemma value_iter_le_discCost (M : CMP A) (β : ℝ) (hβ : 0 ≤ β) (π : Policy M) (i N : ℕ) :
    (discBellman M β)^[N] 0 i ≤ discCost M π β i := by
  have hU : ∀ t, ∀ᵐ ω ∂(pathMeasure M π i), (ω t).2 ∈ M.U (ω t).1 :=
    ae_mem M π i M.U (fun x => (M.U_compact x).isClosed.measurableSet) π.adm
  have hstep : ∀ t m,
      ∫⁻ ω, (∑ s ∈ Finset.range t, ENNReal.ofReal (β ^ s * M.c (ω s).1 (ω s).2) +
        ENNReal.ofReal (β ^ t) * (discBellman M β)^[m + 1] 0 (ω t).1) ∂(pathMeasure M π i) ≤
      ∫⁻ ω, (∑ s ∈ Finset.range (t + 1), ENNReal.ofReal (β ^ s * M.c (ω s).1 (ω s).2) +
        ENNReal.ofReal (β ^ (t + 1)) * (discBellman M β)^[m] 0 (ω (t + 1)).1)
          ∂(pathMeasure M π i) := by
    intro t m
    rw [step_identity M π i β hβ _ t]
    refine lintegral_mono_ae ((hU t).mono fun ω hω => ?_)
    refine add_le_add le_rfl (mul_le_mul' le_rfl ?_)
    rw [Function.iterate_succ_apply']
    exact iInf₂_le _ hω
  have hind : ∀ k t,
      ∫⁻ ω, (∑ s ∈ Finset.range t, ENNReal.ofReal (β ^ s * M.c (ω s).1 (ω s).2) +
        ENNReal.ofReal (β ^ t) * (discBellman M β)^[k] 0 (ω t).1) ∂(pathMeasure M π i) ≤
      ∫⁻ ω, (∑ s ∈ Finset.range (t + k), ENNReal.ofReal (β ^ s * M.c (ω s).1 (ω s).2) +
        ENNReal.ofReal (β ^ (t + k)) * (discBellman M β)^[0] 0 (ω (t + k)).1)
          ∂(pathMeasure M π i) := by
    intro k
    induction k with
    | zero => intro t; exact le_rfl
    | succ k ih =>
      intro t
      refine (hstep t k).trans ?_
      have := ih (t + 1)
      rw [show t + 1 + k = t + (k + 1) by omega] at this
      exact this
  have h0 := hind N 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, ENNReal.ofReal_one,
    one_mul, Function.iterate_zero, id, Pi.zero_apply, mul_zero, add_zero] at h0
  rw [lintegral_at_zero M π i ((discBellman M β)^[N] 0)] at h0
  refine h0.trans ?_
  unfold discCost
  exact lintegral_mono fun ω => ENNReal.sum_le_tsum _

lemma discCost_le_of_fixed (M : CMP A) (β : ℝ) (hβ : 0 ≤ β) (f : StationaryPolicy M)
    (v : ℕ → ℝ≥0∞)
    (hv : ∀ x, v x = ENNReal.ofReal (M.c x (f.1 x)) +
      ENNReal.ofReal β * ∑' j, M.P (x, f.1 x) {j} * v j) (i : ℕ) :
    discCost M f.toPolicy β i ≤ v i := by
  have hf : ∀ t, ∀ᵐ ω ∂(pathMeasure M f.toPolicy i), (ω t).2 ∈ ({f.1 (ω t).1} : Set A) := by
    refine ae_mem M f.toPolicy i (fun x => {f.1 x}) (fun x => measurableSet_singleton _) ?_
    intro t hist
    simp only [StationaryPolicy.toPolicy]
    rw [Kernel.deterministic_apply' _ _ (measurableSet_singleton _).compl]
    simp
  have hc : ∀ s, Measurable (fun ω : ℕ → ℕ × A =>
      ENNReal.ofReal (β ^ s * M.c (ω s).1 (ω s).2)) :=
    fun s => ENNReal.measurable_ofReal.comp
      (measurable_const.mul (M.c_meas.comp (measurable_pi_apply s)))
  have hstep : ∀ t,
      ∫⁻ ω, (∑ s ∈ Finset.range (t + 1), ENNReal.ofReal (β ^ s * M.c (ω s).1 (ω s).2) +
        ENNReal.ofReal (β ^ (t + 1)) * v (ω (t + 1)).1) ∂(pathMeasure M f.toPolicy i) =
      ∫⁻ ω, (∑ s ∈ Finset.range t, ENNReal.ofReal (β ^ s * M.c (ω s).1 (ω s).2) +
        ENNReal.ofReal (β ^ t) * v (ω t).1) ∂(pathMeasure M f.toPolicy i) := by
    intro t
    rw [step_identity M f.toPolicy i β hβ v t]
    refine lintegral_congr_ae ((hf t).mono fun ω hω => ?_)
    beta_reduce
    generalize ω t = p at hω ⊢
    obtain ⟨x, a⟩ := p
    simp only [Set.mem_singleton_iff] at hω
    subst hω
    rw [← hv x]
  have hΨ : ∀ t,
      ∫⁻ ω, (∑ s ∈ Finset.range t, ENNReal.ofReal (β ^ s * M.c (ω s).1 (ω s).2) +
        ENNReal.ofReal (β ^ t) * v (ω t).1) ∂(pathMeasure M f.toPolicy i) = v i := by
    intro t
    induction t with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, ENNReal.ofReal_one,
        one_mul]
      exact lintegral_at_zero M f.toPolicy i v
    | succ t ih => rw [hstep, ih]
  have hS : ∀ N, ∫⁻ ω, ∑ s ∈ Finset.range N, ENNReal.ofReal (β ^ s * M.c (ω s).1 (ω s).2)
      ∂(pathMeasure M f.toPolicy i) ≤ v i :=
    fun N => (lintegral_mono fun ω => le_self_add).trans (hΨ N).le
  unfold discCost
  rw [lintegral_tsum (fun s => (hc s).aemeasurable), ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  rw [← lintegral_finset_sum _ (fun s _ => hc s)]
  exact hS N

/-! ### Value iteration -/

lemma lsc_mul_const_of_continuousOn {s : Set A} {g : A → ℝ≥0∞} (hg : ContinuousOn g s)
    (C : ℝ≥0∞) : LowerSemicontinuousOn (fun a => g a * C) s := by
  intro a ha y hy
  have hy' : y < g a * C := hy
  have hne : g a ≠ 0 := by
    intro h
    rw [h, zero_mul] at hy'
    exact absurd hy' (by simp)
  have ht : Tendsto (fun a => g a * C) (𝓝[s] a) (𝓝 (g a * C)) :=
    ENNReal.Tendsto.mul_const (hg a ha) (Or.inl hne)
  exact ht.eventually (eventually_gt_nhds hy)

lemma lsc_F (M : CMP A) (β : ℝ) (v : ℕ → ℝ≥0∞) (x : ℕ) :
    LowerSemicontinuousOn (fun a => ENNReal.ofReal (M.c x a) +
      ENNReal.ofReal β * ∑' j, M.P (x, a) {j} * v j) (M.U x) := by
  have h1 : LowerSemicontinuousOn (fun a => ENNReal.ofReal (M.c x a)) (M.U x) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (M.c_cont x)).lowerSemicontinuousOn
  have hP : ∀ j, ContinuousOn (fun a => M.P (x, a) {j}) (M.U x) := by
    intro j
    have : (fun a => M.P (x, a) {j}) = fun a => ENNReal.ofReal ((M.P (x, a) {j}).toReal) := by
      funext a; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [this]; exact ENNReal.continuous_ofReal.comp_continuousOn (M.P_cont x j)
  have h2 : LowerSemicontinuousOn (fun a => ∑' j, M.P (x, a) {j} * v j) (M.U x) :=
    lowerSemicontinuousOn_tsum (fun j => lsc_mul_const_of_continuousOn (hP j) (v j))
  have h3 : LowerSemicontinuousOn (fun a => ENNReal.ofReal β * ∑' j, M.P (x, a) {j} * v j)
      (M.U x) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_lowerSemicontinuousOn h2
      (fun p q h => mul_le_mul' le_rfl h)
  exact h1.add h3

lemma exists_min_F (M : CMP A) (β : ℝ) (v : ℕ → ℝ≥0∞) (x : ℕ) :
    ∃ a ∈ M.U x, discBellman M β v x =
      ENNReal.ofReal (M.c x a) + ENNReal.ofReal β * ∑' j, M.P (x, a) {j} * v j := by
  obtain ⟨a, ha, hmin⟩ := (lsc_F M β v x).exists_isMinOn (M.U_nonempty x) (M.U_compact x)
  refine ⟨a, ha, le_antisymm (iInf₂_le a ha) (le_iInf₂ fun b hb => ?_)⟩
  exact isMinOn_iff.mp hmin b hb

lemma discBellman_mono (M : CMP A) (β : ℝ) {v w : ℕ → ℝ≥0∞} (h : v ≤ w) :
    discBellman M β v ≤ discBellman M β w := fun x =>
  iInf₂_mono fun a _ => add_le_add le_rfl (mul_le_mul' le_rfl
    (ENNReal.tsum_le_tsum fun j => mul_le_mul' le_rfl (h j)))

lemma tsum_iSup_mono (g : ℕ → ℕ → ℝ≥0∞) (hg : Monotone g) :
    ∑' j, ⨆ m, g m j = ⨆ m, ∑' j, g m j := by
  simp_rw [← lintegral_count]
  exact lintegral_iSup (fun m => measurable_of_countable _) hg

lemma fixed_of_iter (M : CMP A) (β : ℝ) (w : ℕ → ℕ → ℝ≥0∞) (h0 : w 0 = 0)
    (hs : ∀ m, w (m + 1) = discBellman M β (w m)) (x : ℕ) :
    discBellman M β (fun y => ⨆ m, w m y) x = ⨆ m, w m x := by
  have hmono : Monotone w := by
    refine monotone_nat_of_le_succ fun m => ?_
    induction m with
    | zero => rw [h0]; exact fun y => by simp
    | succ m ih =>
      calc w (m + 1) = discBellman M β (w m) := hs m
        _ ≤ discBellman M β (w (m + 1)) := discBellman_mono M β ih
        _ = w (m + 1 + 1) := (hs (m + 1)).symm
  have hwW : ∀ m, w m ≤ fun y => ⨆ m, w m y := fun m y => le_iSup (fun m => w m y) m
  apply le_antisymm
  · choose a ha haeq using fun m => exists_min_F M β (w m) x
    obtain ⟨a', ha', ψ, hψ, hlim⟩ := (M.U_compact x).tendsto_subseq ha
    have hlim' : Tendsto (fun k => a (ψ k)) atTop (𝓝[M.U x] a') :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun k => ha _⟩
    have hM : ∀ m, ENNReal.ofReal (M.c x a') +
        ENNReal.ofReal β * ∑' j, M.P (x, a') {j} * w m j ≤ ⨆ m, w m x := by
      intro m
      refine le_of_forall_lt fun y hy => ?_
      have hev := hlim'.eventually (lsc_F M β (w m) x a' ha' y hy)
      have hev2 := hev.and (hψ.tendsto_atTop.eventually_ge_atTop m)
      obtain ⟨k, hk1, hk2⟩ := hev2.exists
      calc y < _ := hk1
        _ ≤ ENNReal.ofReal (M.c x (a (ψ k))) +
            ENNReal.ofReal β * ∑' j, M.P (x, a (ψ k)) {j} * w (ψ k) j :=
          add_le_add le_rfl (mul_le_mul' le_rfl
            (ENNReal.tsum_le_tsum fun j => mul_le_mul' le_rfl (hmono hk2 j)))
        _ = w (ψ k + 1) x := by rw [hs (ψ k), haeq (ψ k)]
        _ ≤ ⨆ m, w m x := le_iSup (fun m => w m x) _
    calc discBellman M β (fun y => ⨆ m, w m y) x
        ≤ ENNReal.ofReal (M.c x a') +
          ENNReal.ofReal β * ∑' j, M.P (x, a') {j} * ⨆ m, w m j := iInf₂_le a' ha'
      _ = ⨆ m, (ENNReal.ofReal (M.c x a') +
          ENNReal.ofReal β * ∑' j, M.P (x, a') {j} * w m j) := by
          simp_rw [ENNReal.mul_iSup]
          rw [tsum_iSup_mono (fun m j => M.P (x, a') {j} * w m j)
            (fun m n h j => mul_le_mul' le_rfl (hmono h j)), ENNReal.mul_iSup, ENNReal.add_iSup]
      _ ≤ ⨆ m, w m x := iSup_le hM
  · refine iSup_le fun m => ?_
    cases m with
    | zero => rw [h0]; simp
    | succ m => rw [hs m]; exact discBellman_mono M β (hwW m) x

theorem disc_opt (M : CMP A) (β : ℝ) (hβ : 0 ≤ β) :
    (∀ i, discValue M β i = discBellman M β (discValue M β) i) ∧
    ∃ f : StationaryPolicy M, ∀ i, discValue M β i = ENNReal.ofReal (M.c i (f.1 i)) +
      ENNReal.ofReal β * ∑' j, M.P (i, f.1 i) {j} * discValue M β j := by
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℕ → ℝ≥0∞, w = fun m => (discBellman M β)^[m] 0 := ⟨_, rfl⟩
  have h0 : w 0 = 0 := by rw [hw]; rfl
  have hs : ∀ m, w (m + 1) = discBellman M β (w m) := by
    intro m; rw [hw]; exact Function.iterate_succ_apply' _ _ _
  have hfix : ∀ x, discBellman M β (fun y => ⨆ m, w m y) x = ⨆ m, w m x :=
    fixed_of_iter M β w h0 hs
  choose fa hfa hfeq using fun x => exists_min_F M β (fun y => ⨆ m, w m y) x
  let f : StationaryPolicy M := ⟨fa, hfa⟩
  have hfv : ∀ x, (⨆ m, w m x) = ENNReal.ofReal (M.c x (f.1 x)) +
      ENNReal.ofReal β * ∑' j, M.P (x, f.1 x) {j} * ⨆ m, w m j :=
    fun x => (hfix x).symm.trans (hfeq x)
  have hle : ∀ i, (⨆ m, w m i) ≤ discValue M β i := fun i =>
    iSup_le fun m => le_iInf fun π => by
      rw [hw]; exact value_iter_le_discCost M β hβ π i m
  have hge : ∀ i, discValue M β i ≤ ⨆ m, w m i := fun i =>
    (iInf_le _ f.toPolicy).trans
      (discCost_le_of_fixed M β hβ f (fun y => ⨆ m, w m y) hfv i)
  have hEq : discValue M β = fun y => ⨆ m, w m y :=
    funext fun i => le_antisymm (hge i) (hle i)
  refine ⟨fun i => ?_, f, fun i => ?_⟩
  · rw [hEq]; exact (hfix i).symm
  · rw [hEq]; exact hfv i

/-! ### The relative discounted optimality equation (5.6) -/

theorem eq_5_6' (M : CMP A) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hfin : ∀ i, discValue M β i ≠ ⊤) (i : ℕ) :
    (∃ a ∈ M.U i, Summable (fun j => prob M i a j * hRel M β j) ∧
      (1 - β) * (discValue M β 0).toReal + hRel M β i =
        M.c i a + β * ∑' j, prob M i a j * hRel M β j) ∧
    (∀ a ∈ M.U i, Summable (fun j => prob M i a j * hRel M β j) →
      (1 - β) * (discValue M β 0).toReal + hRel M β i ≤
        M.c i a + β * ∑' j, prob M i a j * hRel M β j) := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  obtain ⟨hT, f, hf⟩ := disc_opt M β hβ0.le
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, r = fun j => (discValue M β j).toReal := ⟨_, rfl⟩
  have hRI : ∀ j, (discValue M β j).toReal = r j := by intro j; rw [hr]
  have hRel_eq : ∀ j, hRel M β j = r j - r 0 := by intro j; unfold hRel; rw [hRI, hRI]
  have hJr : ∀ j, discValue M β j = ENNReal.ofReal (r j) := by
    intro j; rw [← hRI]; exact (ENNReal.ofReal_toReal (hfin j)).symm
  have hr0 : ∀ j, 0 ≤ r j := by intro j; rw [← hRI]; exact ENNReal.toReal_nonneg
  have hPr : ∀ x a j, M.P (x, a) {j} = ENNReal.ofReal (prob M x a j) :=
    fun x a j => (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hterm : ∀ x a j, M.P (x, a) {j} * discValue M β j = ENNReal.ofReal (prob M x a j * r j) := by
    intro x a j; rw [hPr, hJr, ENNReal.ofReal_mul (prob_nonneg' M x a j)]
  have hfun : ∀ a, (fun j => prob M i a j * hRel M β j) =
      fun j => prob M i a j * r j - prob M i a j * r 0 := by
    intro a; funext j; rw [hRel_eq]; ring
  have hsum_iff : ∀ a, Summable (fun j => prob M i a j * hRel M β j) ↔
      Summable (fun j => prob M i a j * r j) := by
    intro a
    have hp := (prob_hasSum M i a).summable
    rw [hfun a]
    constructor
    · intro h
      have := h.add (hp.mul_right (r 0))
      refine this.congr fun j => ?_
      ring
    · intro h; exact h.sub (hp.mul_right (r 0))
  have htsum : ∀ a, Summable (fun j => prob M i a j * r j) →
      ∑' j, prob M i a j * hRel M β j = ∑' j, prob M i a j * r j - r 0 := by
    intro a h
    have hp := (prob_hasSum M i a).summable
    rw [hfun a, h.tsum_sub (hp.mul_right (r 0)), tsum_mul_right, prob_tsum, one_mul]
  have hofsum : ∀ a, Summable (fun j => prob M i a j * r j) →
      ∑' j, M.P (i, a) {j} * discValue M β j = ENNReal.ofReal (∑' j, prob M i a j * r j) := by
    intro a h
    simp_rw [hterm]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (prob_nonneg' M i a j) (hr0 j)) h).symm
  have hnn : ∀ a ∈ M.U i, 0 ≤ M.c i a + β * ∑' j, prob M i a j * r j := fun a ha =>
    add_nonneg (M.c_nonneg i a ha)
      (mul_nonneg hβ0.le (tsum_nonneg fun j => mul_nonneg (prob_nonneg' M i a j) (hr0 j)))
  have hconv : ∀ a ∈ M.U i, Summable (fun j => prob M i a j * r j) →
      ENNReal.ofReal (M.c i a) + ENNReal.ofReal β * ∑' j, M.P (i, a) {j} * discValue M β j =
        ENNReal.ofReal (M.c i a + β * ∑' j, prob M i a j * r j) := by
    intro a ha h
    rw [hofsum a h, ← ENNReal.ofReal_mul hβ0.le, ← ENNReal.ofReal_add (M.c_nonneg i a ha)
      (mul_nonneg hβ0.le (tsum_nonneg fun j => mul_nonneg (prob_nonneg' M i a j) (hr0 j)))]
  have hineq : ∀ a ∈ M.U i, Summable (fun j => prob M i a j * r j) →
      r i ≤ M.c i a + β * ∑' j, prob M i a j * r j := by
    intro a ha h
    have h1 : discValue M β i ≤ ENNReal.ofReal (M.c i a) +
        ENNReal.ofReal β * ∑' j, M.P (i, a) {j} * discValue M β j :=
      (hT i).le.trans (iInf₂_le a ha)
    rw [hconv a ha h] at h1
    rw [← hRI]
    exact ENNReal.toReal_le_of_le_ofReal (hnn a ha) h1
  rw [hRI 0, hRel_eq i]
  constructor
  · refine ⟨f.1 i, f.2 i, ?_⟩
    have hfi := hf i
    have hne : ∑' j, M.P (i, f.1 i) {j} * discValue M β j ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hβ0).ne', add_top] at hfi
      exact hfin i hfi
    have hs : Summable (fun j => prob M i (f.1 i) j * r j) := by
      have := ENNReal.summable_toReal hne
      refine this.congr fun j => ?_
      rw [hterm, ENNReal.toReal_ofReal (mul_nonneg (prob_nonneg' M _ _ j) (hr0 j))]
    refine ⟨(hsum_iff _).mpr hs, ?_⟩
    rw [htsum _ hs]
    have h2 : r i = M.c i (f.1 i) + β * ∑' j, prob M i (f.1 i) j * r j := by
      have h3 := congrArg ENNReal.toReal hfi
      rw [hconv _ (f.2 i) hs, ENNReal.toReal_ofReal (hnn _ (f.2 i)), hRI] at h3
      exact h3
    rw [h2]
    ring
  · intro a ha hsa
    have hs := (hsum_iff a).mp hsa
    rw [htsum a hs]
    have := hineq a ha hs
    nlinarith

theorem prob_series_bound (M : CMP A) (i : ℕ) (a : A) (h : ℕ → ℝ) (K : ℝ) (hK : ∀ j, |h j| ≤ K) :
    Summable (fun j => prob M i a j * h j) ∧ |∑' j, prob M i a j * h j| ≤ K := by
  have hs := (prob_hasSum M i a).summable
  have hb : ∀ j, ‖prob M i a j * h j‖ ≤ prob M i a j * K := by
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (prob_nonneg' M i a j)]
    exact mul_le_mul_of_nonneg_left (hK j) (prob_nonneg' M i a j)
  have hsK : Summable (fun j => prob M i a j * K) := hs.mul_right K
  have hsum : Summable (fun j => prob M i a j * h j) := hsK.of_norm_bounded hb
  refine ⟨hsum, ?_⟩
  calc |∑' j, prob M i a j * h j| = ‖∑' j, prob M i a j * h j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' j, ‖prob M i a j * h j‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' j, prob M i a j * K := hsum.norm.tsum_le_tsum hb hsK
    _ = K := by rw [tsum_mul_right, prob_tsum, one_mul]

/-- Bounds of a probability-weighted series by bounds of its terms. -/
lemma series_between (M : CMP A) (i : ℕ) (a : A) (v : ℕ → ℝ) (lo hi : ℝ)
    (hv : ∀ j, lo ≤ v j ∧ v j ≤ hi) (hs : Summable (fun j => prob M i a j * v j)) :
    lo ≤ ∑' j, prob M i a j * v j ∧ ∑' j, prob M i a j * v j ≤ hi := by
  have hp := (prob_hasSum M i a).summable
  constructor
  · calc lo = ∑' j, prob M i a j * lo := by rw [tsum_mul_right, prob_tsum, one_mul]
      _ ≤ ∑' j, prob M i a j * v j :=
        (hp.mul_right lo).tsum_le_tsum
          (fun j => mul_le_mul_of_nonneg_left (hv j).1 (prob_nonneg' M i a j)) hs
  · calc ∑' j, prob M i a j * v j ≤ ∑' j, prob M i a j * hi :=
        hs.tsum_le_tsum
          (fun j => mul_le_mul_of_nonneg_left (hv j).2 (prob_nonneg' M i a j)) (hp.mul_right hi)
      _ = hi := by rw [tsum_mul_right, prob_tsum, one_mul]

lemma series_shift (M : CMP A) (i : ℕ) (a : A) (v : ℕ → ℝ) (K : ℝ) (hv : ∀ j, |v j| ≤ K) :
    Summable (fun j => prob M i a j * (v j + K)) ∧
      ∑' j, prob M i a j * (v j + K) = ∑' j, prob M i a j * v j + K := by
  have hs1 := (prob_series_bound M i a v K hv).1
  have hs2 : Summable (fun j => prob M i a j * K) := (prob_hasSum M i a).summable.mul_right K
  have hfun : (fun j => prob M i a j * (v j + K)) = fun j => prob M i a j * v j + prob M i a j * K := by
    funext j; ring
  rw [hfun]
  refine ⟨hs1.add hs2, ?_⟩
  rw [hs1.tsum_add hs2, tsum_mul_right, prob_tsum, one_mul]

lemma tsum_shift_ge (M : CMP A) (i : ℕ) (a : A) (v : ℕ → ℝ) (K : ℝ) (hv : ∀ j, |v j| ≤ K) (N : ℕ) :
    ∑ j ∈ Finset.range N, prob M i a j * (v j + K) - K ≤ ∑' j, prob M i a j * v j := by
  obtain ⟨hs, heq⟩ := series_shift M i a v K hv
  have hle : ∑ j ∈ Finset.range N, prob M i a j * (v j + K) ≤ ∑' j, prob M i a j * (v j + K) :=
    hs.sum_le_tsum _ (fun j _ => mul_nonneg (prob_nonneg' M i a j)
      (by linarith [(abs_le.mp (hv j)).1]))
  linarith

theorem exists_subseq_tendsto_pointwise (g : ℕ → ℝ) (u : ℕ → ℕ → ℝ) (B K : ℝ)
    (hg : ∀ n, |g n| ≤ B) (hu : ∀ n i, |u n i| ≤ K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ρ : ℝ, ∃ h : ℕ → ℝ,
      Tendsto (fun k => g (φ k)) atTop (𝓝 ρ) ∧ ∀ i, Tendsto (fun k => u (φ k) i) atTop (𝓝 (h i)) := by
  let s : Set (ℝ × (ℕ → ℝ)) := Set.Icc (-B) B ×ˢ Set.univ.pi (fun _ => Set.Icc (-K) K)
  have hs : IsCompact s := isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hx : ∀ n, (g n, u n) ∈ s := fun n =>
    ⟨abs_le.mp (hg n), fun i _ => abs_le.mp (hu n i)⟩
  obtain ⟨⟨ρ, h⟩, -, φ, hφ, hlim⟩ := hs.tendsto_subseq hx
  refine ⟨φ, hφ, ρ, h, ?_, fun i => ?_⟩
  · exact (continuous_fst.tendsto _).comp hlim
  · exact (((continuous_apply i).comp continuous_snd).tendsto _).comp hlim

theorem acoe_of_limit (M : CMP A) (β g : ℕ → ℝ) (u : ℕ → ℕ → ℝ) (ρ : ℝ) (h : ℕ → ℝ) (K : ℝ)
    (hβ : ∀ n, β n ∈ Set.Ioo (0 : ℝ) 1) (hβ1 : Tendsto β atTop (𝓝 1))
    (hg : Tendsto g atTop (𝓝 ρ)) (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 (h i)))
    (hbd : ∀ n i, |u n i| ≤ K)
    (heq : ∀ n i,
      (∃ a ∈ M.U i, g n + u n i = M.c i a + β n * ∑' j, prob M i a j * u n j) ∧
      (∀ a ∈ M.U i, g n + u n i ≤ M.c i a + β n * ∑' j, prob M i a j * u n j)) :
    ACOE M ρ h := by
  have hhK : ∀ i, |h i| ≤ K := fun i =>
    le_of_tendsto' ((continuous_abs.tendsto _).comp (hu i)) (fun n => hbd n i)
  intro i
  have hle : ∀ a ∈ M.U i, ρ + h i ≤ M.c i a + ∑' j, prob M i a j * h j := by
    intro a ha
    have hS : Tendsto (fun n => ∑' j, prob M i a j * u n j) atTop
        (𝓝 (∑' j, prob M i a j * h j)) := by
      apply tendsto_tsum_of_dominated_convergence (bound := fun j => prob M i a j * K)
        ((prob_hasSum M i a).summable.mul_right K)
      · intro j; exact (hu j).const_mul _
      · refine Eventually.of_forall (fun n j => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (prob_nonneg' M i a j)]
        exact mul_le_mul_of_nonneg_left (hbd n j) (prob_nonneg' M i a j)
    have hL : Tendsto (fun n => g n + u n i) atTop (𝓝 (ρ + h i)) := hg.add (hu i)
    have hR : Tendsto (fun n => M.c i a + β n * ∑' j, prob M i a j * u n j) atTop
        (𝓝 (M.c i a + 1 * ∑' j, prob M i a j * h j)) := tendsto_const_nhds.add (hβ1.mul hS)
    rw [one_mul] at hR
    exact le_of_tendsto_of_tendsto' hL hR (fun n => (heq n i).2 a ha)
  refine ⟨fun a _ => (prob_series_bound M i a h K hhK).1, ?_, hle⟩
  choose a ha haeq using fun n => (heq n i).1
  obtain ⟨a', ha', ψ, hψ, hlim⟩ := (M.U_compact i).tendsto_subseq ha
  have hlim' : Tendsto (fun k => a (ψ k)) atTop (𝓝[M.U i] a') :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun k => ha _⟩
  have hpk : ∀ j, Tendsto (fun k => prob M i (a (ψ k)) j) atTop (𝓝 (prob M i a' j)) :=
    fun j => ((M.P_cont i j) a' ha').tendsto.comp hlim'
  have hck : Tendsto (fun k => M.c i (a (ψ k))) atTop (𝓝 (M.c i a')) :=
    ((M.c_cont i) a' ha').tendsto.comp hlim'
  have hψt := hψ.tendsto_atTop
  have hF : ∀ N : ℕ, M.c i a' + (∑ j ∈ Finset.range N, prob M i a' j * (h j + K) - K) ≤ ρ + h i := by
    intro N
    have hFk : Tendsto (fun k => ∑ j ∈ Finset.range N, prob M i (a (ψ k)) j * (u (ψ k) j + K))
        atTop (𝓝 (∑ j ∈ Finset.range N, prob M i a' j * (h j + K))) :=
      tendsto_finsetSum _ (fun j _ => (hpk j).mul (((hu j).comp hψt).add_const K))
    have hR : Tendsto (fun k => M.c i (a (ψ k)) + β (ψ k) *
        (∑ j ∈ Finset.range N, prob M i (a (ψ k)) j * (u (ψ k) j + K) - K)) atTop
        (𝓝 (M.c i a' + 1 * (∑ j ∈ Finset.range N, prob M i a' j * (h j + K) - K))) :=
      hck.add ((hβ1.comp hψt).mul (hFk.sub_const K))
    rw [one_mul] at hR
    have hL : Tendsto (fun k => g (ψ k) + u (ψ k) i) atTop (𝓝 (ρ + h i)) :=
      (hg.comp hψt).add ((hu i).comp hψt)
    refine le_of_tendsto_of_tendsto' hR hL (fun k => ?_)
    have h1 := tsum_shift_ge M i (a (ψ k)) (u (ψ k)) K (hbd (ψ k)) N
    have h2 := mul_le_mul_of_nonneg_left h1 (hβ (ψ k)).1.le
    have h3 := haeq (ψ k)
    linarith
  obtain ⟨hsK, hshift⟩ := series_shift M i a' h K hhK
  have hlimN : Tendsto (fun N : ℕ => M.c i a' +
      (∑ j ∈ Finset.range N, prob M i a' j * (h j + K) - K)) atTop
      (𝓝 (M.c i a' + (∑' j, prob M i a' j * (h j + K) - K))) :=
    tendsto_const_nhds.add (hsK.hasSum.tendsto_sum_nat.sub_const K)
  have hge := le_of_tendsto' hlimN hF
  refine ⟨a', ha', le_antisymm (hle a' ha') ?_⟩
  rw [hshift] at hge
  linarith

theorem abelian_rate (M : CMP A) (ρ : ℝ) (h : ℕ → ℝ) (C : ℝ) (hsol : ACOE M ρ h)
    (hC : ∀ i, |h i| ≤ C)
    (β g : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (u : ℕ → ℝ) (K : ℝ) (hK : ∀ i, |u i| ≤ K)
    (heq : ∀ i,
      (∃ a ∈ M.U i, g + u i = M.c i a + β * ∑' j, prob M i a j * u j) ∧
      (∀ a ∈ M.U i, g + u i ≤ M.c i a + β * ∑' j, prob M i a j * u j)) :
    |g - ρ| ≤ (1 - β) * (K + 2 * C) := by
  obtain ⟨hβ0, hβ1⟩ := hβ
  have hwb : ∀ i, -(K + C) ≤ u i - h i ∧ u i - h i ≤ K + C := by
    intro i
    obtain ⟨a1, a2⟩ := abs_le.mp (hK i)
    obtain ⟨b1, b2⟩ := abs_le.mp (hC i)
    exact ⟨by linarith, by linarith⟩
  -- series identities, for any action
  have hser : ∀ i a, ∑' j, prob M i a j * (u j - h j) =
      ∑' j, prob M i a j * u j - ∑' j, prob M i a j * h j := by
    intro i a
    have hsu := (prob_series_bound M i a u K hK).1
    have hsh := (prob_series_bound M i a h C hC).1
    rw [← hsu.tsum_sub hsh]
    congr 1; funext j; ring
  have hsw : ∀ i a, Summable (fun j => prob M i a j * (u j - h j)) := by
    intro i a
    have hsu := (prob_series_bound M i a u K hK).1
    have hsh := (prob_series_bound M i a h C hC).1
    have := hsu.sub hsh
    refine this.congr (fun j => ?_)
    ring
  have hbdd : BddAbove (Set.range fun i => u i - h i) :=
    ⟨K + C, by rintro _ ⟨i, rfl⟩; exact (hwb i).2⟩
  have hbdd' : BddAbove (Set.range fun i => -(u i - h i)) :=
    ⟨K + C, by rintro _ ⟨i, rfl⟩; linarith [(hwb i).1]⟩
  set W := ⨆ i, (u i - h i) with hW
  set W' := ⨆ i, -(u i - h i) with hW'
  have hWge : -(K + C) ≤ W := le_trans (hwb 0).1 (le_ciSup hbdd 0)
  have hW'ge : -(K + C) ≤ W' := le_trans (by linarith [(hwb 0).2]) (le_ciSup hbdd' 0)
  have h1b : 0 ≤ 1 - β := by linarith
  rw [abs_le]
  constructor
  · -- lower bound: ρ - g ≤ ...
    have : ρ - g ≤ (1 - β) * (K + 2 * C) := by
      refine le_of_forall_pos_le_add (fun η hη => ?_)
      obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup (show W' - η < W' by linarith)
      obtain ⟨a, ha, haeq⟩ := (heq i).1
      have hac := (hsol i).2.2 a ha
      have hsh := prob_series_bound M i a h C hC
      have hbt := series_between M i a (fun j => u j - h j) (-W') W
        (fun j => ⟨by linarith [le_ciSup hbdd' j], le_ciSup hbdd j⟩) (hsw i a)
      rw [hser i a] at hbt
      have e1 := mul_le_mul_of_nonneg_left (by linarith [hbt.1] :
        -(∑' j, prob M i a j * u j - ∑' j, prob M i a j * h j) ≤ W') hβ0.le
      have e2 := mul_le_mul_of_nonneg_left (le_abs_self (∑' j, prob M i a j * h j)) h1b
      have e3 := mul_le_mul_of_nonneg_left hsh.2 h1b
      have e4 := mul_le_mul_of_nonneg_left (by linarith : -W' ≤ K + C) h1b
      nlinarith
    linarith
  · refine le_of_forall_pos_le_add (fun η hη => ?_)
    obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup (show W - η < W by linarith)
    obtain ⟨a, ha, haeq⟩ := (hsol i).2.1
    have hac := (heq i).2 a ha
    have hsh := prob_series_bound M i a h C hC
    have hbt := series_between M i a (fun j => u j - h j) (-W') W
      (fun j => ⟨by linarith [le_ciSup hbdd' j], le_ciSup hbdd j⟩) (hsw i a)
    rw [hser i a] at hbt
    have e1 := mul_le_mul_of_nonneg_left hbt.2 hβ0.le
    have e2 := mul_le_mul_of_nonneg_left (neg_abs_le (∑' j, prob M i a j * h j)) h1b
    have e3 := mul_le_mul_of_nonneg_left hsh.2 h1b
    have e4 := mul_le_mul_of_nonneg_left (by linarith : -W ≤ K + C) h1b
    nlinarith

/-- The parent, assuming the relative discounted optimality equation `eq_5_6` as a hypothesis. -/
theorem theorem_5_2_of_eq_5_6 (M : CMP A) (hfin : ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, discValue M β i ≠ ⊤)
    (K : ℝ) (hK : 0 < K) (hbd : ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, |hRel M β i| ≤ K)
    (h56 : ∀ β : ℝ, β ∈ Set.Ioo (0 : ℝ) 1 → (∀ i, discValue M β i ≠ ⊤) → ∀ i : ℕ,
      (∃ a ∈ M.U i, Summable (fun j => prob M i a j * hRel M β j) ∧
        (1 - β) * (discValue M β 0).toReal + hRel M β i =
          M.c i a + β * ∑' j, prob M i a j * hRel M β j) ∧
      (∀ a ∈ M.U i, Summable (fun j => prob M i a j * hRel M β j) →
        (1 - β) * (discValue M β 0).toReal + hRel M β i ≤
          M.c i a + β * ∑' j, prob M i a j * hRel M β j)) :
    ∃ ρ : ℝ, ∃ h : ℕ → ℝ, ∃ β : ℕ → ℝ,
      (ACOE M ρ h ∧ ∃ C, ∀ i, |h i| ≤ C) ∧
      ((∀ n, β n ∈ Set.Ioo (0 : ℝ) 1) ∧ Tendsto β atTop (𝓝 1) ∧
        ∀ i, Tendsto (fun n => hRel M (β n) i) atTop (𝓝 (h i))) ∧
      ∀ i, Tendsto (fun b => (1 - b) * (discValue M b i).toReal) (𝓝[<] 1) (𝓝 ρ) := by
  have hEq : ∀ b ∈ Set.Ioo (0 : ℝ) 1, ∀ i,
      (∃ a ∈ M.U i, (1 - b) * (discValue M b 0).toReal + hRel M b i =
        M.c i a + b * ∑' j, prob M i a j * hRel M b j) ∧
      (∀ a ∈ M.U i, (1 - b) * (discValue M b 0).toReal + hRel M b i ≤
        M.c i a + b * ∑' j, prob M i a j * hRel M b j) := by
    intro b hb i
    obtain ⟨⟨a, ha, -, he⟩, hle⟩ := h56 b hb (hfin b hb) i
    exact ⟨⟨a, ha, he⟩, fun a ha => hle a ha (prob_series_bound M i a _ K (hbd b hb)).1⟩
  obtain ⟨a₀, ha₀⟩ := M.U_nonempty 0
  have hGb : ∀ b ∈ Set.Ioo (0 : ℝ) 1, |(1 - b) * (discValue M b 0).toReal| ≤ M.c 0 a₀ + K := by
    intro b hb
    have h1 := (hEq b hb 0).2 a₀ ha₀
    have h0 : hRel M b 0 = 0 := sub_self _
    have h2 := (prob_series_bound M 0 a₀ _ K (hbd b hb)).2
    have hG0 : 0 ≤ (1 - b) * (discValue M b 0).toReal :=
      mul_nonneg (by linarith [hb.2]) ENNReal.toReal_nonneg
    rw [abs_of_nonneg hG0]
    rw [h0] at h1
    have h3 := mul_le_mul_of_nonneg_left (le_abs_self (∑' j, prob M 0 a₀ j * hRel M b j)) hb.1.le
    have h4 := mul_le_of_le_one_left (abs_nonneg (∑' j, prob M 0 a₀ j * hRel M b j)) hb.2.le
    linarith
  obtain ⟨βs, hβs_def⟩ : ∃ f : ℕ → ℝ, f = fun (n : ℕ) => 1 - 1 / ((n : ℝ) + 2) := ⟨_, rfl⟩
  have hβs_mem : ∀ n, βs n ∈ Set.Ioo (0 : ℝ) 1 := by
    intro n
    subst hβs_def
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hp : 0 < 1 / ((n : ℝ) + 2) := by positivity
    have hl : 1 / ((n : ℝ) + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
    exact ⟨by simp only; linarith, by simp only; linarith⟩
  have hβs_lim : Tendsto βs atTop (𝓝 1) := by
    subst hβs_def
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    rw [sub_zero] at this
    exact this
  obtain ⟨φ, hφ, ρ, h, hgl, hul⟩ := exists_subseq_tendsto_pointwise
    (fun n => (1 - βs n) * (discValue M (βs n) 0).toReal) (fun n i => hRel M (βs n) i)
    (M.c 0 a₀ + K) K (fun n => hGb _ (hβs_mem n)) (fun n i => hbd _ (hβs_mem n) i)
  have hφt := hφ.tendsto_atTop
  have hhK : ∀ i, |h i| ≤ K := fun i =>
    le_of_tendsto' ((continuous_abs.tendsto _).comp (hul i)) (fun n => hbd _ (hβs_mem _) i)
  have hacoe : ACOE M ρ h :=
    acoe_of_limit M (fun k => βs (φ k)) (fun k => (1 - βs (φ k)) * (discValue M (βs (φ k)) 0).toReal)
      (fun k i => hRel M (βs (φ k)) i) ρ h K (fun k => hβs_mem _) (hβs_lim.comp hφt) hgl hul
      (fun k i => hbd _ (hβs_mem _) i) (fun k i => hEq _ (hβs_mem _) i)
  refine ⟨ρ, h, fun k => βs (φ k), ⟨hacoe, K, hhK⟩, ⟨fun k => hβs_mem _, hβs_lim.comp hφt, hul⟩, ?_⟩
  intro i
  have hbound : ∀ b ∈ Set.Ioo (0 : ℝ) 1,
      |(1 - b) * (discValue M b i).toReal - ρ| ≤ (1 - b) * (4 * K) := by
    intro b hb
    have h1 := abelian_rate M ρ h K hacoe hhK b ((1 - b) * (discValue M b 0).toReal) hb
      (hRel M b) K (hbd b hb) (hEq b hb)
    have h2 : (1 - b) * (discValue M b i).toReal - ρ =
        ((1 - b) * (discValue M b 0).toReal - ρ) + (1 - b) * hRel M b i := by
      unfold hRel; ring
    rw [h2]
    have h1b : (0 : ℝ) ≤ 1 - b := by linarith [hb.2]
    have h3 : |(1 - b) * hRel M b i| ≤ (1 - b) * K := by
      rw [abs_mul, abs_of_nonneg h1b]
      exact mul_le_mul_of_nonneg_left (hbd b hb i) h1b
    calc _ ≤ |(1 - b) * (discValue M b 0).toReal - ρ| + |(1 - b) * hRel M b i| := abs_add_le _ _
      _ ≤ (1 - b) * (K + 2 * K) + (1 - b) * K := add_le_add h1 h3
      _ = (1 - b) * (4 * K) := by ring
  have hlim0 : Tendsto (fun b : ℝ => (1 - b) * (4 * K)) (𝓝[<] 1) (𝓝 0) := by
    have : Tendsto (fun b : ℝ => (1 - b) * (4 * K)) (𝓝 1) (𝓝 ((1 - 1) * (4 * K))) :=
      ((continuous_const.sub continuous_id).mul continuous_const).tendsto 1
    rw [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ hlim0
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with b hb
  simp only [Real.norm_eq_abs, abs_abs]
  exact hbound b hb


/-- Theorem 5.2, from the relative discounted optimality equation proved above. -/
theorem theorem_5_2_full (M : CMP A) (hfin : ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, discValue M β i ≠ ⊤)
    (K : ℝ) (hK : 0 < K) (hbd : ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, |hRel M β i| ≤ K) :
    ∃ ρ : ℝ, ∃ h : ℕ → ℝ, ∃ β : ℕ → ℝ,
      (ACOE M ρ h ∧ ∃ C, ∀ i, |h i| ≤ C) ∧
      ((∀ n, β n ∈ Set.Ioo (0 : ℝ) 1) ∧ Tendsto β atTop (𝓝 1) ∧
        ∀ i, Tendsto (fun n => hRel M (β n) i) atTop (𝓝 (h i))) ∧
      ∀ i, Tendsto (fun b => (1 - b) * (discValue M b i).toReal) (𝓝[<] 1) (𝓝 ρ) :=
  theorem_5_2_of_eq_5_6 M hfin K hK hbd (fun β hβ hf i => eq_5_6' M β hβ hf i)

end ArapostathisAC.VanishingDiscount

open Filter Topology ArapostathisAC.VanishingDiscount in
theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (hfin : ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, discValue M β i ≠ ⊤)
    (K : ℝ) (hK : 0 < K) (hbd : ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, |hRel M β i| ≤ K) :
    ∃ ρ : ℝ, ∃ h : ℕ → ℝ, ∃ β : ℕ → ℝ,
      (ACOE M ρ h ∧ ∃ C, ∀ i, |h i| ≤ C) ∧
      ((∀ n, β n ∈ Set.Ioo (0 : ℝ) 1) ∧ Tendsto β atTop (𝓝 1) ∧
        ∀ i, Tendsto (fun n => hRel M (β n) i) atTop (𝓝 (h i))) ∧
      ∀ i, Tendsto (fun b => (1 - b) * (discValue M b i).toReal) (𝓝[<] 1) (𝓝 ρ) := by
  exact theorem_5_2_full M hfin K hK hbd
