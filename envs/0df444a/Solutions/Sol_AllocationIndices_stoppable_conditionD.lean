-- Prove2me | solution 1 for AllocationIndices.stoppable_conditionD
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T07:52:48.113148+00:00
-- url     : https://prove2.me/submissions/1f07bf83-bb3a-4608-934d-b1d002dce872

import Mathlib
import Definitions.Def_AllocationIndices_Superprocess

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_prob {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_marg0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) : (markovChainMeasure P x).map (Preorder.frestrictLe 0) =
      Measure.dirac (fun _ ↦ x) := by
  rw [markovChainMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp, Measure.map_dirac' (MeasurableEquiv.measurable _)]
  congr 1

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_int0 {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) (F : S → ℝ) (hF : Measurable F) :
    ∫ ω, F (ω 0) ∂markovChainMeasure P x = F x := by
  have hFm : Measurable (fun h : (Π _i : Finset.Iic 0, S) ↦ F (h ⟨0, Finset.mem_Iic.2 le_rfl⟩)) :=
    hF.comp (measurable_pi_apply _)
  have h1 := integral_map (μ := markovChainMeasure P x) (Preorder.measurable_frestrictLe 0).aemeasurable
    hFm.aestronglyMeasurable
  rw [p2ma2_marg0, integral_dirac' _ _ hFm.stronglyMeasurable] at h1
  exact h1.symm

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_int_of_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (F : α → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_abs_int_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (F : α → ℝ) (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    |∫ x, F x ∂μ| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := B)
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hB x)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

open MeasureTheory ProbabilityTheory BanditAlgorithm in
private lemma p2ma2_markov {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (s : ℕ) (A : Set (ℕ → S))
    (hA : MeasurableSet[trajectoryFiltration S s] A) (g : S → ℝ) (Bg : ℝ)
    (hg : ∀ y, |g y| ≤ Bg) :
    ∫ ω, A.indicator (fun ω ↦ g (ω (s + 1))) ω ∂markovChainMeasure P x =
      ∫ ω, A.indicator (fun ω ↦ ∫ z, g z ∂P (ω s)) ω ∂markovChainMeasure P x := by
  haveI := p2ma2_prob P x
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  have hgm : Measurable g := Measurable.of_discrete
  have hPgm : Measurable (fun y ↦ ∫ z, g z ∂P y) := Measurable.of_discrete
  have hmap : (markovChainMeasure P x).map (Preorder.frestrictLe s) ⊗ₘ markovChainStep P s =
      (markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe s ω, ω (s + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure (X := fun _ : ℕ ↦ S)
      (μ₀ := Measure.dirac x) (κ := markovChainStep P) (a := s)
  have hΦ : Measurable (fun ω : ℕ → S ↦ (Preorder.frestrictLe s ω, ω (s + 1))) :=
    (Preorder.measurable_frestrictLe s).prodMk (measurable_pi_apply (s + 1))
  have hFm : Measurable ((B ×ˢ (Set.univ : Set S)).indicator
      (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2)) :=
    (hgm.comp measurable_snd).indicator (hB.prod MeasurableSet.univ)
  have hFint : Integrable ((B ×ˢ (Set.univ : Set S)).indicator
      (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2))
      ((markovChainMeasure P x).map (Preorder.frestrictLe s) ⊗ₘ markovChainStep P s) :=
    p2ma2_int_of_bound _ _ hFm Bg (fun p ↦ by
      by_cases hp : p ∈ B ×ˢ (Set.univ : Set S)
      · rw [Set.indicator_of_mem hp]; exact hg _
      · rw [Set.indicator_of_notMem hp, abs_zero]; exact le_trans (abs_nonneg _) (hg p.2))
  have hGm : Measurable (B.indicator
      (fun h : (Π _i : Finset.Iic s, S) ↦ ∫ z, g z ∂P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩))) :=
    (hPgm.comp (measurable_pi_apply _)).indicator hB
  calc ∫ ω, ((fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B).indicator (fun ω ↦ g (ω (s + 1))) ω
        ∂markovChainMeasure P x
      = ∫ ω, (B ×ˢ (Set.univ : Set S)).indicator
          (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2)
          (Preorder.frestrictLe s ω, ω (s + 1)) ∂markovChainMeasure P x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        dsimp only
        by_cases h : Preorder.frestrictLe s ω ∈ B
        · rw [Set.indicator_of_mem (show ω ∈ (fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B from h),
            Set.indicator_of_mem (show (Preorder.frestrictLe s ω, ω (s + 1)) ∈
              B ×ˢ (Set.univ : Set S) from ⟨h, trivial⟩)]
        · rw [Set.indicator_of_notMem
              (show ω ∉ (fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B from h),
            Set.indicator_of_notMem (show (Preorder.frestrictLe s ω, ω (s + 1)) ∉
              B ×ˢ (Set.univ : Set S) from fun hh ↦ h hh.1)]
    _ = ∫ p, (B ×ˢ (Set.univ : Set S)).indicator
          (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2) p
          ∂((markovChainMeasure P x).map (fun ω ↦ (Preorder.frestrictLe s ω, ω (s + 1)))) :=
        (integral_map hΦ.aemeasurable hFm.aestronglyMeasurable).symm
    _ = ∫ p, (B ×ˢ (Set.univ : Set S)).indicator
          (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2) p
          ∂((markovChainMeasure P x).map (Preorder.frestrictLe s) ⊗ₘ markovChainStep P s) := by
        rw [hmap]
    _ = ∫ h, ∫ y, (B ×ˢ (Set.univ : Set S)).indicator
          (fun p : (Π _i : Finset.Iic s, S) × S ↦ g p.2) (h, y) ∂(markovChainStep P s h)
          ∂((markovChainMeasure P x).map (Preorder.frestrictLe s)) :=
        Measure.integral_compProd hFint
    _ = ∫ h, B.indicator
          (fun h : (Π _i : Finset.Iic s, S) ↦ ∫ z, g z ∂P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩)) h
          ∂((markovChainMeasure P x).map (Preorder.frestrictLe s)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
        have hk : markovChainStep P s h = P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩) := by
          rw [markovChainStep, Kernel.comap_apply]
        simp only
        rw [hk]
        by_cases hh : h ∈ B
        · rw [Set.indicator_of_mem hh]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
          exact Set.indicator_of_mem
            (show (h, y) ∈ B ×ˢ (Set.univ : Set S) from ⟨hh, trivial⟩) _
        · rw [Set.indicator_of_notMem hh]
          exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y ↦
            Set.indicator_of_notMem (fun hh' ↦ hh hh'.1) _)
    _ = ∫ ω, B.indicator
          (fun h : (Π _i : Finset.Iic s, S) ↦ ∫ z, g z ∂P (h ⟨s, Finset.mem_Iic.2 le_rfl⟩))
          (Preorder.frestrictLe s ω) ∂markovChainMeasure P x :=
        integral_map (Preorder.measurable_frestrictLe s).aemeasurable hGm.aestronglyMeasurable
    _ = ∫ ω, ((fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B).indicator
          (fun ω ↦ ∫ z, g z ∂P (ω s)) ω ∂markovChainMeasure P x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        dsimp only
        by_cases h : Preorder.frestrictLe s ω ∈ B
        · rw [Set.indicator_of_mem h,
            Set.indicator_of_mem (show ω ∈ (fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B from h)]
          rfl
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem
            (show ω ∉ (fun ω (i : Finset.Iic s) ↦ ω i.1) ⁻¹' B from h)]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_fixgen {Z : Type*} (T : (Z → ℝ) → (Z → ℝ)) (a B : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (hB : 0 ≤ B)
    (hcontr : ∀ (u v : Z → ℝ) (Bu Bv D : ℝ), (∀ z, |u z| ≤ Bu) → (∀ z, |v z| ≤ Bv) →
      (∀ z, |u z - v z| ≤ D) → ∀ y, |T u y - T v y| ≤ a * D)
    (h0 : ∀ y, |T 0 y| ≤ B) :
    ∃ G : Z → ℝ, (∀ y, |G y| ≤ B / (1 - a)) ∧ ∀ y, G y = T G y := by
  have h1a : 0 < 1 - a := by linarith
  have hbd : ∀ u : Z → ℝ, (∀ z, |u z| ≤ B / (1 - a)) → ∀ y, |T u y| ≤ B / (1 - a) := by
    intro u hu y
    have h1 := hcontr u 0 (B / (1 - a)) 0 (B / (1 - a)) hu (fun z ↦ by simp)
      (fun z ↦ by simpa using hu z) y
    have h2 : |T u y| ≤ |T u y - T 0 y| + |T 0 y| := by
      have := abs_add_le (T u y - T 0 y) (T 0 y)
      rwa [sub_add_cancel] at this
    have h3 : B + a * (B / (1 - a)) = B / (1 - a) := by field_simp; ring
    linarith [h0 y]
  let seq : ℕ → Z → ℝ := fun k ↦ T^[k] 0
  have hseq_succ : ∀ k, seq (k + 1) = T (seq k) := fun k ↦ Function.iterate_succ_apply' T k 0
  have hseqb : ∀ k y, |seq k y| ≤ B / (1 - a) := by
    intro k
    induction k with
    | zero => intro y; show |(0 : ℝ)| ≤ _; rw [abs_zero]; positivity
    | succ k ih => rw [hseq_succ]; exact hbd _ ih
  have hdiff : ∀ k y, |seq (k + 1) y - seq k y| ≤ B * a ^ k := by
    intro k
    induction k with
    | zero =>
        intro y
        show |T 0 y - 0| ≤ B * a ^ 0
        rw [sub_zero, pow_zero, mul_one]
        exact h0 y
    | succ k ih =>
        intro y
        calc |seq (k + 1 + 1) y - seq (k + 1) y| = |T (seq (k + 1)) y - T (seq k) y| := by
              rw [hseq_succ (k + 1), hseq_succ k]
          _ ≤ a * (B * a ^ k) := hcontr _ _ _ _ _ (hseqb (k + 1)) (hseqb k) ih y
          _ = B * a ^ (k + 1) := by ring
  have hgeo : ∀ y k, dist (seq k y) (seq (k + 1) y) ≤ B * a ^ k := fun y k ↦ by
    rw [Real.dist_eq, abs_sub_comm]; exact hdiff k y
  have hcauchy : ∀ y, CauchySeq (fun k ↦ seq k y) := fun y ↦
    cauchySeq_of_le_geometric a B ha1 (hgeo y)
  choose G hG using fun y ↦ cauchySeq_tendsto_of_complete (hcauchy y)
  have hGk : ∀ k y, |seq k y - G y| ≤ B * a ^ k / (1 - a) := fun k y ↦ by
    have := dist_le_of_le_geometric_of_tendsto a B ha1 (hgeo y) (hG y) k
    rwa [Real.dist_eq] at this
  have hGb : ∀ y, |G y| ≤ B / (1 - a) := fun y ↦ by
    have := hGk 0 y
    have h0' : seq 0 y = 0 := rfl
    rwa [h0', zero_sub, abs_neg, pow_zero, mul_one] at this
  refine ⟨G, hGb, fun y ↦ ?_⟩
  have hT : Filter.Tendsto (fun k ↦ seq (k + 1) y) Filter.atTop (nhds (T G y)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hlim : Filter.Tendsto (fun k : ℕ ↦ a * (B * a ^ k / (1 - a))) Filter.atTop
        (nhds 0) := by
      have := (((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul B).div_const
        (1 - a)).const_mul a
      simpa using this
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ ?_) hlim
    rw [Real.dist_eq, hseq_succ k]
    exact hcontr _ _ _ _ _ (hseqb k) hGb (hGk k) y
  have hT' : Filter.Tendsto (fun k ↦ seq (k + 1) y) Filter.atTop (nhds (G y)) :=
    (hG y).comp (Filter.tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hT' hT

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private noncomputable def p2ma2_Q {X U : Type*} [MeasurableSpace X] (E : DecisionProcess X U)
    (a : ℝ) (V : (Fin 2 → X) → ℝ) (z : Fin 2 → X) (c : Fin 2 × U) : ℝ :=
  E.reward (z c.1) c.2 + a * ∫ s, V (Function.update z c.1 s) ∂(E.step c.2 (z c.1))

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private noncomputable def p2ma2_B {X U : Type*} [MeasurableSpace X] (E : DecisionProcess X U)
    (a : ℝ) (V : (Fin 2 → X) → ℝ) (z : Fin 2 → X) : ℝ :=
  (Finset.univ : Finset (Fin 2)).sup' Finset.univ_nonempty
    (fun i ↦ (E.avail (z i)).sup' (E.avail_nonempty (z i)) (fun u ↦ p2ma2_Q E a V z (i, u)))

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_le_B {X U : Type*} [MeasurableSpace X] (E : DecisionProcess X U)
    (a : ℝ) (V : (Fin 2 → X) → ℝ) (z : Fin 2 → X) (c : Fin 2 × U)
    (hc : c.2 ∈ E.avail (z c.1)) : p2ma2_Q E a V z c ≤ p2ma2_B E a V z := by
  unfold p2ma2_B
  refine le_trans ?_ (Finset.le_sup' (fun i ↦ (E.avail (z i)).sup' (E.avail_nonempty (z i))
    (fun u ↦ p2ma2_Q E a V z (i, u))) (Finset.mem_univ c.1))
  exact Finset.le_sup' (fun u ↦ p2ma2_Q E a V z (c.1, u)) hc

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_ex_B {X U : Type*} [MeasurableSpace X] (E : DecisionProcess X U)
    (a : ℝ) (V : (Fin 2 → X) → ℝ) (z : Fin 2 → X) :
    ∃ c : Fin 2 × U, c.2 ∈ E.avail (z c.1) ∧ p2ma2_B E a V z = p2ma2_Q E a V z c := by
  unfold p2ma2_B
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin 2))
    (fun i ↦ (E.avail (z i)).sup' (E.avail_nonempty (z i)) (fun u ↦ p2ma2_Q E a V z (i, u)))
  obtain ⟨u, hu, hu'⟩ := Finset.exists_mem_eq_sup' (E.avail_nonempty (z i))
    (fun u ↦ p2ma2_Q E a V z (i, u))
  exact ⟨(i, u), hu, hi.trans hu'⟩

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_Q_contr {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (E : DecisionProcess X U) (a : ℝ) (ha0 : 0 ≤ a)
    (V V' : (Fin 2 → X) → ℝ) (Bu Bv D : ℝ) (hu : ∀ z, |V z| ≤ Bu) (hv : ∀ z, |V' z| ≤ Bv)
    (huv : ∀ z, |V z - V' z| ≤ D) (z : Fin 2 → X) (c : Fin 2 × U) :
    |p2ma2_Q E a V z c - p2ma2_Q E a V' z c| ≤ a * D := by
  unfold p2ma2_Q
  have hi : Integrable (fun s ↦ V (Function.update z c.1 s)) (E.step c.2 (z c.1)) :=
    p2ma2_int_of_bound _ _ (measurable_of_countable _) Bu (fun s ↦ hu _)
  have hi' : Integrable (fun s ↦ V' (Function.update z c.1 s)) (E.step c.2 (z c.1)) :=
    p2ma2_int_of_bound _ _ (measurable_of_countable _) Bv (fun s ↦ hv _)
  have hI : |∫ s, V (Function.update z c.1 s) ∂(E.step c.2 (z c.1)) -
      ∫ s, V' (Function.update z c.1 s) ∂(E.step c.2 (z c.1))| ≤ D := by
    rw [← integral_sub hi hi']
    exact p2ma2_abs_int_le _ _ D (fun s ↦ huv _)
  rw [show E.reward (z c.1) c.2 + a * ∫ s, V (Function.update z c.1 s) ∂(E.step c.2 (z c.1)) -
      (E.reward (z c.1) c.2 + a * ∫ s, V' (Function.update z c.1 s) ∂(E.step c.2 (z c.1))) =
      a * (∫ s, V (Function.update z c.1 s) ∂(E.step c.2 (z c.1)) -
        ∫ s, V' (Function.update z c.1 s) ∂(E.step c.2 (z c.1))) by ring,
    abs_mul, abs_of_nonneg ha0]
  exact mul_le_mul_of_nonneg_left hI ha0

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_B_contr {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (E : DecisionProcess X U) (a : ℝ) (ha0 : 0 ≤ a)
    (V V' : (Fin 2 → X) → ℝ) (Bu Bv D : ℝ) (hu : ∀ z, |V z| ≤ Bu) (hv : ∀ z, |V' z| ≤ Bv)
    (huv : ∀ z, |V z - V' z| ≤ D) (z : Fin 2 → X) :
    |p2ma2_B E a V z - p2ma2_B E a V' z| ≤ a * D := by
  have hvu : ∀ z, |V' z - V z| ≤ D := fun z ↦ by rw [abs_sub_comm]; exact huv z
  obtain ⟨c, hc, hB⟩ := p2ma2_ex_B E a V z
  obtain ⟨c', hc', hB'⟩ := p2ma2_ex_B E a V' z
  have h1 := p2ma2_Q_contr E a ha0 V V' Bu Bv D hu hv huv z c
  have h2 := p2ma2_Q_contr E a ha0 V' V Bv Bu D hv hu hvu z c'
  have h3 := p2ma2_le_B E a V' z c hc
  have h4 := p2ma2_le_B E a V z c' hc'
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_Vstar {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (E : DecisionProcess X U) (a M : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (hM0 : 0 ≤ M) (hM : ∀ y u, |E.reward y u| ≤ M) :
    ∃ V : (Fin 2 → X) → ℝ, (∀ z, |V z| ≤ M / (1 - a)) ∧ ∀ z, V z = p2ma2_B E a V z := by
  refine p2ma2_fixgen (p2ma2_B E a) a M ha0 ha1 hM0
    (fun u v Bu Bv D hu hv huv y ↦ p2ma2_B_contr E a ha0 u v Bu Bv D hu hv huv y) (fun y ↦ ?_)
  obtain ⟨c, -, hc⟩ := p2ma2_ex_B E a 0 y
  rw [hc]
  unfold p2ma2_Q
  simp only [Pi.zero_apply, integral_zero, mul_zero, add_zero]
  exact hM _ _

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_step {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (π : SFASPolicy 2 X U) (z0 : Fin 2 → X) (t : ℕ)
    (φ : SFASHistory 2 X U (t + 1) → ℝ) (B : ℝ) (hφ : ∀ h, |φ h| ≤ B) :
    ∫ h, φ h ∂sfasMeasure E π z0 (t + 1) =
      ∫ h, ∫ c, ∫ s, φ (Fin.snoc (α := fun _ ↦ (Fin 2 → X) × (Fin 2 × U)) h.1 (h.2, c),
        Function.update h.2 c.1 s) ∂(E.step c.2 (h.2 c.1)) ∂(π.select t h)
        ∂(sfasMeasure E π z0 t) := by
  rw [sfasMeasure.eq_2, integral_map
    (measurable_sfasSnoc (n := 2) (S := X) (U := U) (t := t)).aemeasurable
    (measurable_of_countable φ).aestronglyMeasurable, Measure.integral_compProd]
  swap
  · exact p2ma2_int_of_bound _ _ (measurable_of_countable _) B (fun p ↦ hφ _)
  refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
  haveI hη : IsMarkovKernel (Kernel.mk (fun p : SFASHistory 2 X U t × (Fin 2 × U) ↦
      E.step p.2.2 (p.1.2 p.2.1)) (measurable_of_countable _)) :=
    ⟨fun p ↦ (E.markov p.2.2).isProbabilityMeasure _⟩
  try dsimp only
  rw [sfasStepKernel, ProbabilityTheory.integral_compProd]
  swap
  · exact p2ma2_int_of_bound _ _ (measurable_of_countable _) B (fun p ↦ hφ _)
  rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_rr {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (M : ℝ) (hM : ∀ y u, |E.reward y u| ≤ M) (π : SFASPolicy 2 X U)
    (z0 : Fin 2 → X) (t : ℕ) :
    sfasRoundReward E π z0 t =
      ∫ h, ∫ c, E.reward (h.2 c.1) c.2 ∂(π.select t h) ∂(sfasMeasure E π z0 t) := by
  unfold sfasRoundReward
  rw [p2ma2_step E π z0 t (fun h ↦ E.reward ((h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2.1))
    ((h.1 (Fin.last t)).2.2)) M (fun h ↦ hM _ _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun c ↦ ?_)
  simp only [Fin.snoc_last, integral_const, probReal_univ, one_smul, smul_eq_mul, one_mul]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_Astep {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (V : (Fin 2 → X) → ℝ) (BV : ℝ) (hV : ∀ z, |V z| ≤ BV)
    (π : SFASPolicy 2 X U) (z0 : Fin 2 → X) (t : ℕ) :
    ∫ h, V h.2 ∂sfasMeasure E π z0 (t + 1) =
      ∫ h, ∫ c, ∫ s, V (Function.update h.2 c.1 s) ∂(E.step c.2 (h.2 c.1)) ∂(π.select t h)
        ∂(sfasMeasure E π z0 t) :=
  p2ma2_step E π z0 t (fun h ↦ V h.2) BV (fun h ↦ hV _)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_Q_bd {X U : Type*} [MeasurableSpace X] (E : DecisionProcess X U) (a : ℝ)
    (ha0 : 0 ≤ a) (M : ℝ) (hM : ∀ y u, |E.reward y u| ≤ M) (V : (Fin 2 → X) → ℝ) (BV : ℝ)
    (hV : ∀ z, |V z| ≤ BV) (z : Fin 2 → X) (c : Fin 2 × U) :
    |p2ma2_Q E a V z c| ≤ M + a * BV := by
  unfold p2ma2_Q
  have h1 := p2ma2_abs_int_le (E.step c.2 (z c.1)) (fun s ↦ V (Function.update z c.1 s)) BV
    (fun s ↦ hV _)
  calc _ ≤ |E.reward (z c.1) c.2| +
        |a * ∫ s, V (Function.update z c.1 s) ∂(E.step c.2 (z c.1))| := abs_add_le _ _
    _ ≤ M + a * BV := by
        rw [abs_mul, abs_of_nonneg ha0]
        exact add_le_add (hM _ _) (mul_le_mul_of_nonneg_left h1 ha0)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_comb {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (a : ℝ) (M : ℝ) (hM : ∀ y u, |E.reward y u| ≤ M)
    (V : (Fin 2 → X) → ℝ) (BV : ℝ) (hV : ∀ z, |V z| ≤ BV) (π : SFASPolicy 2 X U)
    (z0 : Fin 2 → X) (t : ℕ) :
    sfasRoundReward E π z0 t + a * ∫ h, V h.2 ∂sfasMeasure E π z0 (t + 1) =
      ∫ h, ∫ c, p2ma2_Q E a V h.2 c ∂(π.select t h) ∂(sfasMeasure E π z0 t) := by
  rw [p2ma2_rr E M hM π z0 t, p2ma2_Astep E V BV hV π z0 t]
  have hR : Integrable (fun h : SFASHistory 2 X U t ↦ ∫ c, E.reward (h.2 c.1) c.2
      ∂(π.select t h)) (sfasMeasure E π z0 t) :=
    p2ma2_int_of_bound _ _ (measurable_of_countable _) M
      (fun h ↦ p2ma2_abs_int_le _ _ M (fun c ↦ hM _ _))
  have hG : Integrable (fun h : SFASHistory 2 X U t ↦ ∫ c, ∫ s, V (Function.update h.2 c.1 s)
      ∂(E.step c.2 (h.2 c.1)) ∂(π.select t h)) (sfasMeasure E π z0 t) :=
    p2ma2_int_of_bound _ _ (measurable_of_countable _) BV
      (fun h ↦ p2ma2_abs_int_le _ _ BV (fun c ↦ p2ma2_abs_int_le _ _ BV (fun s ↦ hV _)))
  have e1 := integral_add hR (hG.const_mul a)
  rw [integral_const_mul] at e1
  rw [← e1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
  try dsimp only
  have hR' : Integrable (fun c : Fin 2 × U ↦ E.reward (h.2 c.1) c.2) (π.select t h) :=
    Integrable.of_finite
  have hG' : Integrable (fun c : Fin 2 × U ↦ ∫ s, V (Function.update h.2 c.1 s)
      ∂(E.step c.2 (h.2 c.1))) (π.select t h) := Integrable.of_finite
  have e2 := integral_add hR' (hG'.const_mul a)
  rw [integral_const_mul] at e2
  rw [← e2]
  rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_inner_le {X U : Type*} [MeasurableSpace X] [MeasurableSpace U] [Fintype U]
    [MeasurableSingletonClass U] (E : DecisionProcess X U) (a : ℝ) (V : (Fin 2 → X) → ℝ)
    (hfix : ∀ z, V z = p2ma2_B E a V z) (ν : Measure (Fin 2 × U)) [IsProbabilityMeasure ν]
    (z : Fin 2 → X) (hν : ν {c | c.2 ∈ E.avail (z c.1)} = 1) :
    ∫ c, p2ma2_Q E a V z c ∂ν ≤ V z := by
  have h1 : ν {c | c.2 ∈ E.avail (z c.1)}ᶜ = 0 :=
    (prob_compl_eq_zero_iff MeasurableSet.of_discrete).2 hν
  have hae : ∀ᵐ c ∂ν, c.2 ∈ E.avail (z c.1) := ae_iff.2 h1
  calc ∫ c, p2ma2_Q E a V z c ∂ν ≤ ∫ _c, V z ∂ν :=
        integral_mono_ae Integrable.of_finite (integrable_const _)
          (hae.mono fun c hc ↦ (p2ma2_le_B E a V z c hc).trans_eq (hfix z).symm)
    _ = V z := by rw [integral_const, probReal_univ, one_smul]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_seq_sum (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (rr : ℕ → ℝ) (M : ℝ)
    (hrr : ∀ t, |rr t| ≤ M) : Summable (fun t ↦ a ^ t * rr t) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_left M)
    (fun t ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm]
  exact mul_le_mul_of_nonneg_right (hrr t) (pow_nonneg ha0 t)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_seq_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (rr A : ℕ → ℝ) (M B : ℝ)
    (hrr : ∀ t, |rr t| ≤ M) (hA : ∀ t, |A t| ≤ B)
    (hstep : ∀ t, rr t + a * A (t + 1) ≤ A t) :
    ∑' t, a ^ t * rr t ≤ rr 0 + a * A 1 := by
  have hsum := p2ma2_seq_sum a ha0 ha1 rr M hrr
  have hJ : ∀ k : ℕ, ∑ s ∈ Finset.range (k + 1), a ^ s * rr s + a ^ (k + 1) * A (k + 1) ≤
      rr 0 + a * A 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ]
        have h1 := hstep (k + 1)
        have h2 : 0 ≤ a ^ (k + 1) := pow_nonneg ha0 _
        have h3 : a ^ (k + 1) * (rr (k + 1) + a * A (k + 1 + 1)) ≤ a ^ (k + 1) * A (k + 1) :=
          mul_le_mul_of_nonneg_left h1 h2
        have h4 : a ^ (k + 1 + 1) = a ^ (k + 1) * a := pow_succ a (k + 1)
        rw [h4]
        nlinarith [h3, ih]
  have hlim1 := hsum.hasSum.tendsto_sum_nat
  have hlim2 : Filter.Tendsto (fun t : ℕ ↦ rr 0 + a * A 1 + B * a ^ t) Filter.atTop
      (nhds (rr 0 + a * A 1)) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul B
    simpa using (tendsto_const_nhds (x := rr 0 + a * A 1)).add this
  refine le_of_tendsto_of_tendsto hlim1 hlim2 (Filter.eventually_atTop.2 ⟨1, fun t ht ↦ ?_⟩)
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have h1 := hJ k
  have h2 : -(B * a ^ (k + 1)) ≤ a ^ (k + 1) * A (k + 1) := by
    have hp := pow_nonneg ha0 (k + 1)
    have hA' := (abs_le.1 (hA (k + 1))).1
    nlinarith
  show ∑ s ∈ Finset.range (k + 1), a ^ s * rr s ≤ rr 0 + a * A 1 + B * a ^ (k + 1)
  linarith

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_seq_eq (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (rr A : ℕ → ℝ) (M B : ℝ)
    (hrr : ∀ t, |rr t| ≤ M) (hA : ∀ t, |A t| ≤ B)
    (hstep : ∀ t, rr t + a * A (t + 1) = A t) :
    ∑' t, a ^ t * rr t = A 0 := by
  have hsum := p2ma2_seq_sum a ha0 ha1 rr M hrr
  have hJ : ∀ k : ℕ, ∑ s ∈ Finset.range k, a ^ s * rr s = A 0 - a ^ k * A k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih, pow_succ, ← hstep k]
        ring
  have hlim1 := hsum.hasSum.tendsto_sum_nat
  have h0 : Filter.Tendsto (fun k : ℕ ↦ a ^ k * A k) Filter.atTop (nhds 0) := by
    have hB : Filter.Tendsto (fun k : ℕ ↦ a ^ k * B) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const B
    refine squeeze_zero_norm (fun k ↦ ?_) hB
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (hA k) (pow_nonneg ha0 k)
  have hlim2 : Filter.Tendsto (fun k : ℕ ↦ A 0 - a ^ k * A k) Filter.atTop (nhds (A 0)) := by
    simpa using (tendsto_const_nhds (x := A 0)).sub h0
  exact tendsto_nhds_unique (hlim1.congr hJ) hlim2

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_val_le {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (M : ℝ)
    (hM : ∀ y u, |E.reward y u| ≤ M) (V : (Fin 2 → X) → ℝ) (BV : ℝ)
    (hV : ∀ z, |V z| ≤ BV) (hfix : ∀ z, V z = p2ma2_B E a V z) (π : SFASPolicy 2 X U)
    (hπ : IsFeasiblePolicy E π) (z0 : Fin 2 → X) :
    sfasValue E a π z0 ≤ ∫ c, p2ma2_Q E a V z0 c ∂(π.select 0 (fun i ↦ i.elim0, z0)) := by
  have hstep : ∀ t, sfasRoundReward E π z0 t + a * ∫ h, V h.2 ∂sfasMeasure E π z0 (t + 1) ≤
      ∫ h, V h.2 ∂sfasMeasure E π z0 t := by
    intro t
    rw [p2ma2_comb E a M hM V BV hV π z0 t]
    exact integral_mono (p2ma2_int_of_bound _ _ (measurable_of_countable _) (M + a * BV)
      (fun h ↦ p2ma2_abs_int_le _ _ _ (fun c ↦ p2ma2_Q_bd E a ha0 M hM V BV hV _ _)))
      (p2ma2_int_of_bound _ _ (measurable_of_countable _) BV (fun h ↦ hV _))
      (fun h ↦ p2ma2_inner_le E a V hfix (π.select t h) h.2 (hπ t h))
  have h1 := p2ma2_seq_le a ha0 ha1 (fun t ↦ sfasRoundReward E π z0 t)
    (fun t ↦ ∫ h, V h.2 ∂sfasMeasure E π z0 t) M BV
    (fun t ↦ p2ma2_abs_int_le _ _ M (fun h ↦ hM _ _))
    (fun t ↦ p2ma2_abs_int_le _ _ BV (fun h ↦ hV _)) hstep
  unfold sfasValue
  refine h1.trans (le_of_eq ?_)
  have hc := p2ma2_comb E a M hM V BV hV π z0 0
  rw [zero_add] at hc
  rw [hc, sfasMeasure.eq_1, integral_dirac]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private noncomputable def p2ma2_pol {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (f : (Fin 2 → X) → Fin 2 × U) : SFASPolicy 2 X U where
  select t := Kernel.deterministic (fun h : SFASHistory 2 X U t ↦ f h.2)
    (measurable_of_countable _)
  markov _ := inferInstance

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_pol_apply {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (f : (Fin 2 → X) → Fin 2 × U) (t : ℕ) (h : SFASHistory 2 X U t) :
    (p2ma2_pol f).select t h = Measure.dirac (f h.2) :=
  Kernel.deterministic_apply (f := fun h : SFASHistory 2 X U t ↦ f h.2)
    (measurable_of_countable _) h

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_pol_feas {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (f : (Fin 2 → X) → Fin 2 × U)
    (hf : ∀ z, (f z).2 ∈ E.avail (z (f z).1)) : IsFeasiblePolicy E (p2ma2_pol f) := by
  intro t h
  rw [p2ma2_pol_apply]
  exact Measure.dirac_apply_of_mem (hf h.2)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_pol_val {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (M : ℝ)
    (hM : ∀ y u, |E.reward y u| ≤ M) (V : (Fin 2 → X) → ℝ) (BV : ℝ)
    (hV : ∀ z, |V z| ≤ BV) (f : (Fin 2 → X) → Fin 2 × U)
    (hfQ : ∀ z, p2ma2_Q E a V z (f z) = V z) (z0 : Fin 2 → X) :
    sfasValue E a (p2ma2_pol f) z0 = V z0 := by
  have hstep : ∀ t, sfasRoundReward E (p2ma2_pol f) z0 t +
      a * ∫ h, V h.2 ∂sfasMeasure E (p2ma2_pol f) z0 (t + 1) =
      ∫ h, V h.2 ∂sfasMeasure E (p2ma2_pol f) z0 t := by
    intro t
    rw [p2ma2_comb E a M hM V BV hV (p2ma2_pol f) z0 t]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h ↦ ?_)
    show ∫ c, p2ma2_Q E a V h.2 c ∂((p2ma2_pol f).select t h) = V h.2
    rw [p2ma2_pol_apply, integral_dirac]
    exact hfQ h.2
  have h1 := p2ma2_seq_eq a ha0 ha1 (fun t ↦ sfasRoundReward E (p2ma2_pol f) z0 t)
    (fun t ↦ ∫ h, V h.2 ∂sfasMeasure E (p2ma2_pol f) z0 t) M BV
    (fun t ↦ p2ma2_abs_int_le _ _ M (fun h ↦ hM _ _))
    (fun t ↦ p2ma2_abs_int_le _ _ BV (fun h ↦ hV _)) hstep
  unfold sfasValue
  rw [h1, sfasMeasure.eq_1, integral_dirac]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_greedyF {X U : Type*} [MeasurableSpace X] (E : DecisionProcess X U)
    (a : ℝ) (V : (Fin 2 → X) → ℝ) (hfix : ∀ z, V z = p2ma2_B E a V z) :
    ∃ f : (Fin 2 → X) → Fin 2 × U, (∀ z, (f z).2 ∈ E.avail (z (f z).1)) ∧
      ∀ z, p2ma2_Q E a V z (f z) = V z := by
  have hex : ∀ z, ∃ c : Fin 2 × U, c.2 ∈ E.avail (z c.1) ∧ p2ma2_Q E a V z c = V z := by
    intro z
    obtain ⟨c, hc, hB⟩ := p2ma2_ex_B E a V z
    exact ⟨c, hc, by rw [← hB, ← hfix z]⟩
  choose f hf hfQ using hex
  exact ⟨f, hf, hfQ⟩

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_sup {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (M : ℝ)
    (hM : ∀ y u, |E.reward y u| ≤ M) (V : (Fin 2 → X) → ℝ) (BV : ℝ)
    (hV : ∀ z, |V z| ≤ BV) (hfix : ∀ z, V z = p2ma2_B E a V z) (z : Fin 2 → X) :
    (⨆ π' : {π' : SFASPolicy 2 X U // IsFeasiblePolicy E π'}, sfasValue E a π'.1 z) = V z := by
  obtain ⟨f, hf, hfQ⟩ := p2ma2_greedyF E a V hfix
  have hle : ∀ π' : {π' : SFASPolicy 2 X U // IsFeasiblePolicy E π'},
      sfasValue E a π'.1 z ≤ V z := fun π' ↦
    (p2ma2_val_le E a ha0 ha1 M hM V BV hV hfix π'.1 π'.2 z).trans
      (p2ma2_inner_le E a V hfix (π'.1.select 0 (fun i ↦ i.elim0, z)) z
        (π'.2 0 (fun i ↦ i.elim0, z)))
  haveI : Nonempty {π' : SFASPolicy 2 X U // IsFeasiblePolicy E π'} :=
    ⟨⟨p2ma2_pol f, p2ma2_pol_feas E f hf⟩⟩
  refine le_antisymm (ciSup_le hle) ?_
  rw [← p2ma2_pol_val E a ha0 ha1 M hM V BV hV f hfQ z]
  exact le_ciSup (f := fun π' : {π' : SFASPolicy 2 X U // IsFeasiblePolicy E π'} ↦
      sfasValue E a π'.1 z) ⟨V z, by rintro _ ⟨π', rfl⟩; exact hle π'⟩
    ⟨p2ma2_pol f, p2ma2_pol_feas E f hf⟩

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_mkopt {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (M : ℝ)
    (hM : ∀ y u, |E.reward y u| ≤ M) (V : (Fin 2 → X) → ℝ) (BV : ℝ)
    (hV : ∀ z, |V z| ≤ BV) (hfix : ∀ z, V z = p2ma2_B E a V z) (z0 : Fin 2 → X)
    (c0 : Fin 2 × U) (hc0 : c0.2 ∈ E.avail (z0 c0.1)) (hQ : p2ma2_Q E a V z0 c0 = V z0) :
    ∃ π : SFASPolicy 2 X U, IsOptimalSFASPolicy E a π ∧
      π.select 0 (fun i ↦ i.elim0, z0) = Measure.dirac c0 := by
  classical
  obtain ⟨g, hg, hgQ⟩ := p2ma2_greedyF E a V hfix
  have hf : ∀ z, (Function.update g z0 c0 z).2 ∈ E.avail (z (Function.update g z0 c0 z).1) := by
    intro z
    by_cases h : z = z0
    · rw [h, Function.update_self]; exact hc0
    · rw [Function.update_of_ne h]; exact hg z
  have hfQ : ∀ z, p2ma2_Q E a V z (Function.update g z0 c0 z) = V z := by
    intro z
    by_cases h : z = z0
    · rw [h, Function.update_self]; exact hQ
    · rw [Function.update_of_ne h]; exact hgQ z
  refine ⟨p2ma2_pol (Function.update g z0 c0),
    ⟨p2ma2_pol_feas E _ hf, fun z ↦ ?_⟩, ?_⟩
  · rw [p2ma2_pol_val E a ha0 ha1 M hM V BV hV _ hfQ z,
      p2ma2_sup E a ha0 ha1 M hM V BV hV hfix z]
  · rw [p2ma2_pol_apply]
    show Measure.dirac (Function.update g z0 c0 z0) = _
    rw [Function.update_self]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_opt_val {X U : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]
    (E : DecisionProcess X U) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (M : ℝ)
    (hM : ∀ y u, |E.reward y u| ≤ M) (V : (Fin 2 → X) → ℝ) (BV : ℝ)
    (hV : ∀ z, |V z| ≤ BV) (hfix : ∀ z, V z = p2ma2_B E a V z) (π : SFASPolicy 2 X U)
    (hopt : IsOptimalSFASPolicy E a π) (z : Fin 2 → X) : sfasValue E a π z = V z :=
  (hopt.2 z).trans (p2ma2_sup E a ha0 ha1 M hM V BV hV hfix z)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_upd0 {S : Type*} (y : S) (s : S ⊕ Unit) :
    Function.update (![Sum.inl y, Sum.inr ()] : Fin 2 → S ⊕ Unit) 0 s = ![s, Sum.inr ()] := by
  funext i; fin_cases i <;> simp

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_upd1 {S : Type*} (y : S) :
    Function.update (![Sum.inl y, Sum.inr ()] : Fin 2 → S ⊕ Unit) 1 (Sum.inr ()) =
      ![Sum.inl y, Sum.inr ()] := by
  funext i; fin_cases i <;> simp

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_Q_ws0 {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MeasurableSpace U] [Fintype U] [Nonempty U]
    [MeasurableSingletonClass U] [DiscreteMeasurableSpace (S ⊕ Unit)]
    (D : DecisionProcess S U) (lam a : ℝ) (V : (Fin 2 → S ⊕ Unit) → ℝ) (y : S) (u : U) :
    p2ma2_Q (withStandard D lam) a V ![Sum.inl y, Sum.inr ()] (0, u) =
      D.reward y u + a * ∫ s, V ![Sum.inl s, Sum.inr ()] ∂(D.step u y) := by
  have hstep : (withStandard D lam).step u (Sum.inl y) = (D.step u y).map Sum.inl := by
    show ((D.step u).map Sum.inl) y = _
    exact Kernel.map_apply _ measurable_inl _
  show D.reward y u + a * ∫ s, V (Function.update ![Sum.inl y, Sum.inr ()] 0 s)
      ∂((withStandard D lam).step u (Sum.inl y)) = _
  rw [hstep, integral_map measurable_inl.aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  simp only [p2ma2_upd0]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_Q_ws1 {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MeasurableSpace U] [Fintype U] [Nonempty U]
    [MeasurableSingletonClass U] [DiscreteMeasurableSpace (S ⊕ Unit)]
    (D : DecisionProcess S U) (lam a : ℝ) (V : (Fin 2 → S ⊕ Unit) → ℝ) (y : S) (u : U) :
    p2ma2_Q (withStandard D lam) a V ![Sum.inl y, Sum.inr ()] (1, u) =
      lam + a * V ![Sum.inl y, Sum.inr ()] := by
  have hstep : (withStandard D lam).step u (Sum.inr ()) = Measure.dirac (Sum.inr ()) := by
    show ((Kernel.const Unit (Measure.dirac ())).map Sum.inr) () = _
    rw [Kernel.map_apply _ measurable_inr, Kernel.const_apply, Measure.map_dirac' measurable_inr]
  show lam + a * ∫ s, V (Function.update ![Sum.inl y, Sum.inr ()] 1 s)
      ∂((withStandard D lam).step u (Sum.inr ())) = _
  rw [hstep, integral_dirac, p2ma2_upd1]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private noncomputable def p2ma2_Qu {S U : Type*} [MeasurableSpace S] (D : DecisionProcess S U)
    (a lam : ℝ) (W : S → ℝ) (u : U) (y : S) : ℝ :=
  D.reward y u - lam + a * ∫ s, W s ∂(D.step u y)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2ma2_pkg {S U : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] [MeasurableSpace U] [Fintype U] [Nonempty U]
    [MeasurableSingletonClass U] (D : DecisionProcess S U) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y u, |D.reward y u| ≤ M) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (lam : ℝ) (x : S) :
    ∃ W : S → ℝ, (∃ BW : ℝ, ∀ y, |W y| ≤ BW) ∧ (∀ y, 0 ≤ W y) ∧
      (∀ y, ∀ u ∈ D.avail y, p2ma2_Qu D a lam W u y ≤ W y) ∧
      (∀ y, W y = 0 ∨ ∃ u ∈ D.avail y, W y = p2ma2_Qu D a lam W u y) ∧
      (∀ u ∈ D.avail x, OptimalToApply D a lam x u ↔ p2ma2_Qu D a lam W u x = W x) ∧
      (OptimalToSelect D a lam x ↔ ∃ u ∈ D.avail x, p2ma2_Qu D a lam W u x = W x) := by
  haveI : DiscreteMeasurableSpace (S ⊕ Unit) :=
    ⟨fun s ↦ ⟨(MeasurableSet.of_discrete : MeasurableSet (Sum.inl ⁻¹' s : Set S)),
      (MeasurableSet.of_discrete : MeasurableSet (Sum.inr ⁻¹' s : Set Unit))⟩⟩
  have h1a : 0 < 1 - a := by linarith
  have hME : ∀ y u, |(withStandard D lam).reward y u| ≤ M + |lam| := by
    rintro (y | y) u
    · exact (hM y u).trans (le_add_of_nonneg_right (abs_nonneg _))
    · exact le_add_of_nonneg_left hM0
  obtain ⟨V, hVb, hfix⟩ := p2ma2_Vstar (withStandard D lam) a (M + |lam|) ha0.le ha1
    (add_nonneg hM0 (abs_nonneg _)) hME
  obtain ⟨BV, hBV⟩ : ∃ BV : ℝ, BV = (M + |lam|) / (1 - a) := ⟨_, rfl⟩
  rw [← hBV] at hVb
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = lam / (1 - a) := ⟨_, rfl⟩
  have hLeq : lam + a * L = L := by rw [hL]; field_simp; ring
  obtain ⟨W, hW⟩ : ∃ W : S → ℝ, ∀ y, W y = V ![Sum.inl y, Sum.inr ()] - L :=
    ⟨fun y ↦ V ![Sum.inl y, Sum.inr ()] - L, fun y ↦ rfl⟩
  have hVW : ∀ y, V ![Sum.inl y, Sum.inr ()] = W y + L := fun y ↦ by rw [hW]; ring
  have hQ0 : ∀ y u, p2ma2_Q (withStandard D lam) a V ![Sum.inl y, Sum.inr ()] (0, u) =
      p2ma2_Qu D a lam W u y + L := by
    intro y u
    rw [p2ma2_Q_ws0]
    have hint : ∫ s, W s ∂(D.step u y) = ∫ s, V ![Sum.inl s, Sum.inr ()] ∂(D.step u y) - L := by
      simp_rw [hW]
      rw [integral_sub (p2ma2_int_of_bound _ _ (measurable_of_countable _) BV (fun s ↦ hVb _))
        (integrable_const L), integral_const, probReal_univ, one_smul]
    unfold p2ma2_Qu
    rw [hint]
    linear_combination hLeq
  have hQ1 : ∀ y u, p2ma2_Q (withStandard D lam) a V ![Sum.inl y, Sum.inr ()] (1, u) =
      lam + a * (W y + L) := by
    intro y u
    rw [p2ma2_Q_ws1, hVW]
  have hF1 : ∀ y, ∀ u ∈ D.avail y, p2ma2_Qu D a lam W u y ≤ W y := by
    intro y u hu
    have := p2ma2_le_B (withStandard D lam) a V ![Sum.inl y, Sum.inr ()] (0, u) hu
    rw [← hfix, hQ0, hVW] at this
    linarith
  have hWa : ∀ y, a * W y ≤ W y := by
    intro y
    have := p2ma2_le_B (withStandard D lam) a V ![Sum.inl y, Sum.inr ()]
      (1, Classical.arbitrary U) (Finset.mem_univ _)
    rw [← hfix, hQ1, hVW] at this
    linarith
  have hF0 : ∀ y, 0 ≤ W y := by
    intro y
    have := hWa y
    nlinarith
  have hF2 : ∀ y, W y = 0 ∨ ∃ u ∈ D.avail y, W y = p2ma2_Qu D a lam W u y := by
    intro y
    obtain ⟨c, hc, hB⟩ := p2ma2_ex_B (withStandard D lam) a V ![Sum.inl y, Sum.inr ()]
    rw [← hfix, hVW] at hB
    obtain ⟨i, u⟩ := c
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    rcases hi with rfl | rfl
    · right
      refine ⟨u, hc, ?_⟩
      rw [hQ0] at hB
      linarith
    · left
      rw [hQ1] at hB
      have h2 : (1 - a) * W y = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h | h
      · linarith
      · exact h
  have hopt : ∀ π : SFASPolicy 2 (S ⊕ Unit) U, IsOptimalSFASPolicy (withStandard D lam) a π →
      V ![Sum.inl x, Sum.inr ()] ≤ ∫ c, p2ma2_Q (withStandard D lam) a V
        ![Sum.inl x, Sum.inr ()] c ∂(π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])) := by
    intro π hπ
    rw [← p2ma2_opt_val (withStandard D lam) a ha0.le ha1 (M + |lam|) hME V BV hVb hfix π hπ]
    exact p2ma2_val_le (withStandard D lam) a ha0.le ha1 (M + |lam|) hME V BV hVb hfix π hπ.1 _
  refine ⟨W, ⟨BV + |L|, fun y ↦ ?_⟩, hF0, hF1, hF2, fun u hu ↦ ?_, ?_⟩
  · rw [hW, abs_le]
    have h1 := abs_le.1 (hVb ![Sum.inl y, Sum.inr ()])
    constructor <;> linarith [neg_abs_le L, le_abs_self L, h1.1, h1.2]
  · constructor
    · rintro ⟨π, hπ, hsel⟩
      have hle := hopt π hπ
      have hsel' : (π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])) {(0, u)} = 1 := hsel
      have hae : ∀ᵐ c ∂(π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])), c = (0, u) :=
        ae_iff.2 ((prob_compl_eq_zero_iff (measurableSet_singleton _)).2 hsel')
      rw [integral_congr_ae (hae.mono fun c hc ↦ congrArg
        (p2ma2_Q (withStandard D lam) a V ![Sum.inl x, Sum.inr ()]) hc), integral_const,
        probReal_univ, one_smul] at hle
      have hup := p2ma2_le_B (withStandard D lam) a V ![Sum.inl x, Sum.inr ()] (0, u) hu
      rw [← hfix] at hup
      rw [hQ0, hVW] at hle hup
      exact le_antisymm (by linarith) (by linarith)
    · intro hQ
      obtain ⟨π, hπ, hsel⟩ := p2ma2_mkopt (withStandard D lam) a ha0.le ha1 (M + |lam|) hME V
        BV hVb hfix ![Sum.inl x, Sum.inr ()] (0, u) hu (by rw [hQ0, hVW, hQ])
      refine ⟨π, hπ, ?_⟩
      show (π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])) {(0, u)} = 1
      rw [hsel]
      exact Measure.dirac_apply_of_mem rfl
  · constructor
    · rintro ⟨π, hπ, hsel⟩
      have hle := hopt π hπ
      have hsel' : (π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()]))
          {c | c.1 = 0} = 1 := hsel
      have hfe := hπ.1 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])
      have hae1 : ∀ᵐ c ∂(π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])), c.1 = 0 :=
        ae_iff.2 ((prob_compl_eq_zero_iff MeasurableSet.of_discrete).2 hsel')
      have hae2 : ∀ᵐ c ∂(π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])),
          c.2 ∈ (withStandard D lam).avail (![Sum.inl x, Sum.inr ()] c.1) :=
        ae_iff.2 ((prob_compl_eq_zero_iff MeasurableSet.of_discrete).2 hfe)
      obtain ⟨u, hu, hmax⟩ := Finset.exists_mem_eq_sup' (D.avail_nonempty x)
        (fun u ↦ p2ma2_Q (withStandard D lam) a V ![Sum.inl x, Sum.inr ()] (0, u))
      have hbound : ∀ᵐ c ∂(π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])),
          p2ma2_Q (withStandard D lam) a V ![Sum.inl x, Sum.inr ()] c ≤
            p2ma2_Q (withStandard D lam) a V ![Sum.inl x, Sum.inr ()] (0, u) := by
        filter_upwards [hae1, hae2] with c hc1 hc2
        obtain ⟨i, v⟩ := c
        simp only at hc1
        subst hc1
        exact (Finset.le_sup' (fun u ↦ p2ma2_Q (withStandard D lam) a V
          ![Sum.inl x, Sum.inr ()] (0, u)) hc2).trans_eq hmax
      have hle2 := integral_mono_ae Integrable.of_finite (integrable_const _) hbound
      rw [integral_const, probReal_univ, one_smul] at hle2
      have hup := p2ma2_le_B (withStandard D lam) a V ![Sum.inl x, Sum.inr ()] (0, u) hu
      rw [← hfix] at hup
      have hfin := hle.trans hle2
      rw [hQ0, hVW] at hfin hup
      exact ⟨u, hu, le_antisymm (by linarith) (by linarith)⟩
    · rintro ⟨u, hu, hQ⟩
      obtain ⟨π, hπ, hsel⟩ := p2ma2_mkopt (withStandard D lam) a ha0.le ha1 (M + |lam|) hME V
        BV hVb hfix ![Sum.inl x, Sum.inr ()] (0, u) hu (by rw [hQ0, hVW, hQ])
      refine ⟨π, hπ, ?_⟩
      show (π.select 0 (fun i ↦ i.elim0, ![Sum.inl x, Sum.inr ()])) {c | c.1 = 0} = 1
      rw [hsel]
      exact Measure.dirac_apply_of_mem rfl

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m4e_Qt {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P] (r μ : S → ℝ) (a lam : ℝ) (W : S → ℝ) (y : S) :
    p2ma2_Qu (stoppable P r μ) a lam W true y = r y - lam + a * ∫ s, W s ∂(P y) := by
  simp [p2ma2_Qu, stoppable]

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m4e_Qf {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P] (r μ : S → ℝ) (a lam : ℝ) (W : S → ℝ) (y : S) :
    p2ma2_Qu (stoppable P r μ) a lam W false y = μ y - lam + a * W y := by
  simp [p2ma2_Qu, stoppable, Kernel.id_apply, integral_dirac]

private lemma p2m4e_iter {Y : Type*} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (Φ : Y → ℝ)
    (A : Set Y) (K0 : ℝ) (hK0 : 0 ≤ K0) (h0 : ∀ y ∈ A, Φ y ≤ K0)
    (hstep : ∀ K : ℝ, 0 ≤ K → (∀ y ∈ A, Φ y ≤ K) → ∀ y ∈ A, Φ y ≤ a * K) :
    ∀ y ∈ A, Φ y ≤ 0 := by
  have hn : ∀ n : ℕ, ∀ y ∈ A, Φ y ≤ a ^ n * K0 := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have := hstep _ (mul_nonneg (pow_nonneg ha0 n) hK0) ih
      intro y hy
      calc Φ y ≤ a * (a ^ n * K0) := this y hy
        _ = a ^ (n + 1) * K0 := by ring
  intro y hy
  have ht : Filter.Tendsto (fun n : ℕ ↦ a ^ n * K0) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const K0
  exact ge_of_tendsto ht (Filter.Eventually.of_forall fun n ↦ hn n y hy)

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m4e_ae {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P] (μ : S → ℝ)
    (himp : HasImprovingStoppingOption P μ) (y : S) : ∀ᵐ z ∂(P y), μ y ≤ μ z := by
  haveI := p2ma2_prob P y
  have h0 : ∀ᵐ ω ∂(markovChainMeasure P y), ω 0 = y := by
    obtain ⟨F, hF⟩ : ∃ F : S → ℝ, F = ({y}ᶜ : Set S).indicator 1 := ⟨_, rfl⟩
    have hFm : Measurable F := Measurable.of_discrete
    have hint := p2ma2_int0 P y F hFm
    have hFy : F y = 0 := by simp [hF]
    have hFb : ∀ z, 0 ≤ F z ∧ F z ≤ 1 := fun z ↦ by
      rw [hF]; simp only [Set.indicator]; split_ifs <;> simp
    have hnn : 0 ≤ fun ω : ℕ → S ↦ F (ω 0) := fun ω ↦ (hFb _).1
    have hI : Integrable (fun ω : ℕ → S ↦ F (ω 0)) (markovChainMeasure P y) :=
      p2ma2_int_of_bound _ _ (hFm.comp (measurable_pi_apply 0)) 1 (fun ω ↦ by
        rw [abs_le]; constructor <;> linarith [hFb (ω 0)])
    have hz := (integral_eq_zero_iff_of_nonneg hnn hI).1 (by rw [hint, hFy])
    filter_upwards [hz] with ω hω
    by_contra hne
    have : F (ω 0) = 1 := by rw [hF]; simp [hne]
    simp only [Pi.zero_apply] at hω
    rw [this] at hω
    exact one_ne_zero hω
  have hE : ∀ᵐ ω ∂(markovChainMeasure P y), ∀ t, μ (ω t) ≤ μ (ω (t + 1)) := by
    have hset : {ω : ℕ → S | ∀ t, μ (ω t) ≤ μ (ω (t + 1))} =
        ⋂ t : ℕ, {ω : ℕ → S | μ (ω t) ≤ μ (ω (t + 1))} := by
      ext ω; simp
    have hmeas : MeasurableSet {ω : ℕ → S | ∀ t, μ (ω t) ≤ μ (ω (t + 1))} := by
      rw [hset]
      exact MeasurableSet.iInter fun t ↦ measurableSet_le
        ((Measurable.of_discrete : Measurable μ).comp (measurable_pi_apply t))
        ((Measurable.of_discrete : Measurable μ).comp (measurable_pi_apply (t + 1)))
    rw [ae_iff]
    have := measure_compl hmeas (measure_ne_top (markovChainMeasure P y) _)
    rw [himp y, measure_univ, tsub_self] at this
    exact this
  obtain ⟨g, hg⟩ : ∃ g : S → ℝ, g = ({z | μ y ≤ μ z}ᶜ : Set S).indicator 1 := ⟨_, rfl⟩
  have hgb : ∀ z, |g z| ≤ 1 := fun z ↦ by
    rw [hg]; simp only [Set.indicator]; split_ifs <;> simp
  have hmk := p2ma2_markov P y 0 Set.univ MeasurableSet.univ g 1 hgb
  simp only [Set.indicator_univ] at hmk
  rw [p2ma2_int0 P y (fun x ↦ ∫ z, g z ∂P x) Measurable.of_discrete] at hmk
  have hL : ∫ ω, g (ω (0 + 1)) ∂(markovChainMeasure P y) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [h0, hE] with ω h0ω hEω
    have := hEω 0
    rw [h0ω] at this
    rw [hg]
    simp [this]
  rw [hL, hg, integral_indicator_one (MeasurableSet.of_discrete)] at hmk
  rw [ae_iff]
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hmk.symm

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m4e_att {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P] (r μ : S → ℝ) (a : ℝ) (ha0 : 0 ≤ a) (lam : ℝ)
    (W : S → ℝ)
    (hF1 : ∀ y, ∀ u ∈ (stoppable P r μ).avail y, p2ma2_Qu (stoppable P r μ) a lam W u y ≤ W y)
    (hF2 : ∀ y, W y = 0 ∨ ∃ u ∈ (stoppable P r μ).avail y,
      W y = p2ma2_Qu (stoppable P r μ) a lam W u y)
    (y : S) (hy : lam ≤ μ y) : ∃ u : Bool, p2ma2_Qu (stoppable P r μ) a lam W u y = W y := by
  rcases hF2 y with h | ⟨u, -, hu⟩
  · refine ⟨false, le_antisymm (hF1 y false (Finset.mem_univ _)) ?_⟩
    rw [p2m4e_Qf, h]; linarith
  · exact ⟨u, hu.symm⟩

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m4e_shift {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] (r μ : S → ℝ)
    (hcl : ∀ y, ∀ᵐ z ∂(P y), μ y ≤ μ z) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (lam lam' : ℝ) (hll : lam' ≤ lam) (W W' : S → ℝ) (BW BW' : ℝ)
    (hWb : ∀ y, |W y| ≤ BW) (hWb' : ∀ y, |W' y| ≤ BW')
    (hF1 : ∀ y, ∀ u ∈ (stoppable P r μ).avail y, p2ma2_Qu (stoppable P r μ) a lam W u y ≤ W y)
    (hF2 : ∀ y, W y = 0 ∨ ∃ u ∈ (stoppable P r μ).avail y,
      W y = p2ma2_Qu (stoppable P r μ) a lam W u y)
    (hF1' : ∀ y, ∀ u ∈ (stoppable P r μ).avail y,
      p2ma2_Qu (stoppable P r μ) a lam' W' u y ≤ W' y)
    (hF2' : ∀ y, W' y = 0 ∨ ∃ u ∈ (stoppable P r μ).avail y,
      W' y = p2ma2_Qu (stoppable P r μ) a lam' W' u y) :
    ∀ y, lam ≤ μ y → W' y = W y + (lam - lam') / (1 - a) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (lam - lam') / (1 - a) := ⟨_, rfl⟩
  rw [← hc]
  have h1a : 0 < 1 - a := by linarith
  have hcc : (1 - a) * c = lam - lam' := by rw [hc]; field_simp
  have hK0 : ∀ y ∈ {y : S | lam ≤ μ y}, |W' y - W y - c| ≤ |BW'| + |BW| + |c| := fun y _ ↦ by
    have h1 := abs_le.1 (hWb y)
    have h2 := abs_le.1 (hWb' y)
    rw [abs_le]
    constructor <;> linarith [neg_abs_le c, le_abs_self c, le_abs_self BW, le_abs_self BW']
  have hstep : ∀ K : ℝ, 0 ≤ K → (∀ y ∈ {y : S | lam ≤ μ y}, |W' y - W y - c| ≤ K) →
      ∀ y ∈ {y : S | lam ≤ μ y}, |W' y - W y - c| ≤ a * K := by
    intro K hK hA y hy
    have hy' : lam ≤ μ y := hy
    have hint : |∫ z, (W' z - W z - c) ∂(P y)| ≤ K := by
      have := norm_integral_le_of_norm_le_const (μ := P y) (f := fun z ↦ W' z - W z - c)
        (C := K) (by
          filter_upwards [hcl y] with z hz
          rw [Real.norm_eq_abs]
          exact hA z (show lam ≤ μ z from le_trans hy' hz))
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    have hIW : Integrable W (P y) := p2ma2_int_of_bound _ W Measurable.of_discrete BW hWb
    have hIW' : Integrable W' (P y) := p2ma2_int_of_bound _ W' Measurable.of_discrete BW' hWb'
    have hsplit : ∫ z, (W' z - W z - c) ∂(P y) = ∫ z, W' z ∂(P y) - ∫ z, W z ∂(P y) - c := by
      rw [integral_sub (f := fun z ↦ W' z - W z) (g := fun _ ↦ c) (hIW'.sub hIW)
        (integrable_const c), integral_sub hIW' hIW, integral_const, probReal_univ, one_smul]
    obtain ⟨u1, hu1⟩ := p2m4e_att P r μ a ha0 lam W hF1 hF2 y hy'
    obtain ⟨u2, hu2⟩ := p2m4e_att P r μ a ha0 lam' W' hF1' hF2' y (hll.trans hy')
    have hQ : ∀ u : Bool, |p2ma2_Qu (stoppable P r μ) a lam' W' u y -
        p2ma2_Qu (stoppable P r μ) a lam W u y - c| ≤ a * K := by
      intro u
      cases u
      · rw [p2m4e_Qf, p2m4e_Qf]
        have : μ y - lam' + a * W' y - (μ y - lam + a * W y) - c = a * (W' y - W y - c) := by
          linear_combination (-1 : ℝ) * hcc
        rw [this, abs_mul, abs_of_nonneg ha0]
        exact mul_le_mul_of_nonneg_left (hA y hy) ha0
      · rw [p2m4e_Qt, p2m4e_Qt]
        have : r y - lam' + a * ∫ s, W' s ∂(P y) - (r y - lam + a * ∫ s, W s ∂(P y)) - c =
            a * ∫ z, (W' z - W z - c) ∂(P y) := by
          rw [hsplit]
          linear_combination (-1 : ℝ) * hcc
        rw [this, abs_mul, abs_of_nonneg ha0]
        exact mul_le_mul_of_nonneg_left hint ha0
    have e1 := abs_le.1 (hQ u2)
    have e2 := abs_le.1 (hQ u1)
    have f1 := hF1 y u2 (Finset.mem_univ _)
    have f2 := hF1' y u1 (Finset.mem_univ _)
    rw [abs_le]
    constructor <;> linarith
  have hfin := p2m4e_iter a ha0 ha1 (fun y ↦ |W' y - W y - c|) {y : S | lam ≤ μ y} _
    (by positivity) hK0 hstep
  intro y hy
  have := abs_nonpos_iff.1 (hfin y hy)
  linarith

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m4e_equiv {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] (r μ : S → ℝ)
    (hcl : ∀ y, ∀ᵐ z ∂(P y), μ y ≤ μ z) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (lam lam' : ℝ) (hll : lam' ≤ lam) (W W' : S → ℝ) (BW BW' : ℝ)
    (hWb : ∀ y, |W y| ≤ BW) (hWb' : ∀ y, |W' y| ≤ BW')
    (hF1 : ∀ y, ∀ u ∈ (stoppable P r μ).avail y, p2ma2_Qu (stoppable P r μ) a lam W u y ≤ W y)
    (hF2 : ∀ y, W y = 0 ∨ ∃ u ∈ (stoppable P r μ).avail y,
      W y = p2ma2_Qu (stoppable P r μ) a lam W u y)
    (hF1' : ∀ y, ∀ u ∈ (stoppable P r μ).avail y,
      p2ma2_Qu (stoppable P r μ) a lam' W' u y ≤ W' y)
    (hF2' : ∀ y, W' y = 0 ∨ ∃ u ∈ (stoppable P r μ).avail y,
      W' y = p2ma2_Qu (stoppable P r μ) a lam' W' u y)
    (x : S) (hx : lam ≤ μ x) (u : Bool) :
    p2ma2_Qu (stoppable P r μ) a lam' W' u x = W' x ↔
      p2ma2_Qu (stoppable P r μ) a lam W u x = W x := by
  have hsh := p2m4e_shift P r μ hcl a ha0 ha1 lam lam' hll W W' BW BW' hWb hWb' hF1 hF2
    hF1' hF2'
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (lam - lam') / (1 - a) := ⟨_, rfl⟩
  rw [← hc] at hsh
  have h1a : 0 < 1 - a := by linarith
  have hcc : (1 - a) * c = lam - lam' := by rw [hc]; field_simp
  have hQ : p2ma2_Qu (stoppable P r μ) a lam' W' u x =
      p2ma2_Qu (stoppable P r μ) a lam W u x + c := by
    cases u
    · rw [p2m4e_Qf, p2m4e_Qf, hsh x hx]
      linear_combination (-1 : ℝ) * hcc
    · rw [p2m4e_Qt, p2m4e_Qt]
      have hIW : Integrable W (P x) := p2ma2_int_of_bound _ W Measurable.of_discrete BW hWb
      have hae : ∫ s, W' s ∂(P x) = ∫ s, (W s + c) ∂(P x) := by
        refine integral_congr_ae ?_
        filter_upwards [hcl x] with z hz
        exact hsh z (le_trans hx hz)
      rw [hae, integral_add hIW (integrable_const c), integral_const, probReal_univ, one_smul]
      linear_combination (-1 : ℝ) * hcc
  rw [hQ, hsh x hx]
  constructor <;> intro h <;> linarith

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
private lemma p2m4e_mono {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] (r μ : S → ℝ)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (lam lamS : ℝ) (hll : lamS ≤ lam) (W WS : S → ℝ) (BW BWS : ℝ)
    (hWb : ∀ y, |W y| ≤ BW) (hWbS : ∀ y, |WS y| ≤ BWS)
    (hF2 : ∀ y, W y = 0 ∨ ∃ u ∈ (stoppable P r μ).avail y,
      W y = p2ma2_Qu (stoppable P r μ) a lam W u y)
    (hF0S : ∀ y, 0 ≤ WS y)
    (hF1S : ∀ y, ∀ u ∈ (stoppable P r μ).avail y,
      p2ma2_Qu (stoppable P r μ) a lamS WS u y ≤ WS y) :
    ∀ y, W y ≤ WS y := by
  have hK0 : ∀ y ∈ (Set.univ : Set S), W y - WS y ≤ |BW| + |BWS| := fun y _ ↦ by
    have h1 := abs_le.1 (hWb y)
    have h2 := abs_le.1 (hWbS y)
    linarith [le_abs_self BW, le_abs_self BWS]
  have hstep : ∀ K : ℝ, 0 ≤ K → (∀ y ∈ (Set.univ : Set S), W y - WS y ≤ K) →
      ∀ y ∈ (Set.univ : Set S), W y - WS y ≤ a * K := by
    intro K hK hA y _
    rcases hF2 y with h | ⟨u, -, hu⟩
    · rw [h]
      linarith [hF0S y, mul_nonneg ha0 hK]
    · have hIW : Integrable W ((stoppable P r μ).step u y) :=
        p2ma2_int_of_bound _ W Measurable.of_discrete BW hWb
      have hIWS : Integrable WS ((stoppable P r μ).step u y) :=
        p2ma2_int_of_bound _ WS Measurable.of_discrete BWS hWbS
      have hle : ∫ z, W z ∂((stoppable P r μ).step u y) ≤
          ∫ z, WS z ∂((stoppable P r μ).step u y) + K := by
        have := integral_mono (f := W) (g := fun z ↦ WS z + K) hIW
          (hIWS.add (integrable_const K))
          (fun z ↦ (by linarith [hA z (Set.mem_univ _)] : W z ≤ WS z + K))
        rwa [integral_add hIWS (integrable_const K), integral_const, probReal_univ,
          one_smul] at this
      have hS := hF1S y u (Finset.mem_univ _)
      unfold p2ma2_Qu at hu hS
      rw [hu]
      nlinarith [mul_le_mul_of_nonneg_left hle ha0]
  have hfin := p2m4e_iter a ha0 ha1 (fun y ↦ W y - WS y) Set.univ _ (by positivity) hK0 hstep
  intro y
  have := hfin y (Set.mem_univ _)
  linarith

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
theorem solution {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r μ : S → ℝ}
    (hr : BoundedReward r) (hμ : BoundedReward μ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (himp : HasImprovingStoppingOption P μ) :
    ConditionD (stoppable P r μ) a := by
  classical
  obtain ⟨Mr, hMr⟩ := hr
  obtain ⟨Mμ, hMμ⟩ := hμ
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = |Mr| + |Mμ| := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hM : ∀ y u, |(stoppable P r μ).reward y u| ≤ M := by
    intro y u
    cases u
    · have : (stoppable P r μ).reward y false = μ y := by simp [stoppable]
      rw [this, hMdef]
      linarith [hMμ y, le_abs_self Mμ, abs_nonneg Mr]
    · have : (stoppable P r μ).reward y true = r y := by simp [stoppable]
      rw [this, hMdef]
      linarith [hMr y, le_abs_self Mr, abs_nonneg Mμ]
  have hcl := p2m4e_ae P μ himp
  obtain ⟨lam0, hl0⟩ : ∃ lam0 : ℝ, lam0 = -M - 1 := ⟨_, rfl⟩
  have hlam0 : ∀ y, lam0 ≤ μ y := fun y ↦ by
    have := abs_le.1 (hMμ y)
    rw [hl0, hMdef]
    linarith [le_abs_self Mμ, abs_nonneg Mr]
  have hpk := fun x : S ↦ p2ma2_pkg (stoppable P r μ) M hM0 hM a ha0 ha1 lam0 x
  choose W0 hW0 using hpk
  obtain ⟨g, hg⟩ : ∃ g : S → Bool, ∀ x, g x =
      decide (p2ma2_Qu (stoppable P r μ) a lam0 (W0 x) true x = W0 x x) := ⟨_, fun _ ↦ rfl⟩
  refine ⟨g, fun _ ↦ Finset.mem_univ _, fun x lam hsel ↦ ?_⟩
  obtain ⟨W, ⟨BW, hWb⟩, hF0, hF1, hF2, happ, hselq⟩ :=
    p2ma2_pkg (stoppable P r μ) M hM0 hM a ha0 ha1 lam x
  rw [happ (g x) (Finset.mem_univ _)]
  rw [hselq] at hsel
  obtain ⟨u, -, hu⟩ := hsel
  obtain ⟨⟨B0, hB0⟩, h0F0, h0F1, h0F2, -, -⟩ := hW0 x
  by_cases hx : lam ≤ μ x
  · have key : ∀ v : Bool, (p2ma2_Qu (stoppable P r μ) a lam W v x = W x ↔
        p2ma2_Qu (stoppable P r μ) a lam0 (W0 x) v x = W0 x x) := by
      rcases le_total lam0 lam with h | h
      · intro v
        exact (p2m4e_equiv P r μ hcl a ha0.le ha1 lam lam0 h W (W0 x) BW B0 hWb hB0 hF1 hF2
          h0F1 h0F2 x hx v).symm
      · intro v
        exact p2m4e_equiv P r μ hcl a ha0.le ha1 lam0 lam h (W0 x) W B0 BW hB0 hWb h0F1 h0F2
          hF1 hF2 x (hlam0 x) v
    rw [key]
    cases hgx : g x
    · have hne : p2ma2_Qu (stoppable P r μ) a lam0 (W0 x) true x ≠ W0 x x := by
        intro heq
        rw [hg x, decide_eq_true heq] at hgx
        exact Bool.noConfusion hgx
      obtain ⟨v, hv⟩ := p2m4e_att P r μ a ha0.le lam0 (W0 x) h0F1 h0F2 x (hlam0 x)
      cases v
      · exact hv
      · exact absurd hv hne
    · rw [hg x] at hgx
      exact of_decide_eq_true hgx
  · replace hx := not_le.1 hx
    have huT : u = true := by
      cases u
      · exfalso
        rw [p2m4e_Qf] at hu
        have := hF0 x
        nlinarith
      · rfl
    subst huT
    cases hgx : g x
    · exfalso
      have hne : p2ma2_Qu (stoppable P r μ) a lam0 (W0 x) true x ≠ W0 x x := by
        intro heq
        rw [hg x, decide_eq_true heq] at hgx
        exact Bool.noConfusion hgx
      obtain ⟨WS, ⟨BWS, hWbS⟩, hF0S, hF1S, hF2S, -, -⟩ :=
        p2ma2_pkg (stoppable P r μ) M hM0 hM a ha0 ha1 (μ x) x
      have hneS : p2ma2_Qu (stoppable P r μ) a (μ x) WS true x ≠ WS x := by
        intro heq
        exact hne ((p2m4e_equiv P r μ hcl a ha0.le ha1 (μ x) lam0 (hlam0 x) WS (W0 x) BWS B0
          hWbS hB0 hF1S hF2S h0F1 h0F2 x le_rfl true).2 heq)
      have hWS0 : WS x = 0 := by
        rcases hF2S x with h | ⟨v, -, hv⟩
        · exact h
        · cases v
          · rw [p2m4e_Qf] at hv
            nlinarith [hF0S x]
          · exact absurd hv.symm hneS
      have hQS : p2ma2_Qu (stoppable P r μ) a (μ x) WS true x < 0 := by
        have := hF1S x true (Finset.mem_univ _)
        rw [hWS0] at this hneS
        exact lt_of_le_of_ne this hneS
      have hmono := p2m4e_mono P r μ a ha0.le ha1 lam (μ x) hx.le W WS BW BWS hWb hWbS hF2
        hF0S hF1S
      have hIW : Integrable W (P x) := p2ma2_int_of_bound _ W Measurable.of_discrete BW hWb
      have hIWS : Integrable WS (P x) := p2ma2_int_of_bound _ WS Measurable.of_discrete BWS hWbS
      have hint : ∫ s, W s ∂(P x) ≤ ∫ s, WS s ∂(P x) := integral_mono hIW hIWS hmono
      rw [p2m4e_Qt] at hu hQS
      have := hF0 x
      nlinarith [mul_le_mul_of_nonneg_left hint ha0.le]
    · exact hu
