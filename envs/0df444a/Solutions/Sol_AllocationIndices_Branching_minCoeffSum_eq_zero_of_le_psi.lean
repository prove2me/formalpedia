-- Prove2me | solution 1 for AllocationIndices.Branching.minCoeffSum_eq_zero_of_le_psi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:52:14.988134+00:00
-- url     : https://prove2.me/submissions/35b362f9-5155-4048-84ab-2d5eeefccf1d

import Definitions.Def_AllocationIndices_Branching_Parallel

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset
open AllocationIndices AllocationIndices.Branching

section G69AI
variable {N : ℕ}

lemma g69ai_lt_hit (S : Set (Fin (N + 1))) (ω : ℕ → Fin (N + 1)) (t : ℕ) :
    (t : ℕ∞) < hittingTime S ω ↔ ∀ s, 1 ≤ s → s ≤ t → ω s ∉ S := by
  unfold hittingTime
  rw [← ENat.add_one_le_iff (ENat.natCast_ne_top t), le_iInf_iff]
  constructor
  · intro h s hs1 hst hS
    have := h ⟨s, hs1, hS⟩
    simp only at this
    have : ((t + 1 : ℕ) : ℕ∞) ≤ (s : ℕ∞) := by exact_mod_cast this
    have := Nat.cast_le.mp this
    omega
  · rintro h ⟨s, hs1, hS⟩
    simp only
    have : t + 1 ≤ s := by
      by_contra hc; exact h s hs1 (by omega) hS
    exact_mod_cast this

lemma g69ai_meas_set (S : Set (Fin (N + 1))) (t : ℕ) :
    MeasurableSet {ω : ℕ → Fin (N + 1) | (t : ℕ∞) < hittingTime S ω} := by
  have : {ω : ℕ → Fin (N + 1) | (t : ℕ∞) < hittingTime S ω} =
      ⋂ s ∈ Finset.range (t + 1), {ω | 1 ≤ s → ω s ∉ S} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, g69ai_lt_hit]
    constructor
    · intro h s hs h1; exact h s h1 (by omega)
    · intro h s h1 hs; exact h s (by omega) h1
  rw [this]
  refine Finset.measurableSet_biInter _ fun s _ => ?_
  by_cases h1 : 1 ≤ s
  · simp only [h1, true_implies]
    have hm : Measurable (fun ω : ℕ → Fin (N + 1) => ω s) := measurable_pi_apply s
    exact hm (MeasurableSet.of_discrete (s := Sᶜ))
  · simp [h1]


lemma g69ai_term_le (S : Set (Fin (N + 1))) {a : ℝ} (ha0 : 0 < a) (ω : ℕ → Fin (N + 1)) (t : ℕ) :
    0 ≤ (if (t : ℕ∞) < hittingTime S ω then a ^ t * (fun _ => (1:ℝ)) (ω t) else 0) ∧
    (if (t : ℕ∞) < hittingTime S ω then a ^ t * (fun _ => (1:ℝ)) (ω t) else 0) ≤ a ^ t := by
  split_ifs <;> simp [pow_nonneg ha0.le]

lemma g69ai_summ (S : Set (Fin (N + 1))) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ω : ℕ → Fin (N + 1)) :
    Summable (fun t : ℕ => if (t : ℕ∞) < hittingTime S ω then a ^ t * (fun _ => (1:ℝ)) (ω t) else 0) :=
  Summable.of_nonneg_of_le (fun t => (g69ai_term_le S ha0 ω t).1) (fun t => (g69ai_term_le S ha0 ω t).2)
    (summable_geometric_of_lt_one ha0.le ha1)

lemma g69ai_ge_one (S : Set (Fin (N + 1))) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ω : ℕ → Fin (N + 1)) :
    1 ≤ discountedStoppedSum a (fun _ => (1:ℝ)) (hittingTime S) ω := by
  unfold discountedStoppedSum
  have h0 : (if ((0:ℕ) : ℕ∞) < hittingTime S ω then a ^ 0 * (fun _ => (1:ℝ)) (ω 0) else 0) = 1 := by
    rw [if_pos ((g69ai_lt_hit S ω 0).2 (fun s h1 h2 => by omega))]; simp
  have := (g69ai_summ S ha0 ha1 ω).le_tsum 0 (fun t _ => (g69ai_term_le S ha0 ω t).1)
  rw [h0] at this; exact this

lemma g69ai_le (S : Set (Fin (N + 1))) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ω : ℕ → Fin (N + 1)) :
    discountedStoppedSum a (fun _ => (1:ℝ)) (hittingTime S) ω ≤ (1 - a)⁻¹ := by
  unfold discountedStoppedSum
  rw [← tsum_geometric_of_lt_one ha0.le ha1]
  exact (g69ai_summ S ha0 ha1 ω).tsum_le_tsum (fun t => (g69ai_term_le S ha0 ω t).2)
    (summable_geometric_of_lt_one ha0.le ha1)

lemma g69ai_meas (S : Set (Fin (N + 1))) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Measurable (discountedStoppedSum a (fun _ => (1:ℝ)) (hittingTime S)) := by
  have hterm : ∀ t : ℕ, Measurable (fun ω : ℕ → Fin (N + 1) =>
      if (t : ℕ∞) < hittingTime S ω then a ^ t * (fun _ => (1:ℝ)) (ω t) else 0) := by
    intro t
    have : (fun ω : ℕ → Fin (N + 1) =>
        if (t : ℕ∞) < hittingTime S ω then a ^ t * (fun _ => (1:ℝ)) (ω t) else 0) =
        Set.indicator {ω | (t : ℕ∞) < hittingTime S ω} (fun _ => a ^ t) := by
      ext ω; simp [Set.indicator]
    rw [this]; exact measurable_const.indicator (g69ai_meas_set S t)
  refine measurable_of_tendsto_metrizable (f := fun n ω => ∑ t ∈ Finset.range n,
      (if (t : ℕ∞) < hittingTime S ω then a ^ t * (fun _ => (1:ℝ)) (ω t) else 0))
    (fun n => Finset.measurable_sum _ fun t _ => hterm t) ?_
  exact tendsto_pi_nhds.2 fun ω => (g69ai_summ S ha0 ha1 ω).hasSum.tendsto_sum_nat

instance g69ai_prob (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] (x : Fin (N + 1)) :
    IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure; infer_instance

lemma g69ai_A_ge (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (S : Finset (Fin (N + 1))) (j : Fin (N + 1)) (hj : j ∈ S) :
    1 ≤ conservationCoeff P a S j := by
  unfold conservationCoeff stoppedTime
  rw [if_pos hj]
  have hint : Integrable (discountedStoppedSum a (fun _ => (1:ℝ)) (hittingTime (↑S : Set (Fin (N + 1)))))
      (markovChainMeasure P j) := by
    refine Integrable.of_bound (C := (1 - a)⁻¹) (g69ai_meas _ ha0 ha1).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (g69ai_ge_one _ ha0 ha1 ω))]
    exact g69ai_le _ ha0 ha1 ω
  calc (1:ℝ) = ∫ _ω, (1:ℝ) ∂markovChainMeasure P j := by simp
    _ ≤ _ := integral_mono (integrable_const 1) hint (fun ω => g69ai_ge_one _ ha0 ha1 ω)

lemma g69ai_A_univ (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] {a : ℝ}
    (j : Fin (N + 1)) : conservationCoeff P a Finset.univ j = 1 := by
  unfold conservationCoeff stoppedTime
  rw [if_pos (Finset.mem_univ j)]
  have : ∀ ω : ℕ → Fin (N + 1),
      discountedStoppedSum a (fun _ => (1:ℝ)) (hittingTime (↑(Finset.univ : Finset (Fin (N + 1))))) ω = 1 := by
    intro ω
    unfold discountedStoppedSum
    have e : ∀ t : ℕ, (if (t : ℕ∞) < hittingTime (↑(Finset.univ : Finset (Fin (N + 1)))) ω
        then a ^ t * (fun _ => (1:ℝ)) (ω t) else 0) = if t = 0 then 1 else 0 := by
      intro t
      by_cases ht : t = 0
      · subst ht; rw [if_pos ((g69ai_lt_hit _ ω 0).2 (fun s h1 h2 => by omega))]; simp
      · rw [if_neg, if_neg ht]
        rw [g69ai_lt_hit]; push Not
        exact ⟨1, le_rfl, by omega, by simp⟩
    simp_rw [e]; exact tsum_ite_eq 0 1
  simp_rw [this]; simp

end G69AI



section G69AM
variable {N n M : ℕ}

instance g69am_step_markov (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (t : ℕ) : IsMarkovKernel (parallelStepKernel P π t) := by
  unfold parallelStepKernel; infer_instance

instance g69am_prob (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (k : Fin n → Fin (N + 1)) (t : ℕ) :
    IsProbabilityMeasure (parallelMeasure P π k t) := by
  induction t with
  | zero => simp only [parallelMeasure]; infer_instance
  | succ t ih =>
    simp only [parallelMeasure]
    exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

lemma g69am_sel (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (k : Fin n → Fin (N + 1)) (t : ℕ) :
    ∫ h, (selCount (h.1 (Fin.last t)).2 : ℝ) ∂parallelMeasure P π k (t + 1) = M := by
  simp only [parallelMeasure]
  rw [integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  simp only [Fin.snoc_last]
  rw [Measure.integral_compProd (Integrable.of_finite)]
  have : ∀ h : ParallelHistory n N t, ∫ z, (selCount z.1 : ℝ) ∂(parallelStepKernel P π t h) = M := by
    intro h
    unfold parallelStepKernel
    rw [ProbabilityTheory.integral_compProd (Integrable.of_finite)]
    have hae : ∀ᵐ s ∂(π.select t h), (selCount s : ℝ) = M := by
      have h1 := π.card_eq t h
      rw [ae_iff]
      have : {s : Fin n → Bool | ¬ (selCount s : ℝ) = M} = {s : Fin n → Bool | selCount s = M}ᶜ := by
        ext s; simp
      rw [this, prob_compl_eq_zero_iff (Set.Finite.measurableSet (Set.toFinite _))]
      exact h1
    calc ∫ s, ∫ _z, (selCount s : ℝ) ∂_ ∂(π.select t h) = ∫ s, (selCount s : ℝ) ∂(π.select t h) := by
          congr 1; ext s; simp
      _ = ∫ _s, (M : ℝ) ∂(π.select t h) := integral_congr_ae hae
      _ = M := by simp
  simp_rw [this]; simp


lemma g69am_occ_bd (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (k : Fin n → Fin (N + 1)) (i : Fin (N + 1)) (t : ℕ) :
    0 ≤ parallelOccupation P π k i t ∧ parallelOccupation P π k i t ≤ n := by
  unfold parallelOccupation
  constructor
  · exact integral_nonneg fun h => Nat.cast_nonneg _
  · calc _ ≤ ∫ _h, (n : ℝ) ∂parallelMeasure P π k (t + 1) :=
          integral_mono Integrable.of_finite (integrable_const _) (fun h => by
            simp only
            exact_mod_cast (Finset.card_filter_le _ _).trans (by simp))
      _ = n := by simp

lemma g69am_occ_sum (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (k : Fin n → Fin (N + 1)) (t : ℕ) :
    ∑ i, parallelOccupation P π k i t = M := by
  unfold parallelOccupation
  rw [← integral_finset_sum _ (fun i _ => Integrable.of_finite)]
  rw [← g69am_sel P π k t]
  congr 1; ext h
  rw [← Nat.cast_sum]
  congr 1
  unfold selCount
  rw [Finset.card_eq_sum_card_fiberwise (f := fun b => (h.1 (Fin.last t)).1 b) (t := univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.filter_filter]

lemma g69am_perf_sum (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (k : Fin n → Fin (N + 1)) :
    ∑ i, parallelPerformance P π a k i = M / (1 - a) := by
  unfold parallelPerformance
  have hs : ∀ i ∈ (univ : Finset (Fin (N + 1))),
      Summable (fun t : ℕ => a ^ t * parallelOccupation P π k i t) := by
    intro i _
    refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg ha₀.le _) (g69am_occ_bd P π k i t).1)
      (fun t => ?_) ((summable_geometric_of_lt_one ha₀.le ha₁).mul_right (n : ℝ))
    exact mul_le_mul_of_nonneg_left (g69am_occ_bd P π k i t).2 (pow_nonneg ha₀.le _)
  rw [← Summable.tsum_finsetSum hs]
  simp_rw [← Finset.mul_sum, g69am_occ_sum]
  rw [tsum_mul_right, tsum_geometric_of_lt_one ha₀.le ha₁]
  ring

end G69AM

lemma g69ai_rew {N : ℕ} (P : Kernel (Fin (N + 1)) (Fin (N + 1)))
    [IsMarkovKernel P] (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (r : Fin (N + 1) → ℝ)
    (y : Fin (N + 1) → ℝ)
    (hAG : IsAdaptiveGreedy (conservationCoeff P a) r (Equiv.refl (Fin (N + 1))) y)
    (j : Fin (N + 1)) :
    r j = greedyIndex (Equiv.refl (Fin (N + 1))) y (Fin.last N) -
      ∑ i ∈ univ.filter (fun i : Fin N ↦ j ≤ i.castSucc),
        (greedyIndex (Equiv.refl (Fin (N + 1))) y i.succ -
          greedyIndex (Equiv.refl (Fin (N + 1))) y i.castSucc) *
          conservationCoeff P a (Iic i.castSucc) j := by
  have hlow : ∀ l : Fin (N + 1), lowSet (Equiv.refl (Fin (N + 1))) ((l : ℕ) + 1) = Finset.Iic l := by
    intro l; ext x; simp only [lowSet, Equiv.coe_refl, Finset.image_id, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic, Fin.le_iff_val_le_val]; omega
  have hg := (hAG j).2
  simp only [Equiv.refl_apply] at hg
  rw [hlow j] at hg
  have hpos : 0 < conservationCoeff P a (Iic j) j :=
    lt_of_lt_of_le one_pos (g69ai_A_ge P ha₀ ha₁ _ j (Finset.mem_Iic.2 le_rfl))
  have hr : r j = y j * conservationCoeff P a (Iic j) j +
      ∑ l ∈ univ.filter (fun l => j < l), conservationCoeff P a (Iic l) j * y l := by
    unfold greedyNumerator at hg
    simp only [hlow] at hg
    rw [div_eq_iff hpos.ne'] at hg
    linarith
  -- greedy indices
  have hgI : ∀ x : Fin (N + 1), greedyIndex (Equiv.refl (Fin (N + 1))) y x =
      ∑ l, if x ≤ l then y l else 0 := by
    intro x; unfold greedyIndex; rw [Finset.sum_filter]; rfl
  have hlast : greedyIndex (Equiv.refl (Fin (N + 1))) y (Fin.last N) = y (Fin.last N) := by
    rw [hgI]
    have : ∀ l : Fin (N + 1), (if Fin.last N ≤ l then y l else 0) = if l = Fin.last N then y l else 0 := by
      intro l; congr 1; apply propext; constructor
      · intro h; exact le_antisymm (Fin.le_last l) h
      · intro h; rw [h]
    simp_rw [this]; simp
  have hdiff : ∀ i : Fin N, greedyIndex (Equiv.refl (Fin (N + 1))) y i.succ -
      greedyIndex (Equiv.refl (Fin (N + 1))) y i.castSucc = -y i.castSucc := by
    intro i
    rw [hgI, hgI]
    have : ∀ l : Fin (N + 1), (if i.castSucc ≤ l then y l else 0) =
        (if l = i.castSucc then y l else 0) + (if i.succ ≤ l then y l else 0) := by
      intro l
      by_cases h1 : l = i.castSucc
      · subst h1
        have : ¬ i.succ ≤ i.castSucc := by simp [Fin.le_def]
        simp [this]
      · have : (i.castSucc ≤ l) ↔ (i.succ ≤ l) := by
          simp only [Fin.le_def, Fin.coe_castSucc, Fin.val_succ]
          have : (l : ℕ) ≠ i := fun h => h1 (Fin.ext h)
          omega
        simp [h1, this]
    simp_rw [this, Finset.sum_add_distrib]; simp
  have hA1 : conservationCoeff P a (Iic (Fin.last N)) j = 1 := by
    have : (Iic (Fin.last N) : Finset (Fin (N + 1))) = univ := by
      ext x; simp [Fin.le_last]
    rw [this]; exact g69ai_A_univ P j
  -- LHS as a full sum
  have e1 : r j = ∑ l, if j ≤ l then conservationCoeff P a (Iic l) j * y l else 0 := by
    rw [hr, Finset.sum_filter]
    have : ∀ l : Fin (N + 1), (if j ≤ l then conservationCoeff P a (Iic l) j * y l else 0) =
        (if l = j then conservationCoeff P a (Iic l) j * y l else 0) +
          (if j < l then conservationCoeff P a (Iic l) j * y l else 0) := by
      intro l
      by_cases h1 : l = j
      · subst h1; simp
      · have : j ≤ l ↔ j < l := ⟨fun h => lt_of_le_of_ne h (Ne.symm h1), le_of_lt⟩
        simp [h1, this]
    simp_rw [this, Finset.sum_add_distrib]; simp; ring
  rw [e1, Fin.sum_univ_castSucc, hlast, Finset.sum_filter]
  simp_rw [hdiff]
  rw [if_pos (Fin.le_last j), hA1]
  have : ∀ i : Fin N, (if j ≤ i.castSucc then -y i.castSucc * conservationCoeff P a (Iic i.castSucc) j else 0)
      = -(if j ≤ i.castSucc then conservationCoeff P a (Iic i.castSucc) j * y i.castSucc else 0) := by
    intro i; split_ifs <;> ring
  simp_rw [this, Finset.sum_neg_distrib]; ring


lemma g69ai_ret {N n M : ℕ} (P : Kernel (Fin (N + 1)) (Fin (N + 1)))
    [IsMarkovKernel P] (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (r : Fin (N + 1) → ℝ)
    (y : Fin (N + 1) → ℝ)
    (hAG : IsAdaptiveGreedy (conservationCoeff P a) r (Equiv.refl (Fin (N + 1))) y)
    (k : Fin n → Fin (N + 1)) (π : ParallelPolicy n N M) :
    parallelReturn P π a r k =
      greedyIndex (Equiv.refl (Fin (N + 1))) y (Fin.last N) * ((M : ℝ) / (1 - a)) -
      ∑ i : Fin N,
        (greedyIndex (Equiv.refl (Fin (N + 1))) y i.succ -
          greedyIndex (Equiv.refl (Fin (N + 1))) y i.castSucc) *
          coeffSum P π a k (Iic i.castSucc) := by
  unfold parallelReturn linearObjective
  set x := parallelPerformance P π a k with hx
  set d : Fin N → ℝ := fun i => greedyIndex (Equiv.refl (Fin (N + 1))) y i.succ -
      greedyIndex (Equiv.refl (Fin (N + 1))) y i.castSucc with hd
  have hexp : ∀ j, r j = greedyIndex (Equiv.refl (Fin (N + 1))) y (Fin.last N) -
      ∑ i : Fin N, d i * conservationCoeff P a (Iic i.castSucc) j := by
    intro j
    rw [g69ai_rew P a ha₀ ha₁ r y hAG j, Finset.sum_filter]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · have : conservationCoeff P a (Iic i.castSucc) j = 0 := by
        unfold conservationCoeff; rw [if_neg (by simpa using h)]
      rw [this, mul_zero]
  simp_rw [hexp]
  have hsum := g69am_perf_sum P π a ha₀ ha₁ k
  rw [← hx] at hsum
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [← Finset.mul_sum, hsum, Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_mul]
  unfold coeffSum
  rw [← hx, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hd]; ring


lemma g69ai_policy_nonempty {N n M : ℕ} (hMn : M ≤ n) : Nonempty (ParallelPolicy n N M) := by
  classical
  let s0 : Fin n → Bool := fun b => decide ((b : ℕ) < M)
  have hs0 : selCount s0 = M := by
    unfold selCount
    have : (univ.filter fun b : Fin n => s0 b = true) = univ.filter fun b : Fin n => (b : ℕ) < M := by
      ext b; simp [s0]
    rw [this, Fin.card_filter_val_lt, min_eq_right hMn]
  exact ⟨{ select := fun t => Kernel.const _ (Measure.dirac s0)
           markov := fun t => inferInstance
           card_eq := fun t h => by
             rw [Kernel.const_apply, Measure.dirac_apply' _ (Set.Finite.measurableSet (Set.toFinite _))]
             simp [hs0] }⟩

lemma g69ai_cC_nonneg {N : ℕ} (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P] {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (S : Finset (Fin (N + 1))) (j : Fin (N + 1)) :
    0 ≤ conservationCoeff P a S j := by
  by_cases h : j ∈ S
  · exact le_trans zero_le_one (g69ai_A_ge P ha0 ha1 S j h)
  · unfold conservationCoeff; rw [if_neg h]

lemma g69ai_coeffSum_nonneg {N n M : ℕ} (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (π : ParallelPolicy n N M) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (k : Fin n → Fin (N + 1))
    (S : Finset (Fin (N + 1))) : 0 ≤ coeffSum P π a k S := by
  unfold coeffSum
  refine Finset.sum_nonneg fun i _ => mul_nonneg (g69ai_cC_nonneg P ha0 ha1 S i) ?_
  unfold parallelPerformance
  exact tsum_nonneg fun t => mul_nonneg (pow_nonneg ha0.le _) (g69am_occ_bd P π k i t).1

section G70AL
variable {N n M : ℕ}

lemma g70al_move_ae (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (arm : Fin (N + 1) → Fin n) (hP1 : ∀ i, P i {j | arm j = arm i} = 1)
    (x : Fin n → Fin (N + 1)) (hx : ∀ b, arm (x b) = b) (s : Fin n → Bool) :
    ∀ᵐ y ∂(parallelMove (n := n) P (x, s)), ∀ b, arm (y b) = b := by
  simp only [parallelMove, Kernel.coe_mk]
  have hset : {y : Fin n → Fin (N + 1) | ∀ b, arm (y b) = b} =
      Set.univ.pi (fun b => {j | arm j = b}) := by ext y; simp
  rw [ae_iff]
  have : {y : Fin n → Fin (N + 1) | ¬ ∀ b, arm (y b) = b} =
      {y : Fin n → Fin (N + 1) | ∀ b, arm (y b) = b}ᶜ := by ext y; simp
  rw [this, prob_compl_eq_zero_iff MeasurableSet.of_discrete, hset, Measure.pi_pi]
  refine Finset.prod_eq_one fun b _ => ?_
  unfold armKernel
  split_ifs
  · have := hP1 (x b); rw [hx b] at this; exact this
  · rw [Kernel.id_apply, Measure.dirac_apply' _ MeasurableSet.of_discrete]
    simp [hx b]

lemma g70al_inv (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (arm : Fin (N + 1) → Fin n) (hP1 : ∀ i, P i {j | arm j = arm i} = 1)
    (π : ParallelPolicy n N M) (k : Fin n → Fin (N + 1)) (hk : ∀ b, arm (k b) = b) (t : ℕ) :
    ∀ᵐ h ∂parallelMeasure P π k t, ∀ b, arm (h.2 b) = b := by
  induction t with
  | zero =>
    simp only [parallelMeasure]
    rw [ae_dirac_iff MeasurableSet.of_discrete]; exact hk
  | succ t ih =>
    simp only [parallelMeasure]
    rw [ae_map_iff (measurable_of_countable _).aemeasurable MeasurableSet.of_discrete]
    apply Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete
    filter_upwards [ih] with h hh
    unfold parallelStepKernel
    apply Kernel.ae_compProd_of_ae_ae MeasurableSet.of_discrete
    filter_upwards with s
    rw [Kernel.comap_apply]
    exact g70al_move_ae P arm hP1 h.2 hh s

noncomputable def g70al_pol (s0 : Fin n → Bool) (hs0 : selCount s0 = M) : ParallelPolicy n N M where
  select := fun _ => Kernel.const _ (Measure.dirac s0)
  markov := fun _ => inferInstance
  card_eq := fun t h => by
    rw [Kernel.const_apply, Measure.dirac_apply' _ MeasurableSet.of_discrete]
    simp [hs0]

lemma g70al_last (P : Kernel (Fin (N + 1)) (Fin (N + 1))) [IsMarkovKernel P]
    (arm : Fin (N + 1) → Fin n) (hP1 : ∀ i, P i {j | arm j = arm i} = 1)
    (s0 : Fin n → Bool) (hs0 : selCount s0 = M)
    (k : Fin n → Fin (N + 1)) (hk : ∀ b, arm (k b) = b) (t : ℕ) :
    ∀ᵐ h ∂parallelMeasure P (g70al_pol (N := N) s0 hs0) k (t + 1),
      (h.1 (Fin.last t)).2 = s0 ∧ ∀ b, arm ((h.1 (Fin.last t)).1 b) = b := by
  simp only [parallelMeasure]
  rw [ae_map_iff (measurable_of_countable _).aemeasurable MeasurableSet.of_discrete]
  simp only [Fin.snoc_last]
  apply Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete
  filter_upwards [g70al_inv P arm hP1 (g70al_pol (N := N) s0 hs0) k hk t] with h hh
  unfold parallelStepKernel
  apply Kernel.ae_compProd_of_ae_ae MeasurableSet.of_discrete
  simp only [g70al_pol, Kernel.const_apply]
  rw [ae_dirac_iff MeasurableSet.of_discrete]
  exact Filter.Eventually.of_forall fun _ => ⟨rfl, hh⟩

end G70AL

open AllocationIndices.Branching in
theorem solution {N n M : ℕ} (P : Kernel (Fin (N + 1)) (Fin (N + 1)))
    [IsMarkovKernel P] (arm : Fin (N + 1) → Fin n) (hP : IsArmFamily P arm)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hM : 1 ≤ M) (hMn : M ≤ n)
    (k : Fin n → Fin (N + 1)) (hk : ∀ b, arm (k b) = b) (i : Fin (N + 1))
    (hψ : M ≤ psi arm i) :
    minCoeffSum P M a k (Iic i) = 0 := by
  classical
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (s := missedArms arm i) hψ
  let s0 : Fin n → Bool := fun b => decide (b ∈ T)
  have hs0 : selCount s0 = M := by
    unfold selCount
    have : (univ.filter fun b : Fin n => s0 b = true) = T := by ext b; simp [s0]
    rw [this, hTc]
  let π0 : ParallelPolicy n N M := g70al_pol s0 hs0
  have hocc : ∀ i' ∈ Iic i, ∀ t, parallelOccupation P π0 k i' t = 0 := by
    intro i' hi' t
    unfold parallelOccupation
    apply integral_eq_zero_of_ae
    filter_upwards [g70al_last P arm hP.1 s0 hs0 k hk t] with h ⟨hs, ha⟩
    simp only [Pi.zero_apply, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro b - ⟨hb1, hb2⟩
    rw [hs] at hb1
    have hbT : b ∈ T := by simpa [s0] using hb1
    have hbB := hT hbT
    simp only [missedArms, Finset.mem_filter, Finset.mem_univ, true_and] at hbB
    have h1 := ha b
    rw [hb2] at h1
    have := hbB i' h1
    rw [Finset.mem_Iic] at hi'
    exact absurd hi' (not_le.2 this)
  have h0 : coeffSum P π0 a k (Iic i) = 0 := by
    unfold coeffSum
    refine Finset.sum_eq_zero fun i' _ => ?_
    by_cases hi' : i' ∈ Iic i
    · unfold parallelPerformance
      simp [hocc i' hi']
    · unfold conservationCoeff; rw [if_neg hi', zero_mul]
  unfold minCoeffSum
  apply le_antisymm
  · refine (ciInf_le ⟨0, ?_⟩ π0).trans (le_of_eq h0)
    rintro _ ⟨π, rfl⟩
    exact g69ai_coeffSum_nonneg P π ha₀ ha₁ k _
  · haveI : Nonempty (ParallelPolicy n N M) := ⟨π0⟩
    exact le_ciInf fun π => g69ai_coeffSum_nonneg P π ha₀ ha₁ k _
