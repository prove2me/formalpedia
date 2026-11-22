-- Prove2me | solution 1 for AllocationIndices.Freezing.optimal_value_le_max_index_stage
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:22:06.563248+00:00
-- url     : https://prove2.me/submissions/4044bed9-f048-4de1-a6f4-5e25c95deea1

import Definitions.Def_AllocationIndices_Freezing_Model
import Theorems.Thm_WeberGittins_Submodular_restricted_value_eq_expected_interleaved_charge

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices AllocationIndices.Freezing
open WeberGittins.Submodular WeberGittins.Suboptimality
open Filter Topology Finset

/-!
Proof of `AllocationIndices.Freezing.optimal_value_le_max_index_stage` via Weber's
prevailing-charge interleaving representation (`restricted_value_eq_expected_interleaved_charge`),
Abel summation on `partialInterleavedSum`, and the Markov shift property of `markovChainMeasure`.
-/

section ArithmeticHelpers

private instance instIsProbabilityMeasureMarkovChain {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    IsProbabilityMeasure (markovChainMeasure P x) := by
  unfold markovChainMeasure
  infer_instance

private lemma discountPow_top (a : ℝ) : discountPow a ⊤ = 0 := rfl

private lemma discountPow_coe (a : ℝ) (n : ℕ) : discountPow a (n : ℕ∞) = a ^ n := rfl

private lemma summable_nat_succ_mul_pow {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Summable (fun t : ℕ ↦ ((t : ℝ) + 1) * a ^ t) := by
  have hnorm : ‖a‖ < 1 := by rw [Real.norm_of_nonneg ha0.le]; exact ha1
  have h1 : Summable (fun t : ℕ ↦ (t : ℝ) * a ^ t) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have h0 : Summable (fun t : ℕ ↦ a ^ t) := summable_geometric_of_lt_one ha0.le ha1
  simpa [add_mul, one_mul] using h1.add h0

private lemma tendsto_nat_mul_pow_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun t : ℕ ↦ (t : ℝ) * a ^ t) atTop (nhds 0) := by
  have hnorm : ‖a‖ < 1 := by rw [Real.norm_of_nonneg ha0.le]; exact ha1
  have h1 : Summable (fun t : ℕ ↦ (t : ℝ) * a ^ t) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  exact h1.tendsto_atTop_zero

private lemma abel_partial_sum (a : ℝ) (U : ℕ → ℝ) (hU0 : U 0 = 0) (K : ℕ) :
    ∑ t ∈ Finset.range K, a ^ t * (U (t + 1) - U t) =
      (1 - a) * ∑ t ∈ Finset.range K, a ^ t * U (t + 1) + a ^ K * U K := by
  induction K with
  | zero => simp [hU0]
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

private lemma abel_tsum_eq {a C : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (U : ℕ → ℝ)
    (hU0 : U 0 = 0) (hU_nn : ∀ t, 0 ≤ U t) (hU_le : ∀ t, U t ≤ (t : ℝ) * C)
    (hs1 : Summable (fun t : ℕ ↦ a ^ t * (U (t + 1) - U t))) :
    ∑' t : ℕ, a ^ t * (U (t + 1) - U t) =
      (1 - a) * ∑' t : ℕ, a ^ t * U (t + 1) := by
  have hs2 : Summable (fun t : ℕ ↦ a ^ t * U (t + 1)) := by
    refine Summable.of_nonneg_of_le (fun t ↦ mul_nonneg (pow_nonneg ha0.le t) (hU_nn (t + 1)))
      (fun t ↦ ?_) ((summable_nat_succ_mul_pow ha0 ha1).mul_left C)
    calc a ^ t * U (t + 1) ≤ a ^ t * (((t + 1 : ℕ) : ℝ) * C) :=
          mul_le_mul_of_nonneg_left (hU_le (t + 1)) (pow_nonneg ha0.le t)
      _ = C * (((t : ℝ) + 1) * a ^ t) := by push_cast; ring
  have htail : Tendsto (fun K : ℕ ↦ a ^ K * U K) atTop (nhds 0) := by
    refine squeeze_zero (fun K ↦ mul_nonneg (pow_nonneg ha0.le K) (hU_nn K))
      (fun K ↦ ?_) (by simpa using (tendsto_nat_mul_pow_zero ha0 ha1).const_mul C)
    calc a ^ K * U K ≤ a ^ K * ((K : ℝ) * C) :=
          mul_le_mul_of_nonneg_left (hU_le K) (pow_nonneg ha0.le K)
      _ = C * ((K : ℝ) * a ^ K) := by ring
  have hL : Tendsto (fun K ↦ ∑ t ∈ Finset.range K, a ^ t * (U (t + 1) - U t)) atTop
      (nhds (∑' t : ℕ, a ^ t * (U (t + 1) - U t))) := hs1.hasSum.tendsto_sum_nat
  have hR : Tendsto (fun K ↦ (1 - a) * ∑ t ∈ Finset.range K, a ^ t * U (t + 1) + a ^ K * U K)
      atTop (nhds ((1 - a) * ∑' t : ℕ, a ^ t * U (t + 1) + 0)) :=
    (hs2.hasSum.tendsto_sum_nat.const_mul (1 - a)).add htail
  have hEq : (fun K ↦ ∑ t ∈ Finset.range K, a ^ t * (U (t + 1) - U t)) =
      (fun K ↦ (1 - a) * ∑ t ∈ Finset.range K, a ^ t * U (t + 1) + a ^ K * U K) := by
    funext K; exact abel_partial_sum a U hU0 K
  rw [hEq] at hL
  have := tendsto_nhds_unique hL hR
  linarith

private lemma geom_weight_identity (a : ℝ) (N : ℕ) :
    (1 - a) * (∑ t ∈ Finset.range N, ((t : ℝ) + 1) * a ^ t) + (N : ℝ) * a ^ N =
      ∑ t ∈ Finset.range N, a ^ t := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, pow_succ]
    push_cast
    linarith

private lemma geom_weight_tsum {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (1 - a) * ∑' t : ℕ, ((t : ℝ) + 1) * a ^ t = ∑' t : ℕ, a ^ t := by
  have hL : Tendsto (fun N ↦ (1 - a) * (∑ t ∈ Finset.range N, ((t : ℝ) + 1) * a ^ t) +
      (N : ℝ) * a ^ N) atTop (nhds ((1 - a) * (∑' t : ℕ, ((t : ℝ) + 1) * a ^ t) + 0)) :=
    ((summable_nat_succ_mul_pow ha0 ha1).hasSum.tendsto_sum_nat.const_mul (1 - a)).add
      (tendsto_nat_mul_pow_zero ha0 ha1)
  have hR : Tendsto (fun N ↦ ∑ t ∈ Finset.range N, a ^ t) atTop (nhds (∑' t : ℕ, a ^ t)) :=
    (summable_geometric_of_lt_one ha0.le ha1).hasSum.tendsto_sum_nat
  have hEq : (fun N ↦ (1 - a) * (∑ t ∈ Finset.range N, ((t : ℝ) + 1) * a ^ t) + (N : ℝ) * a ^ N) =
      (fun N ↦ ∑ t ∈ Finset.range N, a ^ t) := by
    funext N; exact geom_weight_identity a N
  rw [hEq] at hL
  have := tendsto_nhds_unique hL hR
  linarith

private lemma discountPow_nonneg {a : ℝ} (ha0 : 0 ≤ a) (n : ℕ∞) :
    0 ≤ discountPow a n := by
  cases n with
  | top => rw [discountPow_top]
  | coe m => rw [discountPow_coe]; exact pow_nonneg ha0 m

private lemma discountPow_le_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ∞) :
    discountPow a n ≤ 1 := by
  cases n with
  | top => rw [discountPow_top]; exact zero_le_one
  | coe m => rw [discountPow_coe]; exact pow_le_one₀ ha0 ha1

private lemma discountPow_le_of_one_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {n : ℕ∞}
    (hn : 1 ≤ n) : discountPow a n ≤ a := by
  cases n with
  | top => rw [discountPow_top]; exact ha0
  | coe m =>
    have hm : 1 ≤ m := by exact_mod_cast hn
    have hpow : a ^ m ≤ a ^ 1 := pow_le_pow_of_le_one ha0 ha1 hm
    rw [discountPow_coe]
    simpa using hpow

private lemma discountedStoppedSum_one_of_nat {S : Type*} (a : ℝ) (N : ℕ) (ω : ℕ → S) :
    discountedStoppedSum a (fun _ ↦ 1) (fun _ ↦ (N : ℕ∞)) ω = ∑ t ∈ Finset.range N, a ^ t := by
  unfold discountedStoppedSum
  simp only [mul_one, Nat.cast_lt]
  rw [tsum_eq_sum (s := Finset.range N)]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    simp [ht]
  · intro t ht
    rw [Finset.mem_range, not_lt] at ht
    simp [not_lt.2 ht]

private lemma discountedStoppedSum_one_of_top {S : Type*} (a : ℝ) (ω : ℕ → S) :
    discountedStoppedSum a (fun _ ↦ 1) (fun _ ↦ (⊤ : ℕ∞)) ω = ∑' t : ℕ, a ^ t := by
  unfold discountedStoppedSum
  simp

private lemma discountedStoppedSum_one_eq_div {S : Type*} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S) :
    discountedStoppedSum a (fun _ ↦ 1) τ ω = (1 - discountPow a (τ ω)) / (1 - a) := by
  have hsub : 1 - a ≠ 0 := sub_ne_zero.2 ha1.ne'
  cases h : τ ω with
  | top =>
    have : discountedStoppedSum a (fun _ ↦ 1) τ ω =
        discountedStoppedSum a (fun _ ↦ 1) (fun _ ↦ (⊤ : ℕ∞)) ω := by
      unfold discountedStoppedSum; simp [h]
    rw [this, discountedStoppedSum_one_of_top, tsum_geometric_of_lt_one ha0.le ha1,
      discountPow_top, sub_zero, one_div]
  | coe N =>
    have hsub' : a - 1 ≠ 0 := sub_ne_zero.2 ha1.ne
    have : discountedStoppedSum a (fun _ ↦ 1) τ ω =
        discountedStoppedSum a (fun _ ↦ 1) (fun _ ↦ (N : ℕ∞)) ω := by
      unfold discountedStoppedSum; simp [h]
    rw [this, discountedStoppedSum_one_of_nat, discountPow_coe, geom_sum_eq ha1.ne]
    field_simp [hsub, hsub']
    ring

end ArithmeticHelpers

section CombinatorialBound

private lemma exists_sub_allocation {α : Type*} [DecidableEq α] (S : Finset α)
    (f : α → ℕ) (s : ℕ) (hs : s ≤ ∑ j ∈ S, f j) :
    ∃ g : α → ℕ, (∀ j ∈ S, g j ≤ f j) ∧ (∀ j ∉ S, g j = 0) ∧ ∑ j ∈ S, g j = s := by
  induction S using Finset.induction generalizing s with
  | empty =>
    simp at hs
    subst hs
    exact ⟨fun _ ↦ 0, by simp, by simp, by simp⟩
  | @insert x S hx ih =>
    rw [Finset.sum_insert hx] at hs
    let c := min s (f x)
    have hc_le_s : c ≤ s := min_le_left s (f x)
    have hc_le_fx : c ≤ f x := min_le_right s (f x)
    have hs' : s - c ≤ ∑ j ∈ S, f j := by omega
    obtain ⟨g, hg_le, hg_zero, hg_sum⟩ := ih (s - c) hs'
    refine ⟨Function.update g x c, ?_, ?_, ?_⟩
    · intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · simpa using hc_le_fx
      · have hjx : j ≠ x := fun h ↦ hx (h ▸ hj)
        simpa [hjx] using hg_le j hj
    · intro j hj
      rw [Finset.mem_insert, not_or] at hj
      simpa [hj.1] using hg_zero j hj.2
    · rw [Finset.sum_insert hx, Function.update_self]
      have hcongr : ∑ j ∈ S, Function.update g x c j = ∑ j ∈ S, g j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjx : j ≠ x := fun h ↦ hx (h ▸ hj)
        simp [hjx]
      rw [hcongr, hg_sum]
      omega

private lemma partialInterleavedSum_univ_zero {k : ℕ} (H : Fin k → ℕ → ℝ) :
    partialInterleavedSum H Finset.univ 0 = 0 := by
  unfold partialInterleavedSum
  split_ifs with hI
  · rfl
  · apply le_antisymm
    · refine Finset.sup'_le _ _ fun m hm ↦ ?_
      simp only [playAllocations, Finset.mem_filter, Finset.mem_univ, not_true_eq_false,
        IsEmpty.forall_iff, implies_true, true_and] at hm
      have hm0 : ∀ j, m j = 0 := fun j ↦ Finset.sum_eq_zero_iff.1 hm.2 j (Finset.mem_univ j)
      simp [hm0]
    · have hmem : (fun _ : Fin k ↦ 0) ∈ playAllocations Finset.univ 0 := by
        simp [playAllocations]
      calc (0 : ℝ) = ∑ j ∈ (Finset.univ : Finset (Fin k)), ∑ u ∈ Finset.range 0, H j u := by simp
        _ ≤ _ := Finset.le_sup' (f := fun m ↦ ∑ j ∈ Finset.univ, ∑ u ∈ Finset.range (m j), H j u) hmem

private lemma partialInterleavedSum_univ_nonneg {k : ℕ} (i : Fin k) (H : Fin k → ℕ → ℝ)
    (hH : ∀ j u, 0 ≤ H j u) (t : ℕ) :
    0 ≤ partialInterleavedSum H Finset.univ t := by
  have hne : (Finset.univ : Finset (Fin k)) ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨i, Finset.mem_univ i⟩
  unfold partialInterleavedSum
  rw [dif_neg hne]
  obtain ⟨m, hm⟩ := playAllocations_nonempty hne t
  calc (0 : ℝ) ≤ ∑ j ∈ Finset.univ, ∑ u ∈ Finset.range (m j), H j u :=
        Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun u _ ↦ hH j u
    _ ≤ _ := Finset.le_sup' (f := fun m ↦ ∑ j ∈ Finset.univ, ∑ u ∈ Finset.range (m j), H j u) hm

private lemma partialInterleavedSum_univ_le_mul {k : ℕ} (i : Fin k) (H : Fin k → ℕ → ℝ)
    {M : ℝ} (hH : ∀ j u, H j u ≤ M) (t : ℕ) :
    partialInterleavedSum H Finset.univ t ≤ (t : ℝ) * M := by
  have hne : (Finset.univ : Finset (Fin k)) ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨i, Finset.mem_univ i⟩
  unfold partialInterleavedSum
  rw [dif_neg hne]
  refine Finset.sup'_le _ _ fun m hm ↦ ?_
  simp only [playAllocations, Finset.mem_filter] at hm
  calc ∑ j ∈ Finset.univ, ∑ u ∈ Finset.range (m j), H j u
      ≤ ∑ j ∈ Finset.univ, ∑ _u ∈ Finset.range (m j), M :=
        Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun u _ ↦ hH j u
    _ = ∑ j ∈ Finset.univ, (m j : ℝ) * M := by simp
    _ = (∑ j ∈ Finset.univ, (m j : ℝ)) * M := by rw [← Finset.sum_mul]
    _ = ((∑ j ∈ Finset.univ, m j : ℕ) : ℝ) * M := by push_cast; rfl
    _ = (t : ℝ) * M := by rw [hm.2.2]

private lemma partialInterleavedSum_univ_step_bounds {k : ℕ} (i : Fin k) (H : Fin k → ℕ → ℝ)
    {C : ℝ} (hH0 : ∀ j u, 0 ≤ H j u) (hHC : ∀ j u, H j u ≤ C) (t : ℕ) :
    0 ≤ partialInterleavedSum H Finset.univ (t + 1) - partialInterleavedSum H Finset.univ t ∧
    partialInterleavedSum H Finset.univ (t + 1) - partialInterleavedSum H Finset.univ t ≤ C := by
  have hne : (Finset.univ : Finset (Fin k)) ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨i, Finset.mem_univ i⟩
  unfold partialInterleavedSum
  rw [dif_neg hne, dif_neg hne]
  constructor
  · rw [sub_nonneg]
    refine Finset.sup'_le _ _ fun m hm ↦ ?_
    simp only [playAllocations, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hm
    let m' : Fin k → ℕ := Function.update m i (m i + 1)
    have hm'_sum : ∑ j : Fin k, m' j = t + 1 := by
      have h1 := Finset.sum_update_of_mem (Finset.mem_univ i) m (m i + 1)
      rw [Finset.sdiff_singleton_eq_erase] at h1
      have h2 := Finset.add_sum_erase Finset.univ m (Finset.mem_univ i)
      dsimp [m']
      omega
    have hm'_mem : m' ∈ playAllocations Finset.univ (t + 1) := by
      simp only [playAllocations, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      refine ⟨fun j ↦ ?_, fun j hj ↦ (hj (Finset.mem_univ j)).elim, hm'_sum⟩
      have hle : m' j ≤ ∑ l : Fin k, m' l :=
        Finset.single_le_sum (f := m') (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
      omega
    calc ∑ j ∈ Finset.univ, ∑ u ∈ Finset.range (m j), H j u
        ≤ ∑ j ∈ Finset.univ, ∑ u ∈ Finset.range (m' j), H j u := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          by_cases hj : j = i
          · subst hj
            simp only [m', Function.update_self, Finset.sum_range_succ]
            linarith [hH0 j (m j)]
          · simp [m', hj]
      _ ≤ _ := Finset.le_sup' (f := fun m ↦ ∑ j ∈ Finset.univ, ∑ u ∈ Finset.range (m j), H j u) hm'_mem
  · rw [sub_le_iff_le_add]
    refine Finset.sup'_le _ _ fun m hm ↦ ?_
    simp only [playAllocations, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hm
    have hex : ∃ j₀ : Fin k, 0 < m j₀ := by
      by_contra h
      push Not at h
      have h0 : ∑ j : Fin k, m j = 0 := Finset.sum_eq_zero fun j _ ↦ Nat.eq_zero_of_le_zero (h j)
      omega
    obtain ⟨j₀, hj₀⟩ := hex
    let m' : Fin k → ℕ := Function.update m j₀ (m j₀ - 1)
    have hm'_sum : ∑ j : Fin k, m' j = t := by
      have h1 := Finset.sum_update_of_mem (Finset.mem_univ j₀) m (m j₀ - 1)
      rw [Finset.sdiff_singleton_eq_erase] at h1
      have h2 := Finset.add_sum_erase Finset.univ m (Finset.mem_univ j₀)
      dsimp [m']
      omega
    have hm'_mem : m' ∈ playAllocations Finset.univ t := by
      simp only [playAllocations, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      refine ⟨fun j ↦ ?_, fun j hj ↦ (hj (Finset.mem_univ j)).elim, hm'_sum⟩
      have hle : m' j ≤ ∑ l : Fin k, m' l :=
        Finset.single_le_sum (f := m') (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
      omega
    have hstep : ∑ j ∈ Finset.univ, ∑ u ∈ Finset.range (m j), H j u =
        (∑ j ∈ Finset.univ, ∑ u ∈ Finset.range (m' j), H j u) + H j₀ (m j₀ - 1) := by
      have h1 := Finset.add_sum_erase Finset.univ (fun j ↦ ∑ u ∈ Finset.range (m j), H j u)
        (Finset.mem_univ j₀)
      have h2 := Finset.add_sum_erase Finset.univ (fun j ↦ ∑ u ∈ Finset.range (m' j), H j u)
        (Finset.mem_univ j₀)
      have hrest : ∑ j ∈ Finset.univ.erase j₀, ∑ u ∈ Finset.range (m' j), H j u =
          ∑ j ∈ Finset.univ.erase j₀, ∑ u ∈ Finset.range (m j), H j u := by
        apply Finset.sum_congr rfl
        intro j hj
        have hne' : j ≠ j₀ := (Finset.mem_erase.1 hj).1
        simp [m', hne']
      have hmj₀ : m j₀ = (m j₀ - 1) + 1 := by omega
      have htop : ∑ u ∈ Finset.range (m j₀), H j₀ u =
          (∑ u ∈ Finset.range (m' j₀), H j₀ u) + H j₀ (m j₀ - 1) := by
        conv_lhs => rw [hmj₀]
        rw [Finset.sum_range_succ]
        simp [m']
      linarith
    have hle_sup := Finset.le_sup' (f := fun m ↦ ∑ j ∈ Finset.univ, ∑ u ∈ Finset.range (m j), H j u) hm'_mem
    linarith [hHC j₀ (m j₀ - 1)]

private lemma partialInterleavedSum_univ_add_le {k : ℕ} (i : Fin k) (N s : ℕ)
    (H H' : Fin k → ℕ → ℝ) {M : ℝ}
    (hHM : ∀ j u, H j u ≤ M)
    (hH'_ne : ∀ j, j ≠ i → ∀ u, H' j u = H j u)
    (hH'_i : ∀ u, H i (N + u) ≤ H' i u) :
    partialInterleavedSum H Finset.univ (N + s) ≤
      (N : ℝ) * M + partialInterleavedSum H' Finset.univ s := by
  have hne : (Finset.univ : Finset (Fin k)) ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨i, Finset.mem_univ i⟩
  unfold partialInterleavedSum
  rw [dif_neg hne, dif_neg hne]
  refine Finset.sup'_le _ _ fun m hm ↦ ?_
  simp only [playAllocations, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hm
  by_cases hmi : N ≤ m i
  · let m' : Fin k → ℕ := Function.update m i (m i - N)
    have hm'_sum : ∑ j : Fin k, m' j = s := by
      have h1 := Finset.sum_update_of_mem (Finset.mem_univ i) m (m i - N)
      rw [Finset.sdiff_singleton_eq_erase] at h1
      have h2 := Finset.add_sum_erase Finset.univ m (Finset.mem_univ i)
      dsimp [m']
      omega
    have hm'_mem : m' ∈ playAllocations Finset.univ s := by
      simp only [playAllocations, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      refine ⟨fun j ↦ ?_, fun j hj ↦ (hj (Finset.mem_univ j)).elim, hm'_sum⟩
      have hle : m' j ≤ ∑ l : Fin k, m' l :=
        Finset.single_le_sum (f := m') (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
      omega
    have hi_split : ∑ u ∈ Finset.range (m i), H i u ≤
        (N : ℝ) * M + ∑ u ∈ Finset.range (m' i), H' i u := by
      have hmi_eq : m i = N + (m i - N) := by omega
      conv_lhs => rw [hmi_eq]
      rw [Finset.sum_range_add]
      have h1 : ∑ u ∈ Finset.range N, H i u ≤ (N : ℝ) * M := by
        calc ∑ u ∈ Finset.range N, H i u ≤ ∑ _u ∈ Finset.range N, M :=
              Finset.sum_le_sum fun u _ ↦ hHM i u
          _ = (N : ℝ) * M := by simp
      have h2 : ∑ u ∈ Finset.range (m i - N), H i (N + u) ≤
          ∑ u ∈ Finset.range (m' i), H' i u := by
        simp only [m', Function.update_self]
        exact Finset.sum_le_sum fun u _ ↦ hH'_i u
      linarith
    have hrest : ∑ j ∈ Finset.univ.erase i, ∑ u ∈ Finset.range (m j), H j u =
        ∑ j ∈ Finset.univ.erase i, ∑ u ∈ Finset.range (m' j), H' j u := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjne : j ≠ i := (Finset.mem_erase.1 hj).1
      simp only [m', Function.update_of_ne hjne]
      exact Finset.sum_congr rfl fun u _ ↦ (hH'_ne j hjne u).symm
    have hsum1 := Finset.add_sum_erase Finset.univ (fun j ↦ ∑ u ∈ Finset.range (m j), H j u)
      (Finset.mem_univ i)
    have hsum2 := Finset.add_sum_erase Finset.univ (fun j ↦ ∑ u ∈ Finset.range (m' j), H' j u)
      (Finset.mem_univ i)
    have hle_sup := Finset.le_sup' (f := fun m ↦ ∑ j ∈ Finset.univ, ∑ u ∈ Finset.range (m j), H' j u) hm'_mem
    linarith
  · push Not at hmi
    have hs_le : s ≤ ∑ j ∈ Finset.univ.erase i, m j := by
      have h2 := Finset.add_sum_erase Finset.univ m (Finset.mem_univ i)
      omega
    obtain ⟨m', hm'_le, hm'_zero, hm'_sum_erase⟩ :=
      exists_sub_allocation (Finset.univ.erase i) m s hs_le
    have hm'_i : m' i = 0 := hm'_zero i (Finset.notMem_erase i Finset.univ)
    have hm'_sum : ∑ j : Fin k, m' j = s := by
      rw [← Finset.add_sum_erase Finset.univ m' (Finset.mem_univ i), hm'_i, zero_add, hm'_sum_erase]
    have hm'_mem : m' ∈ playAllocations Finset.univ s := by
      simp only [playAllocations, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      refine ⟨fun j ↦ ?_, fun j hj ↦ (hj (Finset.mem_univ j)).elim, hm'_sum⟩
      have hle : m' j ≤ ∑ l : Fin k, m' l :=
        Finset.single_le_sum (f := m') (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
      omega
    have hm'_le_all : ∀ j : Fin k, m' j ≤ m j := fun j ↦ by
      by_cases hj : j = i
      · subst hj; rw [hm'_i]; exact Nat.zero_le _
      · exact hm'_le j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
    have hterm : ∀ j : Fin k,
        ∑ u ∈ Finset.range (m j), H j u ≤
          (∑ u ∈ Finset.range (m' j), H' j u) + ((m j - m' j : ℕ) : ℝ) * M := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [hm'_i, Finset.range_zero, Finset.sum_empty, zero_add, Nat.sub_zero]
        calc ∑ u ∈ Finset.range (m j), H j u ≤ ∑ _u ∈ Finset.range (m j), M :=
              Finset.sum_le_sum fun u _ ↦ hHM j u
          _ = (m j : ℝ) * M := by simp
      · have hsplit : m j = m' j + (m j - m' j) := (Nat.add_sub_of_le (hm'_le_all j)).symm
        conv_lhs => rw [hsplit]
        rw [Finset.sum_range_add]
        have h1 : ∑ u ∈ Finset.range (m' j), H j u = ∑ u ∈ Finset.range (m' j), H' j u :=
          Finset.sum_congr rfl fun u _ ↦ (hH'_ne j hj u).symm
        have h2 : ∑ u ∈ Finset.range (m j - m' j), H j (m' j + u) ≤
            ((m j - m' j : ℕ) : ℝ) * M := by
          calc ∑ u ∈ Finset.range (m j - m' j), H j (m' j + u)
              ≤ ∑ _u ∈ Finset.range (m j - m' j), M :=
                Finset.sum_le_sum fun u _ ↦ hHM j (m' j + u)
            _ = ((m j - m' j : ℕ) : ℝ) * M := by simp
        linarith
    have hdiff_sum : ∑ j : Fin k, (m j - m' j) = N := by
      have hadd : ∑ j : Fin k, (m' j + (m j - m' j)) = ∑ j : Fin k, m j :=
        Finset.sum_congr rfl fun j _ ↦ Nat.add_sub_of_le (hm'_le_all j)
      rw [Finset.sum_add_distrib, hm'_sum, hm.2.2] at hadd
      omega
    have htot : ∑ j : Fin k, ∑ u ∈ Finset.range (m j), H j u ≤
        (∑ j : Fin k, ∑ u ∈ Finset.range (m' j), H' j u) + (N : ℝ) * M := by
      calc ∑ j : Fin k, ∑ u ∈ Finset.range (m j), H j u
          ≤ ∑ j : Fin k, ((∑ u ∈ Finset.range (m' j), H' j u) + ((m j - m' j : ℕ) : ℝ) * M) :=
            Finset.sum_le_sum fun j _ ↦ hterm j
        _ = (∑ j : Fin k, ∑ u ∈ Finset.range (m' j), H' j u) +
              (∑ j : Fin k, ((m j - m' j : ℕ) : ℝ)) * M := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
        _ = (∑ j : Fin k, ∑ u ∈ Finset.range (m' j), H' j u) + (N : ℝ) * M := by
            have : (∑ j : Fin k, ((m j - m' j : ℕ) : ℝ)) = (N : ℝ) := by
              exact_mod_cast hdiff_sum
            rw [this]
    have hle_sup := Finset.le_sup' (f := fun m ↦ ∑ j ∈ Finset.univ, ∑ u ∈ Finset.range (m j), H' j u) hm'_mem
    linarith

/-- Discounted interleaved charge sum for a stack `H`. -/
private noncomputable def discChargeSum {k : ℕ} (a : ℝ) (H : Fin k → ℕ → ℝ) : ℝ :=
  ∑' t : ℕ, a ^ t * (partialInterleavedSum H Finset.univ (t + 1) -
    partialInterleavedSum H Finset.univ t)

private lemma summable_discChargeSum_terms {k : ℕ} (i : Fin k) {a C : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (H : Fin k → ℕ → ℝ)
    (hH0 : ∀ j u, 0 ≤ H j u) (hHC : ∀ j u, H j u ≤ C) :
    Summable (fun t : ℕ ↦ a ^ t * (partialInterleavedSum H Finset.univ (t + 1) -
      partialInterleavedSum H Finset.univ t)) := by
  refine Summable.of_nonneg_of_le (fun t ↦ ?_) (fun t ↦ ?_)
    ((summable_geometric_of_lt_one ha0.le ha1).mul_left C)
  · exact mul_nonneg (pow_nonneg ha0.le t) (partialInterleavedSum_univ_step_bounds i H hH0 hHC t).1
  · calc a ^ t * (partialInterleavedSum H Finset.univ (t + 1) - partialInterleavedSum H Finset.univ t)
        ≤ a ^ t * C := mul_le_mul_of_nonneg_left
            (partialInterleavedSum_univ_step_bounds i H hH0 hHC t).2 (pow_nonneg ha0.le t)
      _ = C * a ^ t := mul_comm _ _

private lemma discChargeSum_bounds {k : ℕ} (i : Fin k) {a C : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (H : Fin k → ℕ → ℝ)
    (hH0 : ∀ j u, 0 ≤ H j u) (hHC : ∀ j u, H j u ≤ C) :
    0 ≤ discChargeSum a H ∧ discChargeSum a H ≤ C / (1 - a) := by
  unfold discChargeSum
  have hs := summable_discChargeSum_terms i ha0 ha1 H hH0 hHC
  constructor
  · exact tsum_nonneg fun t ↦ mul_nonneg (pow_nonneg ha0.le t)
      (partialInterleavedSum_univ_step_bounds i H hH0 hHC t).1
  · calc ∑' t : ℕ, a ^ t * (partialInterleavedSum H Finset.univ (t + 1) -
            partialInterleavedSum H Finset.univ t)
        ≤ ∑' t : ℕ, C * a ^ t := by
          refine hs.tsum_le_tsum (fun t ↦ ?_) ((summable_geometric_of_lt_one ha0.le ha1).mul_left C)
          calc a ^ t * (partialInterleavedSum H Finset.univ (t + 1) -
                  partialInterleavedSum H Finset.univ t)
              ≤ a ^ t * C := mul_le_mul_of_nonneg_left
                  (partialInterleavedSum_univ_step_bounds i H hH0 hHC t).2 (pow_nonneg ha0.le t)
            _ = C * a ^ t := mul_comm _ _
      _ = C / (1 - a) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one ha0.le ha1, div_eq_mul_inv]

private lemma discChargeSum_eq_abel {k : ℕ} (i : Fin k) {a C : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (H : Fin k → ℕ → ℝ)
    (hH0 : ∀ j u, 0 ≤ H j u) (hHC : ∀ j u, H j u ≤ C) :
    discChargeSum a H = (1 - a) * ∑' t : ℕ, a ^ t * partialInterleavedSum H Finset.univ (t + 1) := by
  exact abel_tsum_eq ha0 ha1 (fun t ↦ partialInterleavedSum H Finset.univ t)
    (partialInterleavedSum_univ_zero H)
    (partialInterleavedSum_univ_nonneg i H hH0)
    (partialInterleavedSum_univ_le_mul i H hHC)
    (summable_discChargeSum_terms i ha0 ha1 H hH0 hHC)

private lemma abel_shift_bound {a C M : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ)
    (U U' : ℕ → ℝ)
    (hU0 : ∀ t, 0 ≤ U t) (hUM : ∀ t, U t ≤ (t : ℝ) * M)
    (hU'0 : ∀ t, 0 ≤ U' t) (hU'C : ∀ t, U' t ≤ (t : ℝ) * C)
    (hstep : ∀ s, U (N + (s + 1)) ≤ (N : ℝ) * M + U' (s + 1)) :
    (1 - a) * ∑' t : ℕ, a ^ t * U (t + 1) ≤
      M * (∑ t ∈ Finset.range N, a ^ t) + a ^ N * ((1 - a) * ∑' t : ℕ, a ^ t * U' (t + 1)) := by
  have hsU : Summable (fun t : ℕ ↦ a ^ t * U (t + 1)) := by
    refine Summable.of_nonneg_of_le (fun t ↦ mul_nonneg (pow_nonneg ha0.le t) (hU0 (t + 1)))
      (fun t ↦ ?_) ((summable_nat_succ_mul_pow ha0 ha1).mul_left M)
    calc a ^ t * U (t + 1) ≤ a ^ t * (((t + 1 : ℕ) : ℝ) * M) :=
          mul_le_mul_of_nonneg_left (hUM (t + 1)) (pow_nonneg ha0.le t)
      _ = M * (((t : ℝ) + 1) * a ^ t) := by push_cast; ring
  have hsU' : Summable (fun t : ℕ ↦ a ^ t * U' (t + 1)) := by
    refine Summable.of_nonneg_of_le (fun t ↦ mul_nonneg (pow_nonneg ha0.le t) (hU'0 (t + 1)))
      (fun t ↦ ?_) ((summable_nat_succ_mul_pow ha0 ha1).mul_left C)
    calc a ^ t * U' (t + 1) ≤ a ^ t * (((t + 1 : ℕ) : ℝ) * C) :=
          mul_le_mul_of_nonneg_left (hU'C (t + 1)) (pow_nonneg ha0.le t)
      _ = C * (((t : ℝ) + 1) * a ^ t) := by push_cast; ring
  rw [← hsU.sum_add_tsum_nat_add N]
  have hhead : ∑ t ∈ Finset.range N, a ^ t * U (t + 1) ≤
      M * ∑ t ∈ Finset.range N, ((t : ℝ) + 1) * a ^ t := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ ↦ ?_
    calc a ^ t * U (t + 1) ≤ a ^ t * (((t + 1 : ℕ) : ℝ) * M) :=
          mul_le_mul_of_nonneg_left (hUM (t + 1)) (pow_nonneg ha0.le t)
      _ = M * (((t : ℝ) + 1) * a ^ t) := by push_cast; ring
  have hs_shift : Summable (fun s : ℕ ↦ a ^ (s + N) * U (s + N + 1)) :=
    (summable_nat_add_iff N).2 hsU
  have hs_rhs1 : Summable (fun s : ℕ ↦ (a ^ N * ((N : ℝ) * M)) * a ^ s) :=
    (summable_geometric_of_lt_one ha0.le ha1).mul_left _
  have hs_rhs2 : Summable (fun s : ℕ ↦ a ^ N * (a ^ s * U' (s + 1))) :=
    hsU'.mul_left _
  have htail : ∑' s : ℕ, a ^ (s + N) * U (s + N + 1) ≤
      (a ^ N * ((N : ℝ) * M)) / (1 - a) + a ^ N * ∑' s : ℕ, a ^ s * U' (s + 1) := by
    calc ∑' s : ℕ, a ^ (s + N) * U (s + N + 1)
        ≤ ∑' s : ℕ, ((a ^ N * ((N : ℝ) * M)) * a ^ s + a ^ N * (a ^ s * U' (s + 1))) := by
          refine hs_shift.tsum_le_tsum (fun s ↦ ?_) (hs_rhs1.add hs_rhs2)
          have hpow : a ^ (s + N) = a ^ N * a ^ s := by rw [add_comm, pow_add]
          have hidx : s + N + 1 = N + (s + 1) := by omega
          rw [hpow, hidx]
          calc a ^ N * a ^ s * U (N + (s + 1))
              ≤ a ^ N * a ^ s * ((N : ℝ) * M + U' (s + 1)) :=
                mul_le_mul_of_nonneg_left (hstep s) (mul_nonneg (pow_nonneg ha0.le N) (pow_nonneg ha0.le s))
            _ = (a ^ N * ((N : ℝ) * M)) * a ^ s + a ^ N * (a ^ s * U' (s + 1)) := by ring
      _ = (∑' s : ℕ, (a ^ N * ((N : ℝ) * M)) * a ^ s) +
            ∑' s : ℕ, a ^ N * (a ^ s * U' (s + 1)) := hs_rhs1.tsum_add hs_rhs2
      _ = (a ^ N * ((N : ℝ) * M)) / (1 - a) + a ^ N * ∑' s : ℕ, a ^ s * U' (s + 1) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one ha0.le ha1, div_eq_mul_inv, tsum_mul_left]
  have h1a : 0 < 1 - a := sub_pos.2 ha1
  have h1a_ne : 1 - a ≠ 0 := h1a.ne'
  set S1 : ℝ := ∑ t ∈ Finset.range N, ((t : ℝ) + 1) * a ^ t
  set S2 : ℝ := ∑' s : ℕ, a ^ s * U' (s + 1)
  calc (1 - a) * (∑ t ∈ Finset.range N, a ^ t * U (t + 1) +
        ∑' s : ℕ, a ^ (s + N) * U (s + N + 1))
      ≤ (1 - a) * (M * S1 + ((a ^ N * ((N : ℝ) * M)) / (1 - a) + a ^ N * S2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hhead htail) h1a.le
    _ = (1 - a) * (M * S1) + (1 - a) * ((a ^ N * ((N : ℝ) * M)) / (1 - a)) +
          (1 - a) * (a ^ N * S2) := by ring
    _ = (1 - a) * (M * S1) + a ^ N * ((N : ℝ) * M) + (1 - a) * (a ^ N * S2) := by
        rw [mul_div_cancel₀ _ h1a_ne]
    _ = M * ((1 - a) * S1 + (N : ℝ) * a ^ N) + a ^ N * ((1 - a) * S2) := by ring
    _ = M * (∑ t ∈ Finset.range N, a ^ t) + a ^ N * ((1 - a) * S2) := by
        rw [geom_weight_identity]

private lemma discChargeSum_le_shift_nat {k : ℕ} (i : Fin k) {a C M : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) (H H' : Fin k → ℕ → ℝ)
    (hH0 : ∀ j u, 0 ≤ H j u) (hHM : ∀ j u, H j u ≤ M)
    (hH'0 : ∀ j u, 0 ≤ H' j u) (hH'C : ∀ j u, H' j u ≤ C)
    (hH'_ne : ∀ j, j ≠ i → ∀ u, H' j u = H j u)
    (hH'_i : ∀ u, H i (N + u) ≤ H' i u) :
    discChargeSum a H ≤ M * (∑ t ∈ Finset.range N, a ^ t) + a ^ N * discChargeSum a H' := by
  rw [discChargeSum_eq_abel i ha0 ha1 H hH0 hHM,
      discChargeSum_eq_abel i ha0 ha1 H' hH'0 hH'C]
  exact abel_shift_bound ha0 ha1 N
    (fun t ↦ partialInterleavedSum H Finset.univ t)
    (fun t ↦ partialInterleavedSum H' Finset.univ t)
    (partialInterleavedSum_univ_nonneg i H hH0)
    (partialInterleavedSum_univ_le_mul i H hHM)
    (partialInterleavedSum_univ_nonneg i H' hH'0)
    (partialInterleavedSum_univ_le_mul i H' hH'C)
    (fun s ↦ partialInterleavedSum_univ_add_le i N (s + 1) H H' hHM hH'_ne hH'_i)

private lemma discChargeSum_le_top {k : ℕ} (i : Fin k) {a M : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (H : Fin k → ℕ → ℝ)
    (hH0 : ∀ j u, 0 ≤ H j u) (hHM : ∀ j u, H j u ≤ M) :
    discChargeSum a H ≤ M * ∑' t : ℕ, a ^ t := by
  rw [discChargeSum_eq_abel i ha0 ha1 H hH0 hHM]
  have hsH : Summable (fun t : ℕ ↦ a ^ t * partialInterleavedSum H Finset.univ (t + 1)) := by
    refine Summable.of_nonneg_of_le
      (fun t ↦ mul_nonneg (pow_nonneg ha0.le t) (partialInterleavedSum_univ_nonneg i H hH0 (t + 1)))
      (fun t ↦ ?_) ((summable_nat_succ_mul_pow ha0 ha1).mul_left M)
    calc a ^ t * partialInterleavedSum H Finset.univ (t + 1)
        ≤ a ^ t * (((t + 1 : ℕ) : ℝ) * M) :=
          mul_le_mul_of_nonneg_left (partialInterleavedSum_univ_le_mul i H hHM (t + 1)) (pow_nonneg ha0.le t)
      _ = M * (((t : ℝ) + 1) * a ^ t) := by push_cast; ring
  have hle : ∑' t : ℕ, a ^ t * partialInterleavedSum H Finset.univ (t + 1) ≤
      M * ∑' t : ℕ, ((t : ℝ) + 1) * a ^ t := by
    rw [← tsum_mul_left]
    refine hsH.tsum_le_tsum (fun t ↦ ?_) ((summable_nat_succ_mul_pow ha0 ha1).mul_left M)
    calc a ^ t * partialInterleavedSum H Finset.univ (t + 1)
        ≤ a ^ t * (((t + 1 : ℕ) : ℝ) * M) :=
          mul_le_mul_of_nonneg_left (partialInterleavedSum_univ_le_mul i H hHM (t + 1)) (pow_nonneg ha0.le t)
      _ = M * (((t : ℝ) + 1) * a ^ t) := by push_cast; ring
  calc (1 - a) * ∑' t : ℕ, a ^ t * partialInterleavedSum H Finset.univ (t + 1)
      ≤ (1 - a) * (M * ∑' t : ℕ, ((t : ℝ) + 1) * a ^ t) :=
        mul_le_mul_of_nonneg_left hle (sub_pos.2 ha1).le
    _ = M * ((1 - a) * ∑' t : ℕ, ((t : ℝ) + 1) * a ^ t) := by ring
    _ = M * ∑' t : ℕ, a ^ t := by rw [geom_weight_tsum ha0 ha1]

end CombinatorialBound

section ShiftInvarianceAndValue

variable {T : Type*} [MeasurableSpace T] [Countable T] [MeasurableSingletonClass T]

private lemma measurable_of_countable_T {α : Type*} [MeasurableSpace α] (f : T → α) :
    Measurable f :=
  fun _ _ ↦ MeasurableSet.of_discrete

private lemma markovBanditRoundReward_bound (P : Kernel T T) [IsMarkovKernel P]
    {r : T → ℝ} {M : ℝ} (hM : ∀ y, |r y| ≤ M) {k : ℕ} (π : MarkovBanditPolicy k T)
    (x : Fin k → T) (t : ℕ) :
    |markovBanditRoundReward P r π x t| ≤ M := by
  unfold markovBanditRoundReward
  calc |∫ h, r ((h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2)) ∂markovBanditMeasure P π x (t + 1)|
      = ‖∫ h, r ((h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2)) ∂markovBanditMeasure P π x (t + 1)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ M * (markovBanditMeasure P π x (t + 1)).real Set.univ :=
        norm_integral_le_of_norm_le_const (ae_of_all _ fun h ↦ by
          rw [Real.norm_eq_abs]; exact hM _)
    _ = M := by simp

private lemma markovBanditRoundReward_add_const (P : Kernel T T) [IsMarkovKernel P]
    {r : T → ℝ} (hr : BoundedReward r) (c : ℝ) {k : ℕ} (π : MarkovBanditPolicy k T)
    (x : Fin k → T) (t : ℕ) :
    markovBanditRoundReward P (fun y ↦ r y + c) π x t =
      markovBanditRoundReward P r π x t + c := by
  obtain ⟨M, hM⟩ := hr
  unfold markovBanditRoundReward
  have hm : Measurable (fun h : MarkovBanditHistory k T (t + 1) ↦
      r ((h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2))) := by
    have h1 : Measurable (fun h : MarkovBanditHistory k T (t + 1) ↦
        (h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2)) := by
      have hm1 : Measurable (fun h : MarkovBanditHistory k T (t + 1) ↦ h.1 (Fin.last t)) :=
        (measurable_pi_apply (Fin.last t)).comp measurable_fst
      have hm2 : Measurable (fun p : (Fin k → T) × Fin k ↦ p.1 p.2) :=
        measurable_from_prod_countable_left fun j ↦ measurable_pi_apply j
      exact hm2.comp hm1
    exact (measurable_of_countable_T r).comp h1
  have hint : Integrable (fun h : MarkovBanditHistory k T (t + 1) ↦
      r ((h.1 (Fin.last t)).1 ((h.1 (Fin.last t)).2))) (markovBanditMeasure P π x (t + 1)) :=
    Integrable.of_bound hm.aestronglyMeasurable M
      (ae_of_all _ fun h ↦ by rw [Real.norm_eq_abs]; exact hM _)
  rw [integral_add hint (integrable_const c)]
  simp

private lemma markovBanditDiscountedValue_add_const (P : Kernel T T) [IsMarkovKernel P]
    {r : T → ℝ} (hr : BoundedReward r) (c : ℝ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {k : ℕ} (π : MarkovBanditPolicy k T) (x : Fin k → T) :
    markovBanditDiscountedValue P (fun y ↦ r y + c) a π x =
      markovBanditDiscountedValue P r a π x + c / (1 - a) := by
  obtain ⟨M, hM⟩ := hr
  have hs_r : Summable (fun t : ℕ ↦ a ^ t * markovBanditRoundReward P r π x t) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0.le ha1).mul_left M) fun t ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0.le t)]
    calc a ^ t * |markovBanditRoundReward P r π x t| ≤ a ^ t * M :=
          mul_le_mul_of_nonneg_left (markovBanditRoundReward_bound P hM π x t) (pow_nonneg ha0.le t)
      _ = M * a ^ t := mul_comm _ _
  have hs_c : Summable (fun t : ℕ ↦ a ^ t * c) :=
    (summable_geometric_of_lt_one ha0.le ha1).mul_right c
  unfold markovBanditDiscountedValue
  simp_rw [markovBanditRoundReward_add_const P ⟨M, hM⟩ c π x, mul_add]
  rw [hs_r.tsum_add hs_c, tsum_mul_right, tsum_geometric_of_lt_one ha0.le ha1, div_eq_mul_inv, mul_comm]

private lemma markovBanditDiscountedValue_abs_le (P : Kernel T T) [IsMarkovKernel P]
    {r : T → ℝ} {M : ℝ} (hM : ∀ y, |r y| ≤ M) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {k : ℕ} (π : MarkovBanditPolicy k T) (x : Fin k → T) :
    |markovBanditDiscountedValue P r a π x| ≤ M / (1 - a) := by
  have hs_abs : Summable (fun t : ℕ ↦ ‖a ^ t * markovBanditRoundReward P r π x t‖) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun t ↦ ?_)
      ((summable_geometric_of_lt_one ha0.le ha1).mul_left M)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0.le t)]
    calc a ^ t * |markovBanditRoundReward P r π x t| ≤ a ^ t * M :=
          mul_le_mul_of_nonneg_left (markovBanditRoundReward_bound P hM π x t) (pow_nonneg ha0.le t)
      _ = M * a ^ t := mul_comm _ _
  unfold markovBanditDiscountedValue
  calc |∑' t : ℕ, a ^ t * markovBanditRoundReward P r π x t|
      = ‖∑' t : ℕ, a ^ t * markovBanditRoundReward P r π x t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' t : ℕ, ‖a ^ t * markovBanditRoundReward P r π x t‖ := norm_tsum_le_tsum_norm hs_abs
    _ ≤ ∑' t : ℕ, M * a ^ t := by
        refine hs_abs.tsum_le_tsum (fun t ↦ ?_) ((summable_geometric_of_lt_one ha0.le ha1).mul_left M)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0.le t)]
        calc a ^ t * |markovBanditRoundReward P r π x t| ≤ a ^ t * M :=
              mul_le_mul_of_nonneg_left (markovBanditRoundReward_bound P hM π x t) (pow_nonneg ha0.le t)
          _ = M * a ^ t := mul_comm _ _
    _ = M / (1 - a) := by rw [tsum_mul_left, tsum_geometric_of_lt_one ha0.le ha1, div_eq_mul_inv]

private lemma nonempty_markovBanditPolicy {k : ℕ} (i : Fin k) :
    Nonempty (MarkovBanditPolicy k T) :=
  ⟨⟨fun _ ↦ Kernel.const _ (Measure.dirac i), fun _ ↦ inferInstance⟩⟩

private lemma bddAbove_markovBanditDiscountedValue (P : Kernel T T) [IsMarkovKernel P]
    {r : T → ℝ} (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {k : ℕ} (x : Fin k → T) :
    BddAbove (Set.range fun π : MarkovBanditPolicy k T ↦ markovBanditDiscountedValue P r a π x) := by
  obtain ⟨M, hM⟩ := hr
  refine ⟨M / (1 - a), ?_⟩
  rintro _ ⟨π, rfl⟩
  exact (le_abs_self _).trans (markovBanditDiscountedValue_abs_le P hM ha0 ha1 π x)

private lemma iSup_markovBanditDiscountedValue_abs_le (P : Kernel T T) [IsMarkovKernel P]
    {r : T → ℝ} {M : ℝ} (hM : ∀ y, |r y| ≤ M) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {k : ℕ} (i : Fin k) (x : Fin k → T) :
    |⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π x| ≤ M / (1 - a) := by
  have : Nonempty (MarkovBanditPolicy k T) := nonempty_markovBanditPolicy i
  have hbdd := bddAbove_markovBanditDiscountedValue P ⟨M, hM⟩ ha0 ha1 x
  rw [abs_le]
  constructor
  · obtain ⟨π₀⟩ := ‹Nonempty (MarkovBanditPolicy k T)›
    have h1 := (abs_le.1 (markovBanditDiscountedValue_abs_le P hM ha0 ha1 π₀ x)).1
    exact h1.trans (le_ciSup hbdd π₀)
  · exact ciSup_le fun π ↦ (abs_le.1 (markovBanditDiscountedValue_abs_le P hM ha0 ha1 π x)).2

private lemma iSup_markovBanditDiscountedValue_add_const (P : Kernel T T) [IsMarkovKernel P]
    {r : T → ℝ} (hr : BoundedReward r) (c : ℝ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {k : ℕ} (i : Fin k) (x : Fin k → T) :
    (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P (fun y ↦ r y + c) a π x) =
      (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π x) + c / (1 - a) := by
  have : Nonempty (MarkovBanditPolicy k T) := nonempty_markovBanditPolicy i
  have hbdd := bddAbove_markovBanditDiscountedValue P hr ha0 ha1 x
  have hr' : BoundedReward (fun y ↦ r y + c) := by
    obtain ⟨M, hM⟩ := hr
    exact ⟨M + |c|, fun y ↦ (abs_add_le _ _).trans (add_le_add (hM y) le_rfl)⟩
  have hbdd' := bddAbove_markovBanditDiscountedValue P hr' ha0 ha1 x
  apply le_antisymm
  · refine ciSup_le fun π ↦ ?_
    rw [markovBanditDiscountedValue_add_const P hr c ha0 ha1 π x]
    exact add_le_add (le_ciSup hbdd π) le_rfl
  · rw [← le_sub_iff_add_le]
    refine ciSup_le fun π ↦ ?_
    rw [le_sub_iff_add_le, ← markovBanditDiscountedValue_add_const P hr c ha0 ha1 π x]
    exact le_ciSup hbdd' π

private lemma measurable_stopping_time {τ : (ℕ → T) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    Measurable τ := by
  refine measurable_to_countable' fun v ↦ ?_
  have hle_m : ∀ n : ℕ, MeasurableSet {ω : ℕ → T | τ ω ≤ (n : ℕ∞)} := fun n ↦ by
    have hproj : Measurable (fun (ω : ℕ → T) (j : Finset.Iic n) ↦ ω j.1) :=
      measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1
    exact hproj.comap_le _ (hτ n)
  cases v with
  | coe n =>
    cases n with
    | zero =>
      have : τ ⁻¹' {((0 : ℕ) : ℕ∞)} = {ω | τ ω ≤ ((0 : ℕ) : ℕ∞)} := by ext ω; simp
      rw [this]; exact hle_m 0
    | succ m =>
      have : τ ⁻¹' {((m + 1 : ℕ) : ℕ∞)} =
          {ω | τ ω ≤ ((m + 1 : ℕ) : ℕ∞)} \ {ω | τ ω ≤ (m : ℕ∞)} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq]
        cases τ ω with
        | top =>
          simp only [top_le_iff, ENat.natCast_ne_top, false_and, iff_false]
          exact ENat.top_ne_coe (m + 1)
        | coe u =>
          norm_cast
          omega
      rw [this]
      exact (hle_m (m + 1)).diff (hle_m m)
  | top =>
    have : τ ⁻¹' {(⊤ : ℕ∞)} = (⋃ n : ℕ, {ω | τ ω ≤ (n : ℕ∞)})ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        Set.mem_setOf_eq, not_exists]
      cases τ ω with
      | top => simp
      | coe u =>
        simp only [ENat.coe_ne_top, false_iff, not_forall, not_not]
        exact ⟨u, le_rfl⟩
    rw [this]
    exact (MeasurableSet.iUnion hle_m).compl

private lemma summable_discountedStoppedSum_terms {a M : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {f : T → ℝ} (hf : ∀ y, |f y| ≤ M) (τ : (ℕ → T) → ℕ∞) (ω : ℕ → T) :
    Summable (fun t : ℕ ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0.le ha1).mul_left M) fun t ↦ ?_
  split_ifs
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0.le t)]
    calc a ^ t * |f (ω t)| ≤ a ^ t * M := mul_le_mul_of_nonneg_left (hf (ω t)) (pow_nonneg ha0.le t)
      _ = M * a ^ t := mul_comm _ _
  · rw [norm_zero]
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hf (ω 0))
    exact mul_nonneg hM0 (pow_nonneg ha0.le t)

private lemma measurable_discountedStoppedSum {a M : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {f : T → ℝ} (hf : ∀ y, |f y| ≤ M) {τ : (ℕ → T) → ℕ∞} (hτ : IsTrajStoppingTime τ) :
    Measurable (discountedStoppedSum a f τ) := by
  have hτm : Measurable τ := measurable_stopping_time hτ
  have hterm : ∀ t : ℕ, Measurable (fun ω : ℕ → T ↦ if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0) := by
    intro t
    refine Measurable.ite ?_ ?_ measurable_const
    · have : {ω : ℕ → T | (t : ℕ∞) < τ ω} = τ ⁻¹' Set.Ioi (t : ℕ∞) := rfl
      rw [this]
      exact hτm (MeasurableSet.of_discrete)
    · exact measurable_const.mul ((measurable_of_countable_T f).comp (measurable_pi_apply t))
  refine measurable_of_tendsto_metrizable
    (f := fun N ω ↦ ∑ t ∈ Finset.range N, if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0)
    (fun N ↦ Finset.measurable_sum _ fun t _ ↦ hterm t) ?_
  rw [tendsto_pi_nhds]
  intro ω
  exact (summable_discountedStoppedSum_terms ha0 ha1 hf τ ω).hasSum.tendsto_sum_nat

private lemma abs_discountedStoppedSum_le {a M : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {f : T → ℝ} (hf : ∀ y, |f y| ≤ M) (τ : (ℕ → T) → ℕ∞) (ω : ℕ → T) :
    |discountedStoppedSum a f τ ω| ≤ M * discountedStoppedSum a (fun _ ↦ 1) τ ω := by
  have hs1 := summable_discountedStoppedSum_terms ha0 ha1 hf τ ω
  have hs2 := summable_discountedStoppedSum_terms ha0 ha1 (f := fun _ ↦ (1 : ℝ))
    (M := 1) (fun _ ↦ by norm_num) τ ω
  have hsn : Summable (fun t : ℕ ↦ ‖if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0‖) := hs1.norm
  unfold discountedStoppedSum
  calc |∑' t : ℕ, if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0|
      = ‖∑' t : ℕ, if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' t : ℕ, ‖if (t : ℕ∞) < τ ω then a ^ t * f (ω t) else 0‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' t : ℕ, M * (if (t : ℕ∞) < τ ω then a ^ t * 1 else 0) := by
        refine hsn.tsum_le_tsum (fun t ↦ ?_) (hs2.mul_left M)
        split_ifs
        · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0.le t), mul_one]
          calc a ^ t * |f (ω t)| ≤ a ^ t * M := mul_le_mul_of_nonneg_left (hf (ω t)) (pow_nonneg ha0.le t)
            _ = M * a ^ t := mul_comm _ _
        · simp
    _ = M * ∑' t : ℕ, if (t : ℕ∞) < τ ω then a ^ t * 1 else 0 := tsum_mul_left

private lemma discountedStoppedSum_one_ge_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {τ : (ℕ → T) → ℕ∞} (hτ1 : ∀ ω, 1 ≤ τ ω) (ω : ℕ → T) :
    1 ≤ discountedStoppedSum a (fun _ ↦ 1) τ ω := by
  rw [discountedStoppedSum_one_eq_div ha0 ha1]
  have hle : discountPow a (τ ω) ≤ a := discountPow_le_of_one_le ha0.le ha1.le (hτ1 ω)
  have h1a : 0 < 1 - a := sub_pos.2 ha1
  rw [one_le_div h1a]
  linarith

private lemma discountedStoppedSum_one_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (τ : (ℕ → T) → ℕ∞) (ω : ℕ → T) :
    discountedStoppedSum a (fun _ ↦ 1) τ ω ≤ 1 / (1 - a) := by
  rw [discountedStoppedSum_one_eq_div ha0 ha1]
  have h0 : 0 ≤ discountPow a (τ ω) := discountPow_nonneg ha0.le (τ ω)
  exact div_le_div_of_nonneg_right (by linarith) (sub_pos.2 ha1).le

private lemma isTrajStoppingTime_const_one :
    IsTrajStoppingTime (fun _ : ℕ → T ↦ (1 : ℕ∞)) := by
  intro n
  cases n with
  | zero =>
    have : {ω : ℕ → T | (1 : ℕ∞) ≤ ((0 : ℕ) : ℕ∞)} = ∅ := by ext ω; simp
    change MeasurableSet[trajectoryFiltration T 0] {ω : ℕ → T | (1 : ℕ∞) ≤ ((0 : ℕ) : ℕ∞)}
    rw [this]; exact @MeasurableSet.empty _ (trajectoryFiltration T 0)
  | succ m =>
    have : {ω : ℕ → T | (1 : ℕ∞) ≤ ((m + 1 : ℕ) : ℕ∞)} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact_mod_cast Nat.succ_pos m
    change MeasurableSet[trajectoryFiltration T (m + 1)] {ω : ℕ → T | (1 : ℕ∞) ≤ ((m + 1 : ℕ) : ℕ∞)}
    rw [this]; exact @MeasurableSet.univ _ (trajectoryFiltration T (m + 1))

private lemma gittinsIndex_add_const (P : Kernel T T) [IsMarkovKernel P]
    {r : T → ℝ} (hr : BoundedReward r) (c : ℝ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (y : T) :
    gittinsIndex P (fun z ↦ r z + c) a y = gittinsIndex P r a y + c := by
  obtain ⟨M, hM⟩ := hr
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM y)
  have h1a : 0 < 1 - a := sub_pos.2 ha1
  have hratio : ∀ (τ : (ℕ → T) → ℕ∞), IsTrajStoppingTime τ → (∀ ω, 1 ≤ τ ω) →
      (∫ ω, discountedStoppedSum a (fun z ↦ r z + c) τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y) =
      (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y) + c := by
    intro τ hτ hτ1
    have hsplit : ∀ ω, discountedStoppedSum a (fun z ↦ r z + c) τ ω =
        discountedStoppedSum a r τ ω + c * discountedStoppedSum a (fun _ ↦ 1) τ ω := by
      intro ω
      unfold discountedStoppedSum
      have hs1 := summable_discountedStoppedSum_terms ha0 ha1 hM τ ω
      have hs2 := summable_discountedStoppedSum_terms ha0 ha1 (f := fun _ ↦ (1 : ℝ))
        (M := 1) (fun _ ↦ by norm_num) τ ω
      rw [← tsum_mul_left, ← hs1.tsum_add (hs2.mul_left c)]
      congr 1; funext t
      split_ifs <;> ring
    have hint1 : Integrable (discountedStoppedSum a r τ) (markovChainMeasure P y) := by
      refine Integrable.of_bound (measurable_discountedStoppedSum ha0 ha1 hM hτ).aestronglyMeasurable
        (M / (1 - a)) (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs]
      calc |discountedStoppedSum a r τ ω| ≤ M * discountedStoppedSum a (fun _ ↦ 1) τ ω :=
            abs_discountedStoppedSum_le ha0 ha1 hM τ ω
        _ ≤ M * (1 / (1 - a)) := mul_le_mul_of_nonneg_left (discountedStoppedSum_one_le ha0 ha1 τ ω) hM0
        _ = M / (1 - a) := by ring
    have hint2 : Integrable (discountedStoppedSum a (fun _ ↦ 1) τ) (markovChainMeasure P y) := by
      refine Integrable.of_bound
        (measurable_discountedStoppedSum ha0 ha1 (f := fun _ ↦ (1 : ℝ)) (M := 1)
          (fun _ ↦ by norm_num) hτ).aestronglyMeasurable
        (1 / (1 - a)) (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (discountedStoppedSum_one_ge_one ha0 ha1 hτ1 ω))]
      exact discountedStoppedSum_one_le ha0 ha1 τ ω
    have hW_ge : 1 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y := by
      calc (1 : ℝ) = ∫ _ω, (1 : ℝ) ∂markovChainMeasure P y := by simp
        _ ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y :=
          integral_mono (integrable_const 1) hint2 (discountedStoppedSum_one_ge_one ha0 ha1 hτ1)
    have hW_ne : ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y ≠ 0 := by linarith
    simp_rw [hsplit]
    rw [integral_add hint1 (hint2.const_mul c), integral_const_mul, add_div, mul_div_cancel_right₀ _ hW_ne]
  have hle_M : ∀ (τ : (ℕ → T) → ℕ∞), IsTrajStoppingTime τ → (∀ ω, 1 ≤ τ ω) →
      (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y) ≤ M := by
    intro τ hτ hτ1
    have hint1 : Integrable (discountedStoppedSum a r τ) (markovChainMeasure P y) := by
      refine Integrable.of_bound (measurable_discountedStoppedSum ha0 ha1 hM hτ).aestronglyMeasurable
        (M / (1 - a)) (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs]
      calc |discountedStoppedSum a r τ ω| ≤ M * discountedStoppedSum a (fun _ ↦ 1) τ ω :=
            abs_discountedStoppedSum_le ha0 ha1 hM τ ω
        _ ≤ M * (1 / (1 - a)) := mul_le_mul_of_nonneg_left (discountedStoppedSum_one_le ha0 ha1 τ ω) hM0
        _ = M / (1 - a) := by ring
    have hint2 : Integrable (discountedStoppedSum a (fun _ ↦ 1) τ) (markovChainMeasure P y) := by
      refine Integrable.of_bound
        (measurable_discountedStoppedSum ha0 ha1 (f := fun _ ↦ (1 : ℝ)) (M := 1)
          (fun _ ↦ by norm_num) hτ).aestronglyMeasurable
        (1 / (1 - a)) (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (discountedStoppedSum_one_ge_one ha0 ha1 hτ1 ω))]
      exact discountedStoppedSum_one_le ha0 ha1 τ ω
    have hW_pos : 0 < ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y := by
      have hge : 1 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y := by
        calc (1 : ℝ) = ∫ _ω, (1 : ℝ) ∂markovChainMeasure P y := by simp
          _ ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y :=
            integral_mono (integrable_const 1) hint2 (discountedStoppedSum_one_ge_one ha0 ha1 hτ1)
      linarith
    rw [div_le_iff₀ hW_pos, ← integral_const_mul]
    exact integral_mono hint1 (hint2.const_mul M) fun ω ↦
      (le_abs_self _).trans (abs_discountedStoppedSum_le ha0 ha1 hM τ ω)
  unfold gittinsIndex
  set S1 : Set ℝ := {g : ℝ | ∃ τ : (ℕ → T) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
    g = (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)}
  set S2 : Set ℝ := {g : ℝ | ∃ τ : (ℕ → T) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
    g = (∫ ω, discountedStoppedSum a (fun z ↦ r z + c) τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)}
  have hS1_ne : S1.Nonempty := ⟨_, fun _ ↦ 1, isTrajStoppingTime_const_one, fun _ ↦ le_rfl, rfl⟩
  have hS2_ne : S2.Nonempty := ⟨_, fun _ ↦ 1, isTrajStoppingTime_const_one, fun _ ↦ le_rfl, rfl⟩
  have hS1_bdd : BddAbove S1 := ⟨M, by rintro _ ⟨τ, hτ, hτ1, rfl⟩; exact hle_M τ hτ hτ1⟩
  have hS2_bdd : BddAbove S2 := ⟨M + c, by
    rintro _ ⟨τ, hτ, hτ1, rfl⟩
    rw [hratio τ hτ hτ1]
    exact add_le_add (hle_M τ hτ hτ1) le_rfl⟩
  apply le_antisymm
  · refine csSup_le hS2_ne ?_
    rintro _ ⟨τ, hτ, hτ1, rfl⟩
    rw [hratio τ hτ hτ1]
    exact add_le_add (le_csSup hS1_bdd ⟨τ, hτ, hτ1, rfl⟩) le_rfl
  · rw [← le_sub_iff_add_le]
    refine csSup_le hS1_ne ?_
    rintro _ ⟨τ, hτ, hτ1, rfl⟩
    rw [le_sub_iff_add_le, ← hratio τ hτ hτ1]
    exact le_csSup hS2_bdd ⟨τ, hτ, hτ1, rfl⟩

private lemma gittinsIndex_bounds_nonneg (P : Kernel T T) [IsMarkovKernel P]
    {r : T → ℝ} {C : ℝ} (h0 : ∀ y, 0 ≤ r y) (hC : ∀ y, r y ≤ C)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (y : T) :
    0 ≤ gittinsIndex P r a y ∧ gittinsIndex P r a y ≤ C := by
  have hC0 : 0 ≤ C := le_trans (h0 y) (hC y)
  have habs : ∀ z, |r z| ≤ C := fun z ↦ by rw [abs_of_nonneg (h0 z)]; exact hC z
  have hbound : ∀ (τ : (ℕ → T) → ℕ∞), IsTrajStoppingTime τ → (∀ ω, 1 ≤ τ ω) →
      0 ≤ (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y) ∧
      (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y) ≤ C := by
    intro τ hτ hτ1
    have hint1 : Integrable (discountedStoppedSum a r τ) (markovChainMeasure P y) := by
      refine Integrable.of_bound (measurable_discountedStoppedSum ha0 ha1 habs hτ).aestronglyMeasurable
        (C / (1 - a)) (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs]
      calc |discountedStoppedSum a r τ ω| ≤ C * discountedStoppedSum a (fun _ ↦ 1) τ ω :=
            abs_discountedStoppedSum_le ha0 ha1 habs τ ω
        _ ≤ C * (1 / (1 - a)) := mul_le_mul_of_nonneg_left (discountedStoppedSum_one_le ha0 ha1 τ ω) hC0
        _ = C / (1 - a) := by ring
    have hint2 : Integrable (discountedStoppedSum a (fun _ ↦ 1) τ) (markovChainMeasure P y) := by
      refine Integrable.of_bound
        (measurable_discountedStoppedSum ha0 ha1 (f := fun _ ↦ (1 : ℝ)) (M := 1)
          (fun _ ↦ by norm_num) hτ).aestronglyMeasurable
        (1 / (1 - a)) (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (discountedStoppedSum_one_ge_one ha0 ha1 hτ1 ω))]
      exact discountedStoppedSum_one_le ha0 ha1 τ ω
    have hW_pos : 0 < ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y := by
      have hge : 1 ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y := by
        calc (1 : ℝ) = ∫ _ω, (1 : ℝ) ∂markovChainMeasure P y := by simp
          _ ≤ ∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y :=
            integral_mono (integrable_const 1) hint2 (discountedStoppedSum_one_ge_one ha0 ha1 hτ1)
      linarith
    have hR_nn : 0 ≤ ∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y := by
      refine integral_nonneg fun ω ↦ tsum_nonneg fun t ↦ ?_
      split_ifs
      · exact mul_nonneg (pow_nonneg ha0.le t) (h0 (ω t))
      · exact le_rfl
    constructor
    · exact div_nonneg hR_nn hW_pos.le
    · rw [div_le_iff₀ hW_pos, ← integral_const_mul]
      exact integral_mono hint1 (hint2.const_mul C) fun ω ↦
        (le_abs_self _).trans (abs_discountedStoppedSum_le ha0 ha1 habs τ ω)
  unfold gittinsIndex
  set S : Set ℝ := {g : ℝ | ∃ τ : (ℕ → T) → ℕ∞, IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
    g = (∫ ω, discountedStoppedSum a r τ ω ∂markovChainMeasure P y) /
        (∫ ω, discountedStoppedSum a (fun _ ↦ 1) τ ω ∂markovChainMeasure P y)}
  have hS_ne : S.Nonempty := ⟨_, fun _ ↦ 1, isTrajStoppingTime_const_one, fun _ ↦ le_rfl, rfl⟩
  have hS_bdd : BddAbove S := ⟨C, by rintro _ ⟨τ, hτ, hτ1, rfl⟩; exact (hbound τ hτ hτ1).2⟩
  constructor
  · exact le_trans (hbound (fun _ ↦ 1) isTrajStoppingTime_const_one (fun _ ↦ le_rfl)).1
      (le_csSup hS_bdd ⟨fun _ ↦ 1, isTrajStoppingTime_const_one, fun _ ↦ le_rfl, rfl⟩)
  · exact csSup_le hS_ne fun g hg ↦ by rcases hg with ⟨τ, hτ, hτ1, rfl⟩; exact (hbound τ hτ hτ1).2

private lemma restrictedValue_univ_eq_aux (P : Kernel T T) [IsMarkovKernel P] (r : T → ℝ) (a : ℝ)
    {k k' : ℕ} (hcard : k' = k) (e : Fin k' ↪o Fin k) (he : ∀ m, e m = Fin.cast hcard m)
    (x : Fin k → T) :
    (⨆ π : MarkovBanditPolicy k' T, markovBanditDiscountedValue P r a π (fun m ↦ x (e m))) =
      ⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π x := by
  subst hcard
  have he' : (fun m ↦ x (e m)) = x := by
    funext m; simp [he m]
  rw [he']

private lemma restrictedValue_univ_eq (P : Kernel T T) [IsMarkovKernel P] (r : T → ℝ) (a : ℝ)
    {k : ℕ} (i : Fin k) (x : Fin k → T) :
    restrictedValue P r a x Finset.univ =
      ⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π x := by
  have hne : (Finset.univ : Finset (Fin k)) ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨i, Finset.mem_univ i⟩
  unfold restrictedValue
  rw [if_neg hne]
  have hcard : (Finset.univ : Finset (Fin k)).card = k := by simp
  have he : ∀ m : Fin (Finset.univ : Finset (Fin k)).card,
      (Finset.univ : Finset (Fin k)).orderEmbOfFin rfl m = Fin.cast hcard m := by
    have huniq := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin k))) (h := rfl)
      (f := fun m ↦ Fin.cast hcard m)
      (fun _ ↦ Finset.mem_univ _)
      (fun _ _ h ↦ h)
    intro m
    exact (congrFun huniq m).symm
  exact restrictedValue_univ_eq_aux P r a hcard ((Finset.univ : Finset (Fin k)).orderEmbOfFin rfl) he x

end ShiftInvarianceAndValue

section MarkovShift

variable {T : Type*} [MeasurableSpace T] [Countable T] [MeasurableSingletonClass T]

private lemma markovChainMeasure_eq_traj (P : Kernel T T) [IsMarkovKernel P] (x₀ : T) :
    markovChainMeasure P x₀ =
      Kernel.traj (X := fun _ : ℕ ↦ T) (markovChainStep P) 0 (fun _ ↦ x₀) := by
  unfold markovChainMeasure Kernel.trajMeasure
  rw [Measure.map_dirac' (MeasurableEquiv.piUnique _).symm.measurable]
  change (Measure.dirac _).bind (Kernel.traj (X := fun _ : ℕ ↦ T) (markovChainStep P) 0) = _
  rw [Measure.dirac_bind (Kernel.measurable _)]
  congr 1

private lemma ae_eval_zero_markovChainMeasure (P : Kernel T T) [IsMarkovKernel P] (x₀ : T) :
    ∀ᵐ ω ∂markovChainMeasure P x₀, ω 0 = x₀ := by
  rw [markovChainMeasure_eq_traj, ae_iff]
  have hmap : (Kernel.traj (X := fun _ : ℕ ↦ T) (markovChainStep P) 0 (fun _ ↦ x₀)).map
      (Preorder.frestrictLe (π := fun _ : ℕ ↦ T) 0) =
      Measure.dirac (fun _ : Finset.Iic 0 ↦ x₀) := by
    rw [Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply]
  have hset : {ω : ℕ → T | ¬ ω 0 = x₀} =
      Preorder.frestrictLe (π := fun _ : ℕ ↦ T) 0 ⁻¹'
        {u : Π _ : Finset.Iic 0, T | u ⟨0, Finset.mem_Iic.2 le_rfl⟩ ≠ x₀} := rfl
  rw [hset]
  have hm0 : Measurable (fun u : Π _ : Finset.Iic 0, T ↦ u ⟨0, Finset.mem_Iic.2 le_rfl⟩) :=
    measurable_pi_apply _
  have hmeas : MeasurableSet {u : Π _ : Finset.Iic 0, T | u ⟨0, Finset.mem_Iic.2 le_rfl⟩ ≠ x₀} :=
    (hm0 (measurableSet_singleton x₀)).compl
  rw [← Measure.map_apply (Preorder.measurable_frestrictLe 0) hmeas, hmap,
    Measure.dirac_apply' _ hmeas]
  simp

private def shiftRestrict (n b : ℕ) (v : Π _ : Finset.Iic (n + b), T) : Π _ : Finset.Iic b, T :=
  fun j ↦ v ⟨n + j.1, Finset.mem_Iic.2 (Nat.add_le_add_left (Finset.mem_Iic.1 j.2) n)⟩

private lemma measurable_shiftRestrict (n b : ℕ) : Measurable (shiftRestrict (T := T) n b) :=
  measurable_pi_lambda _ fun j ↦ measurable_pi_apply _

private lemma partialTraj_map_shiftRestrict (P : Kernel T T) [IsMarkovKernel P] (n : ℕ) :
    ∀ (b : ℕ) (u : Π _ : Finset.Iic n, T),
      (Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) n (n + b) u).map
        (shiftRestrict n b) =
      Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) 0 b
        (fun _ ↦ u ⟨n, Finset.mem_Iic.2 le_rfl⟩) := by
  intro b
  induction b with
  | zero =>
    intro u
    simp only [Nat.add_zero, Kernel.partialTraj_self, Kernel.id_apply]
    rw [Measure.map_dirac' (measurable_shiftRestrict n 0)]
    congr 1
    funext j
    have hj : j.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.1 j.2)
    simp [shiftRestrict, hj]
  | succ b ih =>
    intro u
    have hstepL : Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) n (n + (b + 1)) u =
        (Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) (n + b) (n + b + 1)) ∘ₘ
          (Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) n (n + b) u) := by
      change Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) n ((n + b) + 1) u = _
      rw [Kernel.partialTraj_succ_eq_comp (Nat.le_add_right n b), Kernel.comp_apply]
    have hstepR : Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) 0 (b + 1)
          (fun _ ↦ u ⟨n, Finset.mem_Iic.2 le_rfl⟩) =
        (Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) b (b + 1)) ∘ₘ
          (Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) 0 b
            (fun _ ↦ u ⟨n, Finset.mem_Iic.2 le_rfl⟩)) := by
      rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le b), Kernel.comp_apply]
    rw [hstepL, hstepR, ← ih u]
    have hcomm :
        (Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) (n + b) (n + b + 1)).map
          (shiftRestrict n (b + 1)) =
        (Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) b (b + 1)).comap
          (shiftRestrict n b) (measurable_shiftRestrict n b) := by
      ext v s hs
      have hs1 : MeasurableSet (shiftRestrict (T := T) n (b + 1) ⁻¹' s) :=
        (measurable_shiftRestrict n (b + 1)) hs
      have hm_iic1 : Measurable (IicProdIoc (X := fun _ : ℕ ↦ T) (n + b) (n + b + 1)) := by
        fun_prop
      have hm_iic2 : Measurable (IicProdIoc (X := fun _ : ℕ ↦ T) b (b + 1)) := by
        fun_prop
      have hs1' : MeasurableSet (Prod.mk v ⁻¹' (IicProdIoc (X := fun _ : ℕ ↦ T) (n + b) (n + b + 1) ⁻¹'
          (shiftRestrict (T := T) n (b + 1) ⁻¹' s))) :=
        measurable_prodMk_left (hm_iic1 hs1)
      have hs2' : MeasurableSet (Prod.mk (shiftRestrict (T := T) n b v) ⁻¹'
          (IicProdIoc (X := fun _ : ℕ ↦ T) b (b + 1) ⁻¹' s)) :=
        measurable_prodMk_left (hm_iic2 hs)
      rw [Kernel.map_apply' _ (measurable_shiftRestrict n (b + 1)) _ hs,
          Kernel.comap_apply, Kernel.partialTraj_succ_self, Kernel.partialTraj_succ_self]
      rw [Kernel.map_apply' _ hm_iic1 _ hs1,
          Kernel.map_apply' _ hm_iic2 _ hs]
      rw [Kernel.prod_apply, Kernel.prod_apply, Kernel.id_apply, Kernel.id_apply]
      rw [Measure.dirac_prod, Measure.dirac_prod]
      rw [Measure.map_apply measurable_prodMk_left (hm_iic1 hs1),
          Measure.map_apply measurable_prodMk_left (hm_iic2 hs)]
      rw [Kernel.map_apply' _ (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ T) (n + b)).measurable _ hs1',
          Kernel.map_apply' _ (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ T) b).measurable _ hs2']
      have hker : markovChainStep P (n + b) v = markovChainStep P b (shiftRestrict n b v) := by
        simp [markovChainStep, shiftRestrict]
      rw [hker]
      congr 1
      ext y
      simp only [Set.mem_preimage]
      have heq : shiftRestrict n (b + 1)
          (IicProdIoc (X := fun _ : ℕ ↦ T) (n + b) (n + b + 1)
            (v, MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ T) (n + b) y)) =
          IicProdIoc (X := fun _ : ℕ ↦ T) b (b + 1)
            (shiftRestrict n b v, MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ T) b y) := by
        funext j
        simp only [shiftRestrict, IicProdIoc_def, MeasurableEquiv.piSingleton, MeasurableEquiv.coe_mk,
          Equiv.coe_fn_mk]
        by_cases hj : j.1 ≤ b
        · have hj' : n + j.1 ≤ n + b := by omega
          simp [hj, hj']
        · have hj' : ¬ n + j.1 ≤ n + b := by omega
          simp [hj, hj']
      rw [heq]
    rw [Measure.map_comp _ _ (measurable_shiftRestrict n (b + 1)), hcomm]
    ext s hs
    change ((Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) n (n + b) u).bind
        ((Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) b (b + 1)).comap
          (shiftRestrict n b) (measurable_shiftRestrict n b))) s =
      (((Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) n (n + b) u).map
          (shiftRestrict n b)).bind
        (Kernel.partialTraj (X := fun _ : ℕ ↦ T) (markovChainStep P) b (b + 1))) s
    rw [Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
      Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
      lintegral_map (Kernel.measurable_coe _ hs) (measurable_shiftRestrict n b)]
    rfl

private lemma traj_map_shift_eq_markovChainMeasure (P : Kernel T T) [IsMarkovKernel P]
    (n : ℕ) (u : Π _ : Finset.Iic n, T) :
    (Kernel.traj (X := fun _ : ℕ ↦ T) (markovChainStep P) n u).map (fun ω t ↦ ω (n + t)) =
      markovChainMeasure P (u ⟨n, Finset.mem_Iic.2 le_rfl⟩) := by
  let f : (Π _ : Finset.Iic 0, T) → (Π _ : Finset.Iic n, T) :=
    fun z j ↦ if j.1 = n then z ⟨0, Finset.mem_Iic.2 le_rfl⟩ else u j
  have hf : Measurable f := by
    refine measurable_pi_lambda _ fun j ↦ ?_
    by_cases hj : j.1 = n
    · simp only [f, hj, ↓reduceIte]; exact measurable_pi_apply _
    · simp only [f, hj, ↓reduceIte]; exact measurable_const
  have hshift : Measurable (fun ω : ℕ → T ↦ fun t : ℕ ↦ ω (n + t)) :=
    measurable_pi_lambda _ fun t ↦ measurable_pi_apply (n + t)
  let η : Kernel (Π _ : Finset.Iic 0, T) (ℕ → T) :=
    ((Kernel.traj (X := fun _ : ℕ ↦ T) (markovChainStep P) n).comap f hf).map
      (fun ω t ↦ ω (n + t))
  have hη : η = Kernel.traj (X := fun _ : ℕ ↦ T) (markovChainStep P) 0 := by
    refine Kernel.eq_traj (X := fun _ : ℕ ↦ T) (markovChainStep P) η fun b ↦ ?_
    ext z : 1
    rw [Kernel.map_apply _ (Preorder.measurable_frestrictLe b),
      Kernel.map_apply _ hshift, Kernel.comap_apply,
      Measure.map_map (Preorder.measurable_frestrictLe b) hshift]
    have hcomp : Preorder.frestrictLe (π := fun _ : ℕ ↦ T) b ∘ (fun ω t ↦ ω (n + t)) =
        shiftRestrict n b ∘ Preorder.frestrictLe (π := fun _ : ℕ ↦ T) (n + b) := rfl
    rw [hcomp, ← Measure.map_map (measurable_shiftRestrict n b) (Preorder.measurable_frestrictLe (n + b)),
      Kernel.traj_map_frestrictLe_apply, partialTraj_map_shiftRestrict]
    have hfz : (fun _ : Finset.Iic 0 ↦ f z ⟨n, Finset.mem_Iic.2 le_rfl⟩) = z := by
      funext j
      have hj : j.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.1 j.2)
      have hj' : j = ⟨0, Finset.mem_Iic.2 le_rfl⟩ := Subtype.ext hj
      simp [f, hj']
    rw [hfz]
  have hzu : f (fun _ ↦ u ⟨n, Finset.mem_Iic.2 le_rfl⟩) = u := by
    funext j
    by_cases hj : j.1 = n
    · have hj' : j = ⟨n, Finset.mem_Iic.2 le_rfl⟩ := Subtype.ext hj
      simp [f, hj']
    · simp [f, hj]
  have heval := congrArg (fun K ↦ K (fun _ ↦ u ⟨n, Finset.mem_Iic.2 le_rfl⟩)) hη
  simp only [η, Kernel.map_apply _ hshift, Kernel.comap_apply, hzu] at heval
  rw [markovChainMeasure_eq_traj]
  exact heval

private lemma setIntegral_shift_markovChainMeasure (P : Kernel T T) [IsMarkovKernel P]
    (x₀ y : T) (n : ℕ) {A : Set (ℕ → T)}
    (hA : MeasurableSet[trajectoryFiltration T n] A)
    (hAy : ∀ ω ∈ A, ω n = y)
    {g : (ℕ → T) → ℝ} (hg_m : Measurable g) {C : ℝ} (hg_b : ∀ ω, ‖g ω‖ ≤ C) :
    ∫ ω in A, g (fun t ↦ ω (n + t)) ∂markovChainMeasure P x₀ =
      (markovChainMeasure P x₀).real A * ∫ ω, g ω ∂markovChainMeasure P y := by
  obtain ⟨B, hB, rfl⟩ := hA
  let B' : Set (Π _ : Finset.Iic n, T) := B ∩ {u | u ⟨n, Finset.mem_Iic.2 le_rfl⟩ = y}
  have hm_n : Measurable (fun u : Π _ : Finset.Iic n, T ↦ u ⟨n, Finset.mem_Iic.2 le_rfl⟩) :=
    measurable_pi_apply _
  have hB' : MeasurableSet B' := hB.inter (hm_n (measurableSet_singleton y))
  have hpre : Preorder.frestrictLe (π := fun _ : ℕ ↦ T) n ⁻¹' B =
      Preorder.frestrictLe (π := fun _ : ℕ ↦ T) n ⁻¹' B' := by
    ext ω
    simp only [Set.mem_preimage, B', Set.mem_inter_iff, Set.mem_setOf_eq, Preorder.frestrictLe_apply]
    exact ⟨fun h ↦ ⟨h, hAy ω h⟩, fun h ↦ h.1⟩
  have hshift : Measurable (fun ω : ℕ → T ↦ fun t : ℕ ↦ ω (n + t)) :=
    measurable_pi_lambda _ fun t ↦ measurable_pi_apply (n + t)
  have hint_g : Integrable (fun ω : ℕ → T ↦ g (fun t ↦ ω (n + t)))
      (Kernel.traj (X := fun _ : ℕ ↦ T) (markovChainStep P) 0 (fun _ ↦ x₀)) :=
    Integrable.of_bound (hg_m.comp hshift).aestronglyMeasurable C (ae_of_all _ fun ω ↦ hg_b _)
  rw [markovChainMeasure_eq_traj]
  change (∫ ω in Preorder.frestrictLe (π := fun _ : ℕ ↦ T) n ⁻¹' B, g (fun t ↦ ω (n + t))
        ∂Kernel.traj (X := fun _ : ℕ ↦ T) (markovChainStep P) 0 (fun _ ↦ x₀)) =
      (Kernel.traj (X := fun _ : ℕ ↦ T) (markovChainStep P) 0 (fun _ ↦ x₀)).real
        (Preorder.frestrictLe (π := fun _ : ℕ ↦ T) n ⁻¹' B) *
        ∫ ω, g ω ∂markovChainMeasure P y
  rw [hpre, ← Kernel.setIntegral_traj_partialTraj (Nat.zero_le n) hint_g hB']
  have hinner : ∀ u ∈ B',
      ∫ ω, g (fun t ↦ ω (n + t)) ∂Kernel.traj (X := fun _ : ℕ ↦ T) (markovChainStep P) n u =
        ∫ ω, g ω ∂markovChainMeasure P y := by
    intro u hu
    rw [← integral_map hshift.aemeasurable hg_m.aestronglyMeasurable,
      traj_map_shift_eq_markovChainMeasure, hu.2]
  rw [setIntegral_congr_fun hB' hinner, setIntegral_const, smul_eq_mul]
  congr 1
  rw [Measure.real, Measure.real]
  congr 1
  rw [← Kernel.traj_map_frestrictLe_apply,
    Measure.map_apply (Preorder.measurable_frestrictLe n) hB']

private lemma measurableSet_stopping_eq {τ : (ℕ → T) → ℕ∞} (hτ : IsTrajStoppingTime τ) (n : ℕ) :
    MeasurableSet[trajectoryFiltration T n] {ω : ℕ → T | τ ω = (n : ℕ∞)} := by
  cases n with
  | zero =>
    have : {ω : ℕ → T | τ ω = ((0 : ℕ) : ℕ∞)} = {ω : ℕ → T | τ ω ≤ ((0 : ℕ) : ℕ∞)} := by
      ext ω; simp
    rw [this]; exact hτ 0
  | succ m =>
    have hmono : trajectoryFiltration T m ≤ trajectoryFiltration T (m + 1) := by
      have hcomp : (fun (ω : ℕ → T) (j : Finset.Iic m) ↦ ω j.1) =
          (fun (u : Π _ : Finset.Iic (m + 1), T) (j : Finset.Iic m) ↦
            u ⟨j.1, Finset.mem_Iic.2 (Nat.le_succ_of_le (Finset.mem_Iic.1 j.2))⟩) ∘
          (fun (ω : ℕ → T) (j : Finset.Iic (m + 1)) ↦ ω j.1) := rfl
      unfold trajectoryFiltration
      rw [hcomp, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_pi_lambda _ fun j ↦ measurable_pi_apply _).comap_le
    have : {ω : ℕ → T | τ ω = ((m + 1 : ℕ) : ℕ∞)} =
        {ω : ℕ → T | τ ω ≤ ((m + 1 : ℕ) : ℕ∞)} \ {ω : ℕ → T | τ ω ≤ (m : ℕ∞)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_diff]
      cases τ ω with
      | top =>
        simp only [top_le_iff, ENat.coe_ne_top, false_and, iff_false]
        exact ENat.top_ne_coe (m + 1)
      | coe u => norm_cast; omega
    rw [this]
    exact (hτ (m + 1)).diff (hmono _ (hτ m))

end MarkovShift

section MainProof

variable {T : Type*} [MeasurableSpace T] [Countable T] [MeasurableSingletonClass T]

private lemma measurable_finset_inf' {α ι : Type*} [MeasurableSpace α] (s : Finset ι)
    (hs : s.Nonempty) (f : ι → α → ℝ) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun x ↦ s.inf' hs (fun i ↦ f i x)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa using hf a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    have h1 : Measurable (f a) := hf a (Finset.mem_cons_self a s)
    have h2 : Measurable (fun x ↦ s.inf' hs (fun i ↦ f i x)) :=
      ih fun i hi ↦ hf i (Finset.mem_cons.2 (Or.inr hi))
    have heq : (fun x ↦ (Finset.cons a s ha).inf' (by simp) (fun i ↦ f i x)) =
        fun x ↦ min (f a x) (s.inf' hs (fun i ↦ f i x)) := by
      funext x; exact Finset.inf'_cons (H := hs) (f := fun i ↦ f i x)
    rw [heq]
    exact h1.min h2

private lemma measurable_finset_sup' {α ι : Type*} [MeasurableSpace α] (s : Finset ι)
    (hs : s.Nonempty) (f : ι → α → ℝ) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun x ↦ s.sup' hs (fun i ↦ f i x)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa using hf a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    have h1 : Measurable (f a) := hf a (Finset.mem_cons_self a s)
    have h2 : Measurable (fun x ↦ s.sup' hs (fun i ↦ f i x)) :=
      ih fun i hi ↦ hf i (Finset.mem_cons.2 (Or.inr hi))
    have heq : (fun x ↦ (Finset.cons a s ha).sup' (by simp) (fun i ↦ f i x)) =
        fun x ↦ max (f a x) (s.sup' hs (fun i ↦ f i x)) := by
      funext x; exact Finset.sup'_cons (H := hs) (f := fun i ↦ f i x)
    rw [heq]
    exact h1.max h2

private lemma measurable_range_inf' {k : ℕ} (g : T → ℝ) (j : Fin k) (u : ℕ) :
    Measurable (fun ω : Fin k → ℕ → T ↦
      (Finset.range (u + 1)).inf' ⟨0, Finset.mem_range.2 (Nat.zero_lt_succ u)⟩
        fun v ↦ g (ω j v)) := by
  refine measurable_finset_inf' (Finset.range (u + 1))
    ⟨0, Finset.mem_range.2 (Nat.zero_lt_succ u)⟩
    (fun v (ω : Fin k → ℕ → T) ↦ g (ω j v)) fun v _ ↦ ?_
  exact (measurable_of_countable_T g).comp ((measurable_pi_apply v).comp (measurable_pi_apply j))

private lemma measurable_prevailingChargeStack (P : Kernel T T) [IsMarkovKernel P]
    (r : T → ℝ) (a : ℝ) {k : ℕ} (j : Fin k) (u : ℕ) :
    Measurable (fun ω : Fin k → ℕ → T ↦ prevailingChargeStack P r a ω j u) :=
  measurable_range_inf' (gittinsIndex P r a) j u

private lemma measurable_partialInterleavedSum_univ (P : Kernel T T) [IsMarkovKernel P]
    (r : T → ℝ) (a : ℝ) {k : ℕ} (t : ℕ) :
    Measurable (fun ω : Fin k → ℕ → T ↦
      partialInterleavedSum (prevailingChargeStack P r a ω) Finset.univ t) := by
  unfold partialInterleavedSum
  split_ifs with hI
  · exact measurable_const
  · refine measurable_finset_sup' (playAllocations Finset.univ t) (playAllocations_nonempty hI t)
      (fun m ω ↦ ∑ j ∈ Finset.univ, ∑ u ∈ Finset.range (m j), prevailingChargeStack P r a ω j u)
      fun m _ ↦ ?_
    exact Finset.measurable_sum _ fun j _ ↦ Finset.measurable_sum _ fun u _ ↦
      measurable_prevailingChargeStack P r a j u

private lemma measurable_discChargeSum_stack (P : Kernel T T) [IsMarkovKernel P]
    {r : T → ℝ} (hrb : RewardsNonnegBounded r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {k : ℕ} (i : Fin k) :
    Measurable (fun ω : Fin k → ℕ → T ↦ discChargeSum a (prevailingChargeStack P r a ω)) := by
  obtain ⟨hr0, C, hrC⟩ := hrb
  have hterm : ∀ t : ℕ, Measurable (fun ω : Fin k → ℕ → T ↦
      a ^ t * (partialInterleavedSum (prevailingChargeStack P r a ω) Finset.univ (t + 1) -
        partialInterleavedSum (prevailingChargeStack P r a ω) Finset.univ t)) := fun t ↦
    measurable_const.mul
      ((measurable_partialInterleavedSum_univ P r a (t + 1)).sub
        (measurable_partialInterleavedSum_univ P r a t))
  refine measurable_of_tendsto_metrizable
    (f := fun N ω ↦ ∑ t ∈ Finset.range N, a ^ t *
      (partialInterleavedSum (prevailingChargeStack P r a ω) Finset.univ (t + 1) -
        partialInterleavedSum (prevailingChargeStack P r a ω) Finset.univ t))
    (fun N ↦ Finset.measurable_sum _ fun t _ ↦ hterm t) ?_
  rw [tendsto_pi_nhds]
  intro ω
  have hbounds : ∀ j u, 0 ≤ prevailingChargeStack P r a ω j u ∧
      prevailingChargeStack P r a ω j u ≤ C := fun j u ↦ by
    unfold prevailingChargeStack
    constructor
    · exact Finset.le_inf' _ _ fun v _ ↦ (gittinsIndex_bounds_nonneg P hr0 hrC ha0 ha1 _).1
    · exact (Finset.inf'_le _ (Finset.mem_range.2 (Nat.zero_lt_succ u))).trans
        (gittinsIndex_bounds_nonneg P hr0 hrC ha0 ha1 _).2
  exact (summable_discChargeSum_terms i ha0 ha1 _ (fun j u ↦ (hbounds j u).1)
    (fun j u ↦ (hbounds j u).2)).hasSum.tendsto_sum_nat

private lemma optimal_value_eq_integral_discChargeSum (P : Kernel T T) [IsMarkovKernel P]
    {r : T → ℝ} (hrb : RewardsNonnegBounded r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {k : ℕ} (i : Fin k) (x : Fin k → T) :
    (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π x) =
      ∫ ω, discChargeSum a (prevailingChargeStack P r a ω)
        ∂(Measure.pi fun j ↦ markovChainMeasure P (x j)) := by
  rw [← restrictedValue_univ_eq P r a i x]
  exact restricted_value_eq_expected_interleaved_charge P (measurable_of_countable_T r)
    hrb ha0 ha1 x Finset.univ

private lemma integral_shiftStack_eq_succ (P : Kernel T T) [IsMarkovKernel P]
    {r : T → ℝ} (hrb : RewardsNonnegBounded r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {m : ℕ} (x : Fin (m + 1) → T) (i : Fin (m + 1))
    {τ : (ℕ → T) → ℕ∞} (hτ : IsPositiveStoppingTime τ) :
    ∫ ω, discountPow a (τ (ω i)) *
        discChargeSum a (prevailingChargeStack P r a
          (Function.update ω i (fun u ↦ ω i ((τ (ω i)).toNat + u))))
      ∂(Measure.pi fun j ↦ markovChainMeasure P (x j)) =
      ∫ η, discountPow a (τ η) *
          (⨆ π : MarkovBanditPolicy (m + 1) T, markovBanditDiscountedValue P r a π
            (Function.update x i (η (τ η).toNat)))
        ∂markovChainMeasure P (x i) := by
  obtain ⟨hr0, C, hrC⟩ := hrb
  have hC0 : 0 ≤ C := le_trans (hr0 (x i)) (hrC (x i))
  have h1a : 0 < 1 - a := sub_pos.2 ha1
  set μ : Measure (Fin (m + 1) → ℕ → T) := Measure.pi fun j ↦ markovChainMeasure P (x j)
  set μi : Measure (ℕ → T) := markovChainMeasure P (x i)
  set μrest : Measure (Fin m → ℕ → T) := Measure.pi fun j : Fin m ↦ markovChainMeasure P (x (i.succAbove j))
  set D : (Fin (m + 1) → ℕ → T) → ℝ := fun ω ↦ discChargeSum a (prevailingChargeStack P r a ω)
  have hDm : Measurable D := measurable_discChargeSum_stack P ⟨hr0, C, hrC⟩ ha0 ha1 i
  have hD_bounds : ∀ ω, 0 ≤ D ω ∧ D ω ≤ C / (1 - a) := fun ω ↦ by
    refine discChargeSum_bounds i ha0 ha1 _ (fun j u ↦ ?_) (fun j u ↦ ?_)
    · exact Finset.le_inf' _ _ fun v _ ↦ (gittinsIndex_bounds_nonneg P hr0 hrC ha0 ha1 _).1
    · exact (Finset.inf'_le _ (Finset.mem_range.2 (Nat.zero_lt_succ u))).trans
        (gittinsIndex_bounds_nonneg P hr0 hrC ha0 ha1 _).2
  set F : (Fin (m + 1) → ℕ → T) → ℝ := fun ω ↦
    discountPow a (τ (ω i)) * D (Function.update ω i (fun u ↦ ω i ((τ (ω i)).toNat + u)))
  set V : (Fin (m + 1) → T) → ℝ := fun y ↦
    ⨆ π : MarkovBanditPolicy (m + 1) T, markovBanditDiscountedValue P r a π y
  set G : (ℕ → T) → ℝ := fun η ↦ discountPow a (τ η) * V (Function.update x i (η (τ η).toNat))
  have hτm : Measurable τ := measurable_stopping_time hτ.1
  -- Partition `{τ ≠ ⊤}` by `(n, y) : ℕ × T`
  let A : ℕ × T → Set (ℕ → T) := fun p ↦ {η | τ η = (p.1 : ℕ∞) ∧ η p.1 = p.2}
  let E : ℕ × T → Set (Fin (m + 1) → ℕ → T) := fun p ↦ (fun ω ↦ ω i) ⁻¹' A p
  have hA_filt : ∀ p : ℕ × T, MeasurableSet[trajectoryFiltration T p.1] (A p) := fun p ↦ by
    have h1 : MeasurableSet[trajectoryFiltration T p.1] {η : ℕ → T | τ η = (p.1 : ℕ∞)} :=
      measurableSet_stopping_eq hτ.1 p.1
    have h2 : MeasurableSet[trajectoryFiltration T p.1] {η : ℕ → T | η p.1 = p.2} := by
      rw [trajectoryFiltration, MeasurableSpace.measurableSet_comap]
      have hm : Measurable (fun u : Π _ : Finset.Iic p.1, T ↦ u ⟨p.1, Finset.mem_Iic.2 le_rfl⟩) :=
        measurable_pi_apply _
      exact ⟨{u : Π _ : Finset.Iic p.1, T | u ⟨p.1, Finset.mem_Iic.2 le_rfl⟩ = p.2},
        hm (measurableSet_singleton p.2), rfl⟩
    exact h1.inter h2
  have hA_meas : ∀ p : ℕ × T, MeasurableSet (A p) := fun p ↦ by
    have hproj : Measurable (fun (ω : ℕ → T) (j : Finset.Iic p.1) ↦ ω j.1) :=
      measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1
    exact hproj.comap_le _ (hA_filt p)
  have hE_meas : ∀ p : ℕ × T, MeasurableSet (E p) := fun p ↦
    (measurable_pi_apply i) (hA_meas p)
  have hA_disj : Pairwise (Function.onFun Disjoint A) := by
    intro p q hpq
    rw [Function.onFun, Set.disjoint_left]
    intro η hp hq
    apply hpq
    have h1 : p.1 = q.1 := by
      have : (p.1 : ℕ∞) = (q.1 : ℕ∞) := hp.1.symm.trans hq.1
      exact_mod_cast this
    have h2 : p.2 = q.2 := by
      have hp2 := hp.2
      rw [h1] at hp2
      exact hp2.symm.trans hq.2
    exact Prod.ext h1 h2
  have hE_disj : Pairwise (Function.onFun Disjoint E) := fun p q hpq ↦
    (hA_disj hpq).preimage (fun (ω : Fin (m + 1) → ℕ → T) ↦ ω i)
  have hA_union : ⋃ p : ℕ × T, A p = {η | τ η ≠ ⊤} := by
    ext η
    simp only [Set.mem_iUnion, A, Set.mem_setOf_eq, Prod.exists]
    constructor
    · rintro ⟨n, y, hn, _⟩; rw [hn]; exact ENat.coe_ne_top n
    · intro hne
      cases h : τ η with
      | top => exact (hne h).elim
      | coe n => exact ⟨n, η n, rfl, rfl⟩
  have hE_union : ⋃ p : ℕ × T, E p = {ω | τ (ω i) ≠ ⊤} := by
    ext ω
    simp only [Set.mem_iUnion, E, Set.mem_preimage, Set.mem_setOf_eq]
    rw [← Set.mem_iUnion, hA_union]
    rfl
  -- Measurability & integrability of F and G
  have hFm : Measurable F := by
    have hshift_n : ∀ n : ℕ, Measurable (fun ω : Fin (m + 1) → ℕ → T ↦
        Function.update ω i (fun u ↦ ω i (n + u))) := fun n ↦ by
      rw [measurable_pi_iff]
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self]
        exact measurable_pi_lambda _ fun u ↦ (measurable_pi_apply (n + u)).comp (measurable_pi_apply j)
      · simp only [Function.update_of_ne hj]
        exact measurable_pi_apply j
    have hF_eq : F = fun ω ↦ ∑' n : ℕ,
        if τ (ω i) = (n : ℕ∞) then a ^ n * D (Function.update ω i (fun u ↦ ω i (n + u))) else 0 := by
      funext ω
      cases h : τ (ω i) with
      | top =>
        simp [F, h, discountPow_top]
      | coe n =>
        rw [tsum_eq_single n]
        · simp [F, h, discountPow_coe]
        · intro b hb
          have : (n : ℕ∞) ≠ (b : ℕ∞) := by exact_mod_cast Ne.symm hb
          simp [this]
    rw [hF_eq]
    refine measurable_of_tendsto_metrizable
      (f := fun N ω ↦ ∑ n ∈ Finset.range N,
        if τ (ω i) = (n : ℕ∞) then a ^ n * D (Function.update ω i (fun u ↦ ω i (n + u))) else 0)
      (fun N ↦ Finset.measurable_sum _ fun n _ ↦ ?_) ?_
    · refine Measurable.ite ?_ (measurable_const.mul (hDm.comp (hshift_n n))) measurable_const
      exact (hτm.comp (measurable_pi_apply i)) (measurableSet_singleton (n : ℕ∞))
    · rw [tendsto_pi_nhds]
      intro ω
      have hsumm : Summable (fun n : ℕ ↦
          if τ (ω i) = (n : ℕ∞) then a ^ n * D (Function.update ω i (fun u ↦ ω i (n + u))) else 0) := by
        cases h : τ (ω i) with
        | top => simp
        | coe n =>
          refine summable_of_ne_finset_zero (s := {n}) fun b hb ↦ ?_
          rw [Finset.mem_singleton] at hb
          have : (n : ℕ∞) ≠ (b : ℕ∞) := by exact_mod_cast Ne.symm hb
          simp [this]
      exact hsumm.hasSum.tendsto_sum_nat
  have hF_int : Integrable F μ := by
    refine Integrable.of_bound hFm.aestronglyMeasurable (C / (1 - a)) (ae_of_all _ fun ω ↦ ?_)
    have hdp0 := discountPow_nonneg ha0.le (τ (ω i))
    have hdp1 := discountPow_le_one ha0.le ha1.le (τ (ω i))
    have hD0 := (hD_bounds (Function.update ω i (fun u ↦ ω i ((τ (ω i)).toNat + u)))).1
    have hDC := (hD_bounds (Function.update ω i (fun u ↦ ω i ((τ (ω i)).toNat + u)))).2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hdp0 hD0)]
    calc discountPow a (τ (ω i)) * D _ ≤ 1 * (C / (1 - a)) :=
          mul_le_mul hdp1 hDC hD0 zero_le_one
      _ = C / (1 - a) := one_mul _
  have hGm : Measurable G := by
    have hdp_m' : Measurable (discountPow a) := fun _ _ ↦ MeasurableSet.of_discrete
    have htn_m' : Measurable ENat.toNat := fun _ _ ↦ MeasurableSet.of_discrete
    have hG1 : Measurable (fun η : ℕ → T ↦ discountPow a (τ η)) := hdp_m'.comp hτm
    have hG2 : Measurable (fun η : ℕ → T ↦ η (τ η).toNat) := by
      refine measurable_to_countable' fun y ↦ ?_
      have : (fun η : ℕ → T ↦ η (τ η).toNat) ⁻¹' {y} =
          ⋃ n : ℕ, ((fun η ↦ (τ η).toNat) ⁻¹' {n} ∩ (fun η ↦ η n) ⁻¹' {y}) := by
        ext η
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff]
        exact ⟨fun h ↦ ⟨(τ η).toNat, rfl, h⟩, fun ⟨n, hn, hy⟩ ↦ by rwa [hn]⟩
      rw [this]
      refine MeasurableSet.iUnion fun n ↦ MeasurableSet.inter ?_ ?_
      · exact (htn_m'.comp hτm) (measurableSet_singleton n)
      · exact (measurable_pi_apply n) (measurableSet_singleton y)
    exact hG1.mul ((measurable_of_countable_T (fun y : T ↦ V (Function.update x i y))).comp hG2)
  have hV_bounds : ∀ y : Fin (m + 1) → T, 0 ≤ V y ∧ V y ≤ C / (1 - a) := fun y ↦ by
    have hV_eq := optimal_value_eq_integral_discChargeSum P ⟨hr0, C, hrC⟩ ha0 ha1 i y
    dsimp only [V]
    rw [hV_eq]
    constructor
    · exact integral_nonneg fun ω ↦ (hD_bounds ω).1
    · calc ∫ ω, D ω ∂(Measure.pi fun j ↦ markovChainMeasure P (y j))
          ≤ ∫ _ω, C / (1 - a) ∂(Measure.pi fun j ↦ markovChainMeasure P (y j)) := by
            refine integral_mono ?_ (integrable_const _) fun ω ↦ (hD_bounds ω).2
            exact Integrable.of_bound hDm.aestronglyMeasurable (C / (1 - a))
              (ae_of_all _ fun ω ↦ by
                rw [Real.norm_eq_abs, abs_of_nonneg (hD_bounds ω).1]; exact (hD_bounds ω).2)
        _ = C / (1 - a) := by simp
  have hG_int : Integrable G μi := by
    refine Integrable.of_bound hGm.aestronglyMeasurable (C / (1 - a)) (ae_of_all _ fun η ↦ ?_)
    have hdp0 := discountPow_nonneg ha0.le (τ η)
    have hdp1 := discountPow_le_one ha0.le ha1.le (τ η)
    have hV0 := (hV_bounds (Function.update x i (η (τ η).toNat))).1
    have hVC := (hV_bounds (Function.update x i (η (τ η).toNat))).2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hdp0 hV0)]
    calc discountPow a (τ η) * V _ ≤ 1 * (C / (1 - a)) :=
          mul_le_mul hdp1 hVC hV0 zero_le_one
      _ = C / (1 - a) := one_mul _
  -- Restrict both full integrals to `{τ ≠ ⊤}` since `discountPow a ⊤ = 0`
  have hLHS_rest : ∫ ω, F ω ∂μ = ∫ ω in ⋃ p : ℕ × T, E p, F ω ∂μ := by
    rw [← integral_indicator (MeasurableSet.iUnion hE_meas)]
    congr 1; funext ω
    by_cases h : ω ∈ ⋃ p : ℕ × T, E p
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]
      rw [hE_union, Set.mem_setOf_eq, not_not] at h
      simp [F, h, discountPow_top]
  have hRHS_rest : ∫ η, G η ∂μi = ∫ η in ⋃ p : ℕ × T, A p, G η ∂μi := by
    rw [← integral_indicator (MeasurableSet.iUnion hA_meas)]
    congr 1; funext η
    by_cases h : η ∈ ⋃ p : ℕ × T, A p
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]
      rw [hA_union, Set.mem_setOf_eq, not_not] at h
      simp [G, h, discountPow_top]
  rw [hLHS_rest, hRHS_rest,
      integral_iUnion hE_meas hE_disj hF_int.integrableOn,
      integral_iUnion hA_meas hA_disj hG_int.integrableOn]
  -- Prove term-by-term equality for each `(n, y) : ℕ × T`
  refine tsum_congr fun ⟨n, y⟩ ↦ ?_
  have hpiece_L : ∫ ω in E (n, y), F ω ∂μ =
      a ^ n * ∫ ω in E (n, y), D (Function.update ω i (fun u ↦ ω i (n + u))) ∂μ := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (hE_meas (n, y)) fun ω hω ↦ ?_
    have hτn : τ (ω i) = (n : ℕ∞) := hω.1
    simp [F, hτn, discountPow_coe]
  have hpiece_R : ∫ η in A (n, y), G η ∂μi =
      a ^ n * (μi.real (A (n, y)) * V (Function.update x i y)) := by
    have hcongr : ∫ η in A (n, y), G η ∂μi =
        ∫ _η in A (n, y), (a ^ n * V (Function.update x i y)) ∂μi := by
      refine setIntegral_congr_fun (hA_meas (n, y)) fun η hη ↦ ?_
      simp [G, hη.1, hη.2, discountPow_coe]
    rw [hcongr, setIntegral_const, smul_eq_mul]
    ring
  rw [hpiece_L, hpiece_R]
  congr 1
  -- Disintegrate μ = μi × μrest via `measurePreserving_piFinSuccAbove`
  let e : (Fin (m + 1) → ℕ → T) ≃ᵐ (ℕ → T) × (Fin m → ℕ → T) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℕ → T) i
  have hmp : MeasurePreserving e μ (μi.prod μrest) :=
    measurePreserving_piFinSuccAbove (fun j ↦ markovChainMeasure P (x j)) i
  have hmp_y : MeasurePreserving e
      (Measure.pi fun j ↦ markovChainMeasure P (Function.update x i y j))
      ((markovChainMeasure P y).prod μrest) := by
    have hmp0 := measurePreserving_piFinSuccAbove
      (fun j ↦ markovChainMeasure P (Function.update x i y j)) i
    have h1 : markovChainMeasure P (Function.update x i y i) = markovChainMeasure P y := by
      simp
    have h2 : (Measure.pi fun j : Fin m ↦ markovChainMeasure P (Function.update x i y (i.succAbove j))) =
        μrest := by
      congr 1; funext j
      rw [Function.update_of_ne (Fin.succAbove_ne i j)]
    rwa [h1, h2] at hmp0
  have hE_eq_pre : E (n, y) = e ⁻¹' (A (n, y) ×ˢ Set.univ) := by
    ext ω
    simp [E, e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  have hshift_e : ∀ p : (ℕ → T) × (Fin m → ℕ → T),
      Function.update (e.symm p) i (fun u ↦ (e.symm p) i (n + u)) =
        e.symm (fun u ↦ p.1 (n + u), p.2) := by
    intro p
    funext j
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    by_cases hj : j = i
    · subst hj
      simp
    · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
      simp [Fin.succAbove_ne]
  -- Pull integral over `E (n, y)` through `e`
  have hD_shift_m : Measurable (fun p : (ℕ → T) × (Fin m → ℕ → T) ↦
      D (e.symm (fun u ↦ p.1 (n + u), p.2))) := by
    have h1 : Measurable (fun p : (ℕ → T) × (Fin m → ℕ → T) ↦
        (fun u : ℕ ↦ p.1 (n + u), p.2)) :=
      (measurable_pi_lambda _ fun u ↦ (measurable_pi_apply (n + u)).comp measurable_fst).prodMk
        measurable_snd
    exact hDm.comp (e.symm.measurable.comp h1)
  have hD_shift_int : Integrable (fun p : (ℕ → T) × (Fin m → ℕ → T) ↦
      (A (n, y) ×ˢ Set.univ).indicator (fun q ↦ D (e.symm (fun u ↦ q.1 (n + u), q.2))) p)
      (μi.prod μrest) := by
    refine Integrable.of_bound
      (hD_shift_m.indicator ((hA_meas (n, y)).prod MeasurableSet.univ)).aestronglyMeasurable
      (C / (1 - a)) (ae_of_all _ fun p ↦ ?_)
    by_cases hp : p ∈ A (n, y) ×ˢ Set.univ
    · rw [Set.indicator_of_mem hp, Real.norm_eq_abs, abs_of_nonneg (hD_bounds _).1]
      exact (hD_bounds _).2
    · rw [Set.indicator_of_notMem hp, norm_zero]
      exact div_nonneg hC0 h1a.le
  calc ∫ ω in E (n, y), D (Function.update ω i (fun u ↦ ω i (n + u))) ∂μ
      = ∫ ω, (A (n, y) ×ˢ Set.univ).indicator
          (fun p ↦ D (e.symm (fun u ↦ p.1 (n + u), p.2))) (e ω) ∂μ := by
        rw [← integral_indicator (hE_meas (n, y))]
        congr 1; funext ω
        rw [hE_eq_pre]
        by_cases h : e ω ∈ A (n, y) ×ˢ Set.univ
        · simp only [Set.mem_preimage, h, Set.indicator_of_mem]
          have heq := hshift_e (e ω)
          rw [e.symm_apply_apply] at heq
          rw [heq]
        · simp [h]
    _ = ∫ p, (A (n, y) ×ˢ Set.univ).indicator
          (fun q ↦ D (e.symm (fun u ↦ q.1 (n + u), q.2))) p ∂(μi.prod μrest) :=
        hmp.integral_comp' _
    _ = ∫ ωrest, ∫ η, (A (n, y) ×ˢ Set.univ).indicator
          (fun q ↦ D (e.symm (fun u ↦ q.1 (n + u), q.2))) (η, ωrest) ∂μi ∂μrest :=
        integral_prod_symm _ hD_shift_int
    _ = ∫ ωrest, ∫ η in A (n, y), D (e.symm (fun u ↦ η (n + u), ωrest)) ∂μi ∂μrest := by
        congr 1; funext ωrest
        rw [← integral_indicator (hA_meas (n, y))]
        congr 1; funext η
        by_cases h : η ∈ A (n, y) <;> simp [h]
    _ = ∫ ωrest, (μi.real (A (n, y)) *
          ∫ η, D (e.symm (η, ωrest)) ∂markovChainMeasure P y) ∂μrest := by
        congr 1; funext ωrest
        refine setIntegral_shift_markovChainMeasure P (x i) y n (hA_filt (n, y))
          (fun η hη ↦ hη.2) (g := fun η ↦ D (e.symm (η, ωrest))) ?_ (C := C / (1 - a)) ?_
        · exact hDm.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
        · intro η
          rw [Real.norm_eq_abs, abs_of_nonneg (hD_bounds _).1]
          exact (hD_bounds _).2
    _ = μi.real (A (n, y)) *
          ∫ ωrest, ∫ η, D (e.symm (η, ωrest)) ∂markovChainMeasure P y ∂μrest :=
        integral_const_mul _ _
    _ = μi.real (A (n, y)) *
          ∫ p, D (e.symm p) ∂((markovChainMeasure P y).prod μrest) := by
        congr 1
        have hD_int_y : Integrable (fun p : (ℕ → T) × (Fin m → ℕ → T) ↦ D (e.symm p))
            ((markovChainMeasure P y).prod μrest) :=
          Integrable.of_bound (hDm.comp e.symm.measurable).aestronglyMeasurable (C / (1 - a))
            (ae_of_all _ fun p ↦ by
              rw [Real.norm_eq_abs, abs_of_nonneg (hD_bounds _).1]; exact (hD_bounds _).2)
        exact (integral_prod_symm _ hD_int_y).symm
    _ = μi.real (A (n, y)) *
          ∫ ω, D ω ∂(Measure.pi fun j ↦ markovChainMeasure P (Function.update x i y j)) := by
        congr 1
        have hcomp := hmp_y.integral_comp' (fun p ↦ D (e.symm p))
        simp only [e.symm_apply_apply] at hcomp
        exact hcomp.symm
    _ = μi.real (A (n, y)) * V (Function.update x i y) := by
        rw [← optimal_value_eq_integral_discChargeSum P ⟨hr0, C, hrC⟩ ha0 ha1 i
          (Function.update x i y)]

private lemma optimal_value_le_max_index_stage_nonneg (P : Kernel T T) [IsMarkovKernel P]
    {r : T → ℝ} (hrb : RewardsNonnegBounded r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {k : ℕ} (x : Fin k → T) (i : Fin k) {τ : (ℕ → T) → ℕ∞} (hτ : IsPositiveStoppingTime τ) :
    (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π x) ≤
      (⨆ j : Fin k, gittinsIndex P r a (x j)) * stoppedTime P a τ (x i) +
        ∫ ω, discountPow a (τ ω) *
            (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π
              (Function.update x i (ω (τ ω).toNat))) ∂markovChainMeasure P (x i) := by
  cases k with
  | zero => exact i.elim0
  | succ m =>
    obtain ⟨hr0, C, hrC⟩ := hrb
    have hC0 : 0 ≤ C := le_trans (hr0 (x i)) (hrC (x i))
    have h1a : 0 < 1 - a := sub_pos.2 ha1
    set μ : Measure (Fin (m + 1) → ℕ → T) := Measure.pi fun j ↦ markovChainMeasure P (x j)
    set Mstar : ℝ := ⨆ j : Fin (m + 1), gittinsIndex P r a (x j)
    set D : (Fin (m + 1) → ℕ → T) → ℝ := fun ω ↦ discChargeSum a (prevailingChargeStack P r a ω)
    have hDm : Measurable D := measurable_discChargeSum_stack P ⟨hr0, C, hrC⟩ ha0 ha1 i
    have hD_bounds : ∀ ω, 0 ≤ D ω ∧ D ω ≤ C / (1 - a) := fun ω ↦ by
      refine discChargeSum_bounds i ha0 ha1 _ (fun j u ↦ ?_) (fun j u ↦ ?_)
      · exact Finset.le_inf' _ _ fun v _ ↦ (gittinsIndex_bounds_nonneg P hr0 hrC ha0 ha1 _).1
      · exact (Finset.inf'_le _ (Finset.mem_range.2 (Nat.zero_lt_succ u))).trans
          (gittinsIndex_bounds_nonneg P hr0 hrC ha0 ha1 _).2
    -- Pointwise inequality for ω with ω j 0 = x j for all j
    have hae_zero : ∀ᵐ ω ∂μ, ∀ j : Fin (m + 1), ω j 0 = x j := by
      rw [ae_all_iff]
      intro j
      have hmp_j : MeasurePreserving (Function.eval j) μ (markovChainMeasure P (x j)) :=
        measurePreserving_eval (fun l ↦ markovChainMeasure P (x l)) j
      exact hmp_j.quasiMeasurePreserving.ae (ae_eval_zero_markovChainMeasure P (x j))
    have hae_bound : ∀ᵐ ω ∂μ,
        D ω ≤ Mstar * discountedStoppedSum a (fun _ ↦ 1) τ (ω i) +
          discountPow a (τ (ω i)) *
            D (Function.update ω i (fun u ↦ ω i ((τ (ω i)).toNat + u))) := by
      filter_upwards [hae_zero] with ω hω0
      have hH0 : ∀ j u, 0 ≤ prevailingChargeStack P r a ω j u := fun j u ↦
        Finset.le_inf' _ _ fun v _ ↦ (gittinsIndex_bounds_nonneg P hr0 hrC ha0 ha1 _).1
      have hHM : ∀ j u, prevailingChargeStack P r a ω j u ≤ Mstar := fun j u ↦ by
        calc prevailingChargeStack P r a ω j u
            ≤ gittinsIndex P r a (ω j 0) :=
              Finset.inf'_le _ (Finset.mem_range.2 (Nat.zero_lt_succ u))
          _ = gittinsIndex P r a (x j) := by rw [hω0 j]
          _ ≤ Mstar := le_ciSup (f := fun j : Fin (m + 1) ↦ gittinsIndex P r a (x j))
              (Set.finite_range _).bddAbove j
      cases hτval : τ (ω i) with
      | top =>
        have hW : discountedStoppedSum a (fun _ ↦ 1) τ (ω i) = ∑' t : ℕ, a ^ t := by
          have : discountedStoppedSum a (fun _ ↦ 1) τ (ω i) =
              discountedStoppedSum a (fun _ ↦ 1) (fun _ ↦ (⊤ : ℕ∞)) (ω i) := by
            unfold discountedStoppedSum; simp [hτval]
          rw [this, discountedStoppedSum_one_of_top]
        rw [hW, discountPow_top, zero_mul, add_zero]
        exact discChargeSum_le_top i ha0 ha1 _ hH0 hHM
      | coe N =>
        have hW : discountedStoppedSum a (fun _ ↦ 1) τ (ω i) = ∑ t ∈ Finset.range N, a ^ t := by
          have : discountedStoppedSum a (fun _ ↦ 1) τ (ω i) =
              discountedStoppedSum a (fun _ ↦ 1) (fun _ ↦ (N : ℕ∞)) (ω i) := by
            unfold discountedStoppedSum; simp [hτval]
          rw [this, discountedStoppedSum_one_of_nat]
        rw [hW, discountPow_coe, ENat.toNat_natCast]
        refine discChargeSum_le_shift_nat i ha0 ha1 N
          (prevailingChargeStack P r a ω)
          (prevailingChargeStack P r a (Function.update ω i (fun u ↦ ω i (N + u))))
          hH0 hHM
          (fun j u ↦ Finset.le_inf' _ _ fun v _ ↦ (gittinsIndex_bounds_nonneg P hr0 hrC ha0 ha1 _).1)
          (fun j u ↦ (Finset.inf'_le _ (Finset.mem_range.2 (Nat.zero_lt_succ u))).trans
            (gittinsIndex_bounds_nonneg P hr0 hrC ha0 ha1 _).2)
          (fun j hj u ↦ by simp [prevailingChargeStack, hj])
          (fun u ↦ ?_)
        unfold prevailingChargeStack
        simp only [Function.update_self]
        refine Finset.le_inf' _ _ fun v hv ↦ ?_
        rw [Finset.mem_range] at hv
        exact Finset.inf'_le (f := fun w ↦ gittinsIndex P r a (ω i w))
          (Finset.mem_range.2 (by omega))
    -- Integrability of all three terms on `μ`
    have hD_int : Integrable D μ :=
      Integrable.of_bound hDm.aestronglyMeasurable (C / (1 - a))
        (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hD_bounds ω).1]; exact (hD_bounds ω).2)
    have hW_int : Integrable (fun ω : Fin (m + 1) → ℕ → T ↦
        Mstar * discountedStoppedSum a (fun _ ↦ 1) τ (ω i)) μ := by
      have hmW : Measurable (fun ω : Fin (m + 1) → ℕ → T ↦
          discountedStoppedSum a (fun _ ↦ 1) τ (ω i)) :=
        (measurable_discountedStoppedSum ha0 ha1 (f := fun _ ↦ (1 : ℝ)) (M := 1)
          (fun _ ↦ by norm_num) hτ.1).comp (measurable_pi_apply i)
      refine (Integrable.of_bound hmW.aestronglyMeasurable (1 / (1 - a)) (ae_of_all _ fun ω ↦ ?_)).const_mul Mstar
      rw [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one (discountedStoppedSum_one_ge_one ha0 ha1 hτ.2 (ω i)))]
      exact discountedStoppedSum_one_le ha0 ha1 τ (ω i)
    have hτm : Measurable τ := measurable_stopping_time hτ.1
    have hF_int : Integrable (fun ω : Fin (m + 1) → ℕ → T ↦
        discountPow a (τ (ω i)) * D (Function.update ω i (fun u ↦ ω i ((τ (ω i)).toNat + u)))) μ := by
      have hshift_n : ∀ n : ℕ, Measurable (fun ω : Fin (m + 1) → ℕ → T ↦
          Function.update ω i (fun u ↦ ω i (n + u))) := fun n ↦ by
        rw [measurable_pi_iff]
        intro j
        by_cases hj : j = i
        · subst hj
          simp only [Function.update_self]
          exact measurable_pi_lambda _ fun u ↦ (measurable_pi_apply (n + u)).comp (measurable_pi_apply j)
        · simp only [Function.update_of_ne hj]
          exact measurable_pi_apply j
      have hFm : Measurable (fun ω : Fin (m + 1) → ℕ → T ↦
          discountPow a (τ (ω i)) * D (Function.update ω i (fun u ↦ ω i ((τ (ω i)).toNat + u)))) := by
        have hF_eq : (fun ω : Fin (m + 1) → ℕ → T ↦
            discountPow a (τ (ω i)) * D (Function.update ω i (fun u ↦ ω i ((τ (ω i)).toNat + u)))) =
            fun ω ↦ ∑' n : ℕ,
              if τ (ω i) = (n : ℕ∞) then a ^ n * D (Function.update ω i (fun u ↦ ω i (n + u))) else 0 := by
          funext ω
          cases h : τ (ω i) with
          | top => simp [discountPow_top]
          | coe n =>
            rw [tsum_eq_single n]
            · simp [discountPow_coe]
            · intro b hb
              have : (n : ℕ∞) ≠ (b : ℕ∞) := by exact_mod_cast Ne.symm hb
              simp [this]
        rw [hF_eq]
        refine measurable_of_tendsto_metrizable
          (f := fun N ω ↦ ∑ n ∈ Finset.range N,
            if τ (ω i) = (n : ℕ∞) then a ^ n * D (Function.update ω i (fun u ↦ ω i (n + u))) else 0)
          (fun N ↦ Finset.measurable_sum _ fun n _ ↦ ?_) ?_
        · refine Measurable.ite ?_ (measurable_const.mul (hDm.comp (hshift_n n))) measurable_const
          exact (hτm.comp (measurable_pi_apply i)) (measurableSet_singleton (n : ℕ∞))
        · rw [tendsto_pi_nhds]
          intro ω
          have hsumm : Summable (fun n : ℕ ↦
              if τ (ω i) = (n : ℕ∞) then a ^ n * D (Function.update ω i (fun u ↦ ω i (n + u))) else 0) := by
            cases h : τ (ω i) with
            | top => simp
            | coe n =>
              refine summable_of_ne_finset_zero (s := {n}) fun b hb ↦ ?_
              rw [Finset.mem_singleton] at hb
              have : (n : ℕ∞) ≠ (b : ℕ∞) := by exact_mod_cast Ne.symm hb
              simp [this]
          exact hsumm.hasSum.tendsto_sum_nat
      refine Integrable.of_bound hFm.aestronglyMeasurable (C / (1 - a)) (ae_of_all _ fun ω ↦ ?_)
      have hdp0 := discountPow_nonneg ha0.le (τ (ω i))
      have hdp1 := discountPow_le_one ha0.le ha1.le (τ (ω i))
      have hD0 := (hD_bounds (Function.update ω i (fun u ↦ ω i ((τ (ω i)).toNat + u)))).1
      have hDC := (hD_bounds (Function.update ω i (fun u ↦ ω i ((τ (ω i)).toNat + u)))).2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hdp0 hD0)]
      calc discountPow a (τ (ω i)) * D _ ≤ 1 * (C / (1 - a)) :=
            mul_le_mul hdp1 hDC hD0 zero_le_one
        _ = C / (1 - a) := one_mul _
    -- Integrate and identify each term
    have hint_le : ∫ ω, D ω ∂μ ≤
        (∫ ω, Mstar * discountedStoppedSum a (fun _ ↦ 1) τ (ω i) ∂μ) +
        ∫ ω, discountPow a (τ (ω i)) *
          D (Function.update ω i (fun u ↦ ω i ((τ (ω i)).toNat + u))) ∂μ := by
      rw [← integral_add hW_int hF_int]
      exact integral_mono_ae hD_int (hW_int.add hF_int) hae_bound
    have hLHS : ∫ ω, D ω ∂μ =
        ⨆ π : MarkovBanditPolicy (m + 1) T, markovBanditDiscountedValue P r a π x :=
      (optimal_value_eq_integral_discChargeSum P ⟨hr0, C, hrC⟩ ha0 ha1 i x).symm
    have hW_eq : ∫ ω, Mstar * discountedStoppedSum a (fun _ ↦ 1) τ (ω i) ∂μ =
        Mstar * stoppedTime P a τ (x i) := by
      rw [integral_const_mul]
      congr 1
      have hmp_i : MeasurePreserving (Function.eval i) μ (markovChainMeasure P (x i)) :=
        measurePreserving_eval (fun l ↦ markovChainMeasure P (x l)) i
      have hm_d : Measurable (discountedStoppedSum a (fun _ ↦ 1) τ) :=
        measurable_discountedStoppedSum ha0 ha1 (f := fun _ ↦ (1 : ℝ)) (M := 1)
          (fun _ ↦ by norm_num) hτ.1
      rw [stoppedTime, ← hmp_i.map_eq, integral_map hmp_i.measurable.aemeasurable hm_d.aestronglyMeasurable]
    have hF_eq := integral_shiftStack_eq_succ P ⟨hr0, C, hrC⟩ ha0 ha1 x i hτ
    rw [hLHS, hW_eq, hF_eq] at hint_le
    exact hint_le

end MainProof

theorem solution {T : Type*} [MeasurableSpace T] [Countable T]
    [MeasurableSingletonClass T] (P : Kernel T T) [IsMarkovKernel P] {r : T → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {k : ℕ} (x : Fin k → T)
    (i : Fin k) {τ : (ℕ → T) → ℕ∞} (hτ : IsPositiveStoppingTime τ) :
    (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π x) ≤
      (⨆ j : Fin k, gittinsIndex P r a (x j)) * stoppedTime P a τ (x i) +
        ∫ ω, discountPow a (τ ω) *
            (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π
              (Function.update x i (ω (τ ω).toNat))) ∂markovChainMeasure P (x i) := by
  obtain ⟨M, hM⟩ := hr
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (x i))
  let r' : T → ℝ := fun y ↦ r y + M
  have hr' : RewardsNonnegBounded r' := by
    refine ⟨fun y ↦ ?_, 2 * M, fun y ↦ ?_⟩
    · have := (abs_le.1 (hM y)).1; dsimp [r']; linarith
    · have := (abs_le.1 (hM y)).2; dsimp [r']; linarith
  have hmain := optimal_value_le_max_index_stage_nonneg P hr' ha0 ha1 x i hτ
  -- Rewrite LHS, max index, and RHS integral under the constant shift `r' = r + M`
  rw [iSup_markovBanditDiscountedValue_add_const P ⟨M, hM⟩ M ha0 ha1 i x] at hmain
  have hsup_idx : (⨆ j : Fin k, gittinsIndex P r' a (x j)) =
      (⨆ j : Fin k, gittinsIndex P r a (x j)) + M := by
    have : Nonempty (Fin k) := ⟨i⟩
    simp_rw [r', gittinsIndex_add_const P ⟨M, hM⟩ M ha0 ha1]
    apply le_antisymm
    · refine ciSup_le fun j ↦ add_le_add
        (le_ciSup (f := fun j : Fin k ↦ gittinsIndex P r a (x j)) (Set.finite_range _).bddAbove j) le_rfl
    · rw [← le_sub_iff_add_le]
      refine ciSup_le fun j ↦ ?_
      rw [le_sub_iff_add_le]
      exact le_ciSup (f := fun j : Fin k ↦ gittinsIndex P r a (x j) + M) (Set.finite_range _).bddAbove j
  rw [hsup_idx] at hmain
  have hτm : Measurable τ := measurable_stopping_time hτ.1
  have hdp_m' : Measurable (discountPow a) := fun _ _ ↦ MeasurableSet.of_discrete
  have htn_m' : Measurable ENat.toNat := fun _ _ ↦ MeasurableSet.of_discrete
  have hdp_m : Measurable (fun ω : ℕ → T ↦ discountPow a (τ ω)) := hdp_m'.comp hτm
  have hdp_int : Integrable (fun ω : ℕ → T ↦ discountPow a (τ ω)) (markovChainMeasure P (x i)) :=
    Integrable.of_bound hdp_m.aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (discountPow_nonneg ha0.le _)]
      exact discountPow_le_one ha0.le ha1.le _)
  have hstate_m : Measurable (fun ω : ℕ → T ↦ ω (τ ω).toNat) := by
    refine measurable_to_countable' fun y ↦ ?_
    have : (fun ω : ℕ → T ↦ ω (τ ω).toNat) ⁻¹' {y} =
        ⋃ n : ℕ, ((fun ω ↦ (τ ω).toNat) ⁻¹' {n} ∩ (fun ω ↦ ω n) ⁻¹' {y}) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff]
      exact ⟨fun h ↦ ⟨(τ ω).toNat, rfl, h⟩, fun ⟨n, hn, hy⟩ ↦ by rwa [hn]⟩
    rw [this]
    refine MeasurableSet.iUnion fun n ↦ MeasurableSet.inter ?_ ?_
    · exact (htn_m'.comp hτm) (measurableSet_singleton n)
    · exact (measurable_pi_apply n) (measurableSet_singleton y)
  have hV_int : Integrable (fun ω : ℕ → T ↦ discountPow a (τ ω) *
      (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π
        (Function.update x i (ω (τ ω).toNat)))) (markovChainMeasure P (x i)) := by
    have hm : Measurable (fun ω : ℕ → T ↦ discountPow a (τ ω) *
        (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π
          (Function.update x i (ω (τ ω).toNat)))) :=
      hdp_m.mul ((measurable_of_countable_T (fun y : T ↦
        ⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π
          (Function.update x i y))).comp hstate_m)
    refine Integrable.of_bound hm.aestronglyMeasurable (M / (1 - a)) (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (discountPow_nonneg ha0.le _)]
    calc discountPow a (τ ω) *
          |⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π
            (Function.update x i (ω (τ ω).toNat))|
        ≤ 1 * (M / (1 - a)) :=
          mul_le_mul (discountPow_le_one ha0.le ha1.le _)
            (iSup_markovBanditDiscountedValue_abs_le P hM ha0 ha1 i _)
            (abs_nonneg _) zero_le_one
      _ = M / (1 - a) := one_mul _
  have hint_shift :
      (∫ ω, discountPow a (τ ω) *
          (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r' a π
            (Function.update x i (ω (τ ω).toNat))) ∂markovChainMeasure P (x i)) =
      (∫ ω, discountPow a (τ ω) *
          (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π
            (Function.update x i (ω (τ ω).toNat))) ∂markovChainMeasure P (x i)) +
      (M / (1 - a)) * ∫ ω, discountPow a (τ ω) ∂markovChainMeasure P (x i) := by
    have hcongr : (fun ω : ℕ → T ↦ discountPow a (τ ω) *
        (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r' a π
          (Function.update x i (ω (τ ω).toNat)))) =
        fun ω ↦ discountPow a (τ ω) *
          (⨆ π : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π
            (Function.update x i (ω (τ ω).toNat))) +
        (M / (1 - a)) * discountPow a (τ ω) := by
      funext ω
      rw [iSup_markovBanditDiscountedValue_add_const P ⟨M, hM⟩ M ha0 ha1 i]
      ring
    rw [hcongr, integral_add hV_int (hdp_int.const_mul (M / (1 - a))), integral_const_mul]
  rw [hint_shift] at hmain
  have hW_id : stoppedTime P a τ (x i) =
      (1 - ∫ ω, discountPow a (τ ω) ∂markovChainMeasure P (x i)) / (1 - a) := by
    unfold stoppedTime
    simp_rw [discountedStoppedSum_one_eq_div ha0 ha1]
    rw [integral_div, integral_sub (integrable_const 1) hdp_int]
    simp
  have hcancel : M * stoppedTime P a τ (x i) +
      (M / (1 - a)) * ∫ ω, discountPow a (τ ω) ∂markovChainMeasure P (x i) = M / (1 - a) := by
    rw [hW_id]
    have h1a : 1 - a ≠ 0 := (sub_pos.2 ha1).ne'
    field_simp [h1a]
    ring
  linarith

