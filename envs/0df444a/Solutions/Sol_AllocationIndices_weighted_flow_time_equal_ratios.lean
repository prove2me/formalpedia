-- Prove2me | solution 1 for AllocationIndices.weighted_flow_time_equal_ratios
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T05:47:54.258793+00:00
-- url     : https://prove2.me/submissions/f9f4c30f-8bad-49b6-bec9-c69e2a1d1b24

import Mathlib
import Definitions.Def_AllocationIndices_Jobs

open MeasureTheory ProbabilityTheory BanditAlgorithm


namespace AllocationIndices

variable {n m : ℕ}

lemma wf_cs (σ : Schedule n m) (s : Fin n → ℝ) :
    ∑ i, s i * completionTime σ s i = ∑ i, ∑ i',
      if σ.machine i' = σ.machine i ∧ σ.pos i' ≤ σ.pos i then s i * s i' else 0 := by
  unfold completionTime
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter]

lemma wf_load (σ : Schedule n m) (s : Fin n → ℝ) :
    ∑ j, load σ s j ^ 2 = ∑ i, ∑ i',
      if σ.machine i' = σ.machine i then s i * s i' else 0 := by
  unfold load
  have e : ∀ j : Fin m, (∑ i : Fin n with σ.machine i = j, s i) ^ 2 =
      ∑ i : Fin n with σ.machine i = j, s i * ∑ i' : Fin n with σ.machine i' = σ.machine i, s i' := by
    intro j
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [hi.2, mul_comm]
  simp_rw [e]
  rw [Finset.sum_fiberwise (Finset.univ) (fun i => σ.machine i)
    (fun i => s i * ∑ i' : Fin n with σ.machine i' = σ.machine i, s i')]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter]

lemma wf_key (σ : Schedule n m) (s : Fin n → ℝ) :
    2 * ∑ i, s i * completionTime σ s i = ∑ j, load σ s j ^ 2 + ∑ i, s i ^ 2 := by
  rw [wf_cs, wf_load]
  set F : Fin n → Fin n → ℝ := fun i i' => if σ.machine i' = σ.machine i then s i * s i' else 0
  set Le : Fin n → Fin n → ℝ := fun i i' =>
    if σ.machine i' = σ.machine i ∧ σ.pos i' ≤ σ.pos i then s i * s i' else 0
  set Lt : Fin n → Fin n → ℝ := fun i i' =>
    if σ.machine i' = σ.machine i ∧ σ.pos i' < σ.pos i then s i * s i' else 0
  set Gt : Fin n → Fin n → ℝ := fun i i' =>
    if σ.machine i' = σ.machine i ∧ σ.pos i < σ.pos i' then s i * s i' else 0
  set Dg : Fin n → Fin n → ℝ := fun i i' => if i' = i then s i * s i' else 0
  have hF : ∀ i i', F i i' = Le i i' + Gt i i' := by
    intro i i'
    simp only [F, Le, Gt]
    by_cases hm : σ.machine i' = σ.machine i
    · by_cases hp : σ.pos i' ≤ σ.pos i
      · rw [if_pos hm, if_pos ⟨hm, hp⟩, if_neg (fun h => absurd h.2 (not_lt.mpr hp))]; ring
      · rw [if_pos hm, if_neg (fun h => hp h.2), if_pos ⟨hm, lt_of_not_ge hp⟩]; ring
    · rw [if_neg hm, if_neg (fun h => hm h.1), if_neg (fun h => hm h.1)]; ring
  have hLe : ∀ i i', Le i i' = Lt i i' + Dg i i' := by
    intro i i'
    simp only [Le, Lt, Dg]
    by_cases he : i' = i
    · subst he
      rw [if_pos ⟨rfl, le_rfl⟩, if_neg (fun h => lt_irrefl _ h.2), if_pos rfl]; ring
    · rw [if_neg he]
      by_cases hm : σ.machine i' = σ.machine i
      · by_cases hp : σ.pos i' ≤ σ.pos i
        · have hlt : σ.pos i' < σ.pos i := by
            rcases hp.lt_or_eq with h | h
            · exact h
            · exact absurd (σ.pos_inj i' i hm h) he
          rw [if_pos ⟨hm, hp⟩, if_pos ⟨hm, hlt⟩]; ring
        · rw [if_neg (fun h => hp h.2), if_neg (fun h => hp h.2.le)]; ring
      · rw [if_neg (fun h => hm h.1), if_neg (fun h => hm h.1)]; ring
  have hsym : ∑ i, ∑ i', Gt i i' = ∑ i, ∑ i', Lt i i' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    simp only [Gt, Lt]
    by_cases h : σ.machine i' = σ.machine i ∧ σ.pos i' < σ.pos i
    · rw [if_pos ⟨h.1.symm, h.2⟩, if_pos h]; ring
    · rw [if_neg (fun h' => h ⟨h'.1.symm, h'.2⟩), if_neg h]
  have hdiag : ∑ i, ∑ i', Dg i i' = ∑ i, s i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Dg]
    rw [Finset.sum_ite_eq']
    simp [sq]
  have hsumF : ∑ i, ∑ i', F i i' = ∑ i, ∑ i', Le i i' + ∑ i, ∑ i', Gt i i' := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i' _ => hF i i'
  have hsumLe : ∑ i, ∑ i', Le i i' = ∑ i, ∑ i', Lt i i' + ∑ i, ∑ i', Dg i i' := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i' _ => hLe i i'
  show 2 * ∑ i, ∑ i', Le i i' = ∑ i, ∑ i', F i i' + ∑ i, s i ^ 2
  rw [hsumF, hsym, hsumLe, hdiag]
  ring

theorem wf_main (σ : Schedule n m) (s c : Fin n → ℝ)
    (hm : 0 < m) {κ : ℝ} (hc : ∀ i, c i = κ * s i) :
    weightedFlowTime σ s c =
      κ / 2 * (∑ i, s i ^ 2 + (∑ i, s i) ^ 2 / m + ∑ j, loadDeviation σ s j ^ 2) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have htot : ∑ j, load σ s j = ∑ i, s i := by
    unfold load
    exact Finset.sum_fiberwise Finset.univ (fun i => σ.machine i) s
  have hdev : ∑ j, loadDeviation σ s j ^ 2 = ∑ j, load σ s j ^ 2 - (∑ i, s i) ^ 2 / m := by
    unfold loadDeviation
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum, htot]
    field_simp
    ring
  have hw : weightedFlowTime σ s c = κ * ∑ i, s i * completionTime σ s i := by
    unfold weightedFlowTime
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hc]; ring
  have hk := wf_key σ s
  rw [hw, hdev]
  linear_combination (κ / 2) * hk

end AllocationIndices

open AllocationIndices

theorem solution {n m : ℕ} (σ : Schedule n m) (s c : Fin n → ℝ)
    (hm : 0 < m) {κ : ℝ} (hc : ∀ i, c i = κ * s i) :
    weightedFlowTime σ s c =
      κ / 2 * (∑ i, s i ^ 2 + (∑ i, s i) ^ 2 / m + ∑ j, loadDeviation σ s j ^ 2) := by
  exact wf_main σ s c hm hc
