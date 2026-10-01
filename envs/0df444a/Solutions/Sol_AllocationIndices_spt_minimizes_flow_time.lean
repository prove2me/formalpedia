-- Prove2me | solution 1 for AllocationIndices.spt_minimizes_flow_time
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T11:46:02.142449+00:00
-- url     : https://prove2.me/submissions/5efa0a97-3a04-4f05-a9de-963386eca00b

import Mathlib
import Definitions.Def_AllocationIndices_Jobs

set_option autoImplicit false

open MeasureTheory ProbabilityTheory BanditAlgorithm Finset

namespace AllocationIndices

namespace SPTProof2c4f

variable {n m : ℕ}

lemma flowTime_eq (σ : Schedule n m) (s : Fin n → ℝ) :
    flowTime σ s = ∑ i, s i * (levelFromEnd σ i : ℝ) := by
  unfold flowTime completionTime levelFromEnd
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hf : (({i | σ.machine j = σ.machine i ∧ σ.pos j ≤ σ.pos i} : Finset (Fin n))) =
      ({i | σ.machine i = σ.machine j ∧ σ.pos j ≤ σ.pos i} : Finset (Fin n)) := by
    apply Finset.filter_congr
    intro i _
    exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩
  rw [hf]

lemma level_pos (σ : Schedule n m) (i : Fin n) : 1 ≤ levelFromEnd σ i := by
  unfold levelFromEnd
  exact Finset.card_pos.mpr ⟨i, by simp⟩

lemma level_lt_of_pos_lt (σ : Schedule n m) {i j : Fin n} (hm : σ.machine i = σ.machine j)
    (hp : σ.pos i < σ.pos j) : levelFromEnd σ j < levelFromEnd σ i := by
  unfold levelFromEnd
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i, by simp, ?_⟩
    simp only [mem_filter, mem_univ, true_and, not_and, not_le]
    intro _
    exact hp
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact ⟨hk.1.trans hm.symm, hp.le.trans hk.2⟩

lemma level_inj (σ : Schedule n m) {i j : Fin n} (hm : σ.machine i = σ.machine j)
    (hl : levelFromEnd σ i = levelFromEnd σ j) : i = j := by
  rcases lt_trichotomy (σ.pos i) (σ.pos j) with h | h | h
  · exact absurd hl (level_lt_of_pos_lt σ hm h).ne'
  · exact σ.pos_inj i j hm h
  · exact absurd hl (level_lt_of_pos_lt σ hm.symm h).ne

lemma level_feasible (σ : Schedule n m) (r : ℕ) :
    #{i | levelFromEnd σ i ≤ r} ≤ r * m := by
  rw [Finset.card_eq_sum_card_fiberwise (f := σ.machine) (t := univ) (fun _ _ => mem_univ _)]
  calc _ ≤ ∑ _c : Fin m, r := by
        refine Finset.sum_le_sum fun c _ => ?_
        calc _ ≤ #(Finset.Icc 1 r) := by
              refine Finset.card_le_card_of_injOn (levelFromEnd σ) ?_ ?_
              · intro i hi
                simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq,
                  mem_coe, coe_Icc, Set.mem_Icc] at hi ⊢
                exact ⟨level_pos σ i, hi.1⟩
              · intro i hi j hj hij
                simp only [coe_filter, mem_filter, mem_univ, true_and, Set.mem_setOf_eq,
                  mem_coe] at hi hj
                exact level_inj σ (hi.2.trans hj.2.symm) hij
          _ = r := by simp
    _ = r * m := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

lemma exists_rank {α : Type*} [LinearOrder α] (f : Fin n → α) :
    ∃ e : Fin n ≃ Fin n, ∀ i j, f i < f j → e i < e j := by
  refine ⟨(Tuple.sort f).symm, fun i j hij => ?_⟩
  by_contra h
  push_neg at h
  have := Tuple.monotone_sort f h
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
  exact absurd hij (not_lt.mpr this)

lemma card_le_rank (e : Fin n ≃ Fin n) (i : Fin n) : #{j | e j ≤ e i} = (e i : ℕ) + 1 := by
  rw [Finset.card_equiv e (t := Finset.Iic (e i)) (by intro j; simp)]
  exact Fin.card_Iic _

lemma rank_le_level (hm : 0 < m) (σ : Schedule n m) (τ : Fin n ≃ Fin n)
    (hτ : ∀ i j, levelFromEnd σ i < levelFromEnd σ j → τ i < τ j) (i : Fin n) :
    (τ i : ℕ) / m + 1 ≤ levelFromEnd σ i := by
  have h1 : (τ i : ℕ) + 1 ≤ levelFromEnd σ i * m := by
    rw [← card_le_rank τ i]
    refine le_trans (Finset.card_le_card ?_) (level_feasible σ _)
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    by_contra h
    push_neg at h
    exact absurd (hτ i j h) (not_lt.mpr hj)
  have h2 : (τ i : ℕ) / m < levelFromEnd σ i := by
    rw [Nat.div_lt_iff_lt_mul hm]
    omega
  omega

lemma rankAsc_lt_of_lt (s : Fin n → ℝ) {i j : Fin n} (h : s j < s i) :
    rankAsc s j < rankAsc s i := by
  unfold rankAsc
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨j, by simp [h], by simp⟩
  · intro k hk
    simp only [mem_filter, mem_univ, true_and] at hk ⊢
    rcases hk with hk | ⟨hk1, _⟩
    · exact Or.inl (hk.trans h)
    · exact Or.inl (hk1.trans_lt h)

lemma rankAsc_inj (s : Fin n → ℝ) {i j : Fin n} (h : rankAsc s i = rankAsc s j) : i = j :=
  (sptSchedule (m := 1) s Nat.one_pos).pos_inj i j (Subsingleton.elim _ _)
    (by show rankAsc s i / 1 = rankAsc s j / 1; rw [h])

lemma rankAsc_lt (s : Fin n → ℝ) (i : Fin n) : rankAsc s i < n := by
  unfold rankAsc
  calc _ < #(univ : Finset (Fin n)) := by
        apply Finset.card_lt_card
        rw [Finset.filter_ssubset]
        exact ⟨i, mem_univ _, by simp⟩
    _ = n := by simp

lemma exists_e0 (s : Fin n → ℝ) :
    ∃ e0 : Fin n ≃ Fin n, ∀ i, (e0 i : ℕ) = n - 1 - rankAsc s i := by
  let f : Fin n → Fin n := fun i => ⟨n - 1 - rankAsc s i, by have := rankAsc_lt s i; omega⟩
  have hf : Function.Injective f := by
    intro i j h
    have h1 := rankAsc_lt s i
    have h2 := rankAsc_lt s j
    have : n - 1 - rankAsc s i = n - 1 - rankAsc s j := congrArg Fin.val h
    exact rankAsc_inj s (by omega)
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), fun i => rfl⟩

lemma spt_level_le (s : Fin n → ℝ) (hm : 0 < m) (i : Fin n) :
    levelFromEnd (sptSchedule s hm) i ≤ (n - 1 - rankAsc s i) / m + 1 := by
  unfold levelFromEnd
  rw [← Finset.card_range ((n - 1 - rankAsc s i) / m + 1)]
  have key : ∀ j : Fin n, j ∈ ({j | (sptSchedule s hm).machine j = (sptSchedule s hm).machine i ∧
      (sptSchedule s hm).pos i ≤ (sptSchedule s hm).pos j} : Finset (Fin n)) →
      rankAsc s j % m = rankAsc s i % m ∧ rankAsc s i / m ≤ rankAsc s j / m := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    exact ⟨congrArg Fin.val hj.1, hj.2⟩
  apply Finset.card_le_card_of_injOn (fun j => rankAsc s j / m - rankAsc s i / m)
  · intro j hj
    obtain ⟨hmod, hdiv⟩ := key j hj
    simp only [mem_coe, mem_range]
    have hj' := rankAsc_lt s j
    have e1 : rankAsc s j / m * m + rankAsc s j % m = rankAsc s j := Nat.div_add_mod' _ _
    have e2 : rankAsc s i / m * m + rankAsc s i % m = rankAsc s i := Nat.div_add_mod' _ _
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hm, Nat.sub_mul]
    have hle : rankAsc s i / m * m ≤ rankAsc s j / m * m := Nat.mul_le_mul_right _ hdiv
    generalize rankAsc s j / m * m = X at *
    generalize rankAsc s i / m * m = Y at *
    omega
  · intro j1 hj1 j2 hj2 hjj
    obtain ⟨hmod1, hdiv1⟩ := key j1 hj1
    obtain ⟨hmod2, hdiv2⟩ := key j2 hj2
    simp only at hjj
    have hq : rankAsc s j1 / m = rankAsc s j2 / m := by omega
    apply rankAsc_inj s
    rw [← Nat.div_add_mod (rankAsc s j1) m, ← Nat.div_add_mod (rankAsc s j2) m, hq, hmod1, hmod2]

lemma antivary_of_rank (s : Fin n → ℝ) (e : Fin n ≃ Fin n)
    (he : ∀ i j, s j < s i → e i < e j) :
    Antivary s (fun i => ((((e i : ℕ) / m + 1 : ℕ)) : ℝ)) := by
  intro i j hg
  by_contra hlt
  push_neg at hlt
  have h1 : e j < e i := he j i hlt
  have h2 : (e j : ℕ) / m ≤ (e i : ℕ) / m := Nat.div_le_div_right (le_of_lt h1)
  have h3 : ((((e j : ℕ) / m + 1 : ℕ)) : ℝ) ≤ ((((e i : ℕ) / m + 1 : ℕ)) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right h2 1
  exact absurd hg (not_lt.mpr h3)

lemma rearr_le (s : Fin n → ℝ) (e τ : Fin n ≃ Fin n) (he : ∀ i j, s j < s i → e i < e j) :
    ∑ i, s i * ((((e i : ℕ) / m + 1 : ℕ)) : ℝ) ≤ ∑ i, s i * ((((τ i : ℕ) / m + 1 : ℕ)) : ℝ) := by
  have := (antivary_of_rank (m := m) s e he).sum_mul_le_sum_mul_comp_perm (σ := τ.trans e.symm)
  simpa [Equiv.trans_apply, Equiv.apply_symm_apply] using this

lemma rearr_eq_iff (s : Fin n → ℝ) (e τ : Fin n ≃ Fin n) (he : ∀ i j, s j < s i → e i < e j) :
    ∑ i, s i * ((((τ i : ℕ) / m + 1 : ℕ)) : ℝ) = ∑ i, s i * ((((e i : ℕ) / m + 1 : ℕ)) : ℝ) ↔
      Antivary s (fun i => ((((τ i : ℕ) / m + 1 : ℕ)) : ℝ)) := by
  have := (antivary_of_rank (m := m) s e he).sum_mul_eq_sum_mul_comp_perm_iff
    (σ := τ.trans e.symm)
  have hc : ((fun i => ((((e i : ℕ) / m + 1 : ℕ)) : ℝ)) ∘ (τ.trans e.symm)) =
      (fun i => ((((τ i : ℕ) / m + 1 : ℕ)) : ℝ)) := by
    funext i; simp [Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [hc] at this
  simpa [Equiv.trans_apply, Equiv.apply_symm_apply] using this

lemma exists_tau (hm : 0 < m) (s : Fin n → ℝ) (σ : Schedule n m) :
    ∃ τ : Fin n ≃ Fin n, (∀ i, (τ i : ℕ) / m + 1 ≤ levelFromEnd σ i) ∧
      (∀ i j, levelFromEnd σ i < levelFromEnd σ j → τ i < τ j) ∧
      (∀ i j, levelFromEnd σ i = levelFromEnd σ j → s j < s i → τ i < τ j) := by
  obtain ⟨τ, hτ⟩ := exists_rank (fun i => toLex (levelFromEnd σ i, -s i))
  have hA : ∀ i j, levelFromEnd σ i < levelFromEnd σ j → τ i < τ j := by
    intro i j h
    exact hτ i j (Prod.Lex.toLex_lt_toLex.mpr (Or.inl h))
  refine ⟨τ, rank_le_level hm σ τ hA, hA, fun i j hl hs => ?_⟩
  exact hτ i j (Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hl, by simpa using hs⟩))

end SPTProof2c4f

end AllocationIndices

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices Finset in
theorem solution {n m : ℕ} (hm : 0 < m) (s : Fin n → ℝ) (hs : ∀ i, 0 < s i) :
    (∀ σ : Schedule n m, flowTime (sptSchedule s hm) s ≤ flowTime σ s) ∧
    (∀ σ : Schedule n m,
      flowTime σ s = flowTime (sptSchedule s hm) s ↔
        ∃ e : Fin n ≃ Fin n, (∀ i j, s j < s i → e i < e j) ∧
          ∀ i, levelFromEnd σ i = (e i : ℕ) / m + 1) := by
  obtain ⟨e0, he0⟩ := SPTProof2c4f.exists_e0 s
  have he0r : ∀ i j, s j < s i → e0 i < e0 j := by
    intro i j h
    have h1 := SPTProof2c4f.rankAsc_lt_of_lt s h
    have h2 := SPTProof2c4f.rankAsc_lt s i
    rw [Fin.lt_iff_val_lt_val, he0, he0]
    omega
  -- lower bound for any schedule
  have lower : ∀ σ : Schedule n m, ∀ τ : Fin n ≃ Fin n,
      (∀ i, (τ i : ℕ) / m + 1 ≤ levelFromEnd σ i) →
      ∑ i, s i * ((((τ i : ℕ) / m + 1 : ℕ)) : ℝ) ≤ flowTime σ s := by
    intro σ τ hτ
    rw [SPTProof2c4f.flowTime_eq]
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hτ i) (hs i).le
  have lowerW : ∀ σ : Schedule n m,
      ∑ i, s i * ((((e0 i : ℕ) / m + 1 : ℕ)) : ℝ) ≤ flowTime σ s := by
    intro σ
    obtain ⟨τ, hτ1, _, _⟩ := SPTProof2c4f.exists_tau hm s σ
    exact (SPTProof2c4f.rearr_le s e0 τ he0r).trans (lower σ τ hτ1)
  have hspt : flowTime (sptSchedule s hm) s = ∑ i, s i * ((((e0 i : ℕ) / m + 1 : ℕ)) : ℝ) := by
    refine le_antisymm ?_ (lowerW _)
    rw [SPTProof2c4f.flowTime_eq]
    refine Finset.sum_le_sum fun i _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hs i).le
    rw [he0]
    exact_mod_cast SPTProof2c4f.spt_level_le s hm i
  refine ⟨fun σ => hspt ▸ lowerW σ, fun σ => ⟨fun hEq => ?_, fun ⟨e, he, hl⟩ => ?_⟩⟩
  · obtain ⟨τ, hτ1, hτ2, hτ3⟩ := SPTProof2c4f.exists_tau hm s σ
    have hW1 := SPTProof2c4f.rearr_le (m := m) s e0 τ he0r
    have hW2 := lower σ τ hτ1
    have hWτ : ∑ i, s i * ((((τ i : ℕ) / m + 1 : ℕ)) : ℝ) =
        ∑ i, s i * ((((e0 i : ℕ) / m + 1 : ℕ)) : ℝ) := by linarith
    have hanti := (SPTProof2c4f.rearr_eq_iff s e0 τ he0r).mp hWτ
    have hflow : flowTime σ s = ∑ i, s i * ((((τ i : ℕ) / m + 1 : ℕ)) : ℝ) := by linarith
    rw [SPTProof2c4f.flowTime_eq] at hflow
    have hzero : ∑ i, (s i * (levelFromEnd σ i : ℝ) - s i * ((((τ i : ℕ) / m + 1 : ℕ)) : ℝ)) = 0 := by
      rw [Finset.sum_sub_distrib, hflow, sub_self]
    have hnn : ∀ i ∈ (univ : Finset (Fin n)),
        0 ≤ s i * (levelFromEnd σ i : ℝ) - s i * ((((τ i : ℕ) / m + 1 : ℕ)) : ℝ) := by
      intro i _
      have : ((((τ i : ℕ) / m + 1 : ℕ)) : ℝ) ≤ (levelFromEnd σ i : ℝ) := by exact_mod_cast hτ1 i
      nlinarith [hs i]
    have hpt := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero
    have hlev : ∀ i, levelFromEnd σ i = (τ i : ℕ) / m + 1 := by
      intro i
      have h1 := hpt i (mem_univ _)
      have h2 : s i * ((levelFromEnd σ i : ℝ) - ((((τ i : ℕ) / m + 1 : ℕ)) : ℝ)) = 0 := by
        rw [mul_sub]; exact h1
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h (hs i).ne'
      · exact_mod_cast sub_eq_zero.mp h
    refine ⟨τ, fun i j hij => ?_, hlev⟩
    rcases lt_trichotomy (levelFromEnd σ i) (levelFromEnd σ j) with h | h | h
    · exact hτ2 i j h
    · exact hτ3 i j h hij
    · exfalso
      have hc : ((((τ j : ℕ) / m + 1 : ℕ)) : ℝ) < ((((τ i : ℕ) / m + 1 : ℕ)) : ℝ) := by
        rw [← hlev i, ← hlev j]; exact_mod_cast h
      have := hanti hc
      linarith
  · have hfe : flowTime σ s = ∑ i, s i * ((((e i : ℕ) / m + 1 : ℕ)) : ℝ) := by
      rw [SPTProof2c4f.flowTime_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hl i]
    rw [hfe, hspt]
    exact le_antisymm (SPTProof2c4f.rearr_le s e e0 he) (SPTProof2c4f.rearr_le s e0 e he0r)

