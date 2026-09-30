-- Prove2me | solution 1 for AlgMechDesign.LowerBound.ratio_step_even
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:15:47.247894+00:00
-- url     : https://prove2.me/submissions/c8e232c7-ac6f-4572-adea-73daf9a83402

import Theorems.Thm_AlgMechDesign_LowerBound_claim_4_8

set_option autoImplicit false
open AlgMechDesign.LowerBound Finset

theorem solution {k : ℕ} (hk : 3 ≤ k) (alloc : (Fin 2 → Fin k → ℝ) → (Fin k → Fin 2))
    (pay : (Fin 2 → Fin k → ℝ) → Fin 2 → ℝ) (htruth : IsTruthful alloc pay)
    (t : Fin 2 → Fin k → ℝ) (ht : t = fun _ _ => 1)
    (hcard : (taskSet (alloc t) 0).card ≤ (taskSet (alloc t) 1).card)
    (heven : Even (taskSet (alloc t) 1).card)
    (x : Finset (Fin k)) (hx : x = taskSet (alloc t) 0)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (that : Fin 2 → Fin k → ℝ)
    (hthat : that = Function.update t 0 (fun j => if j ∈ x then ε else 1 + ε)) :
    makespan that (alloc that) = ((taskSet (alloc t) 1).card : ℝ) ∧
      ∃ y : Fin k → Fin 2,
        makespan that y ≤ ((taskSet (alloc t) 1).card : ℝ) / 2 + (k : ℝ) * ε := by
  classical
  have halloc := claim_4_8 hk alloc pay htruth t ht hcard x hx ε hε0 hε1 that hthat
  let Y := taskSet (alloc t) 1
  have htime0 : ∀ j, that 0 j = if j ∈ x then ε else 1 + ε := by intro j; simp [hthat]
  have htime1 : ∀ j, that 1 j = 1 := by intro j; simp [hthat, ht]
  have hload0 : load that (alloc t) 0 = (x.card : ℝ) * ε := by
    unfold load taskTime
    rw [← hx]
    simp_rw [htime0]
    rw [Finset.sum_congr rfl (fun j hj => if_pos hj)]
    simp
  have hload1 : load that (alloc t) 1 = (Y.card : ℝ) := by
    unfold load taskTime
    simp_rw [htime1]
    simp [Y]
  have hsmall : (x.card : ℝ) * ε ≤ Y.card := by
    have hc : (x.card : ℝ) ≤ Y.card := by exact_mod_cast (show x.card ≤ Y.card by simpa [hx, Y] using hcard)
    have hn : (0 : ℝ) ≤ x.card := Nat.cast_nonneg _
    nlinarith
  constructor
  · rw [halloc]
    apply le_antisymm
    · unfold makespan
      apply Finset.sup'_le
      intro l hl
      fin_cases l
      · simpa [hload0] using hsmall
      · exact le_of_eq hload1
    · rw [← hload1]
      exact Finset.le_sup' (load that (alloc t)) (Finset.mem_univ _)
  · obtain ⟨q, hq⟩ := heven
    have hqY : Y.card = q + q := hq
    have hqle : q ≤ Y.card := by omega
    obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hqle
    have hdis : Disjoint x S := by
      apply Finset.disjoint_left.mpr
      intro j hjx hjS
      have h0 : alloc t j = 0 := by
        have hmem : j ∈ taskSet (alloc t) 0 := hx ▸ hjx
        exact (Finset.mem_filter.mp hmem).2
      have h1 : alloc t j = 1 := (Finset.mem_filter.mp (hS hjS)).2
      exact Fin.zero_ne_one (h0.symm.trans h1)
    let y : Fin k → Fin 2 := fun j => if j ∈ S then 0 else alloc t j
    have hy0 : taskSet y 0 = x ∪ S := by
      ext j
      by_cases hj : j ∈ S
      · simp [taskSet, y, hj]
      · simp [taskSet, y, hj, hx]
    have hy1 : taskSet y 1 = Y \ S := by
      ext j
      by_cases hj : j ∈ S
      · simp [taskSet, y, hj]
      · simp [taskSet, y, hj, Y]
    have hcardY : ((Y \ S).card : ℝ) = q := by
      rw [Finset.card_sdiff_of_subset hS, hScard]
      have : Y.card - q = q := by omega
      rw [this]
    have hcardU : (x.card : ℝ) + q ≤ k := by
      have hh := Finset.card_le_card (Finset.subset_univ (x ∪ S))
      rw [Finset.card_union_of_disjoint hdis, hScard, Finset.card_univ, Fintype.card_fin] at hh
      exact_mod_cast hh
    have hnew0 : load that y 0 = (x.card : ℝ) * ε + (q : ℝ) * (1 + ε) := by
      unfold load taskTime
      rw [hy0, Finset.sum_union hdis]
      congr 1
      · simp_rw [htime0]
        rw [Finset.sum_congr rfl (fun j hj => if_pos hj)]
        simp
      · simp_rw [htime0]
        have hf : ∀ j ∈ S, j ∉ x := fun j hj hxj => Finset.disjoint_left.mp hdis hxj hj
        rw [Finset.sum_congr rfl (fun j hj => if_neg (hf j hj))]
        simp [hScard]
        ring
    have hnew1 : load that y 1 = (q : ℝ) := by
      unfold load taskTime
      rw [hy1]
      simp_rw [htime1]
      simpa using hcardY
    have hhalf : (Y.card : ℝ) / 2 = q := by
      have hh : (Y.card : ℝ) = (q : ℝ) + q := by exact_mod_cast hqY
      linarith
    refine ⟨y, ?_⟩
    change makespan that y ≤ (Y.card : ℝ) / 2 + k * ε
    rw [hhalf]
    unfold makespan
    apply Finset.sup'_le
    intro l hl
    fin_cases l
    · change load that y 0 ≤ _
      rw [hnew0]
      nlinarith [mul_le_mul_of_nonneg_right hcardU (le_of_lt hε0)]
    · change load that y 1 ≤ _
      rw [hnew1]
      have hm := mul_nonneg (Nat.cast_nonneg k) (le_of_lt hε0)
      linarith
