-- Prove2me | solution 1 for AlgMechDesign.Local.ratio_step
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:47:46.924091+00:00
-- url     : https://prove2.me/submissions/b0384e2a-42bf-43f5-a8d7-09fcb7a46dd8

import Definitions.Def_AlgMechDesign_Local_Model

set_option autoImplicit false
open AlgMechDesign.Local Finset

theorem solution {n k : ℕ} [NeZero n] (s : Fin n → Fin k → ℝ) (x : Fin k → Fin n) (a : Fin n)
    (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hcard : (univ.filter (fun j => x j = a)).card = n)
    (hlow : ∀ j, x j = a → 1 - δ ≤ s a j) (hup : ∀ l j, s l j ≤ 1 + δ)
    (hsmall : ∀ l j, l ≠ a → x j = l → s l j ≤ ε) :
    (n : ℝ) * (1 - δ) ≤ makespan s x ∧
      ∃ y : Fin k → Fin n, makespan s y ≤ 1 + δ + k * ε := by
  classical
  constructor
  · have hload : (n : ℝ) * (1 - δ) ≤ load s x a := by
      unfold load
      calc
        (n : ℝ) * (1 - δ) = ∑ _j ∈ univ.filter (fun j => x j = a), (1 - δ) := by simp [hcard]; ring
        _ ≤ _ := Finset.sum_le_sum (fun j hj => hlow j (Finset.mem_filter.mp hj).2)
    exact hload.trans (Finset.le_sup' (load s x) (Finset.mem_univ a))
  · let H := univ.filter (fun j => x j = a)
    let e : H ≃ Fin n := Finset.equivFinOfCardEq hcard
    let y : Fin k → Fin n := fun j => if h : j ∈ H then e ⟨j, h⟩ else x j
    refine ⟨y, ?_⟩
    unfold makespan
    apply Finset.sup'_le
    intro l hl
    let S := univ.filter (fun j => y j = l)
    have hheavy : (S.filter (fun j => x j = a)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j hj q hq
      have hjH : j ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
      have hqH : q ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
      have hjl := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
      have hql := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
      have hej : e ⟨j, hjH⟩ = l := by simpa [y, hjH] using hjl
      have heq : e ⟨q, hqH⟩ = l := by simpa [y, hqH] using hql
      exact congrArg Subtype.val (e.injective (hej.trans heq.symm))
    have hS : S.card ≤ k := by
      simpa using Finset.card_le_card (Finset.filter_subset (fun j => y j = l) univ)
    have hpoint : ∀ j ∈ S, s l j ≤ (if x j = a then 1 + δ else 0) + ε := by
      intro j hj
      have hjl := (Finset.mem_filter.mp hj).2
      by_cases he : x j = a
      · simp only [if_pos he]
        linarith [hup l j]
      · have hjH : j ∉ H := by simpa [H] using he
        have hxl : x j = l := by simpa [y, hjH] using hjl
        have hla : l ≠ a := by intro h; exact he (hxl.trans h)
        simpa only [if_neg he, zero_add] using hsmall l j hla hxl
    change ∑ j ∈ S, s l j ≤ _
    calc
      ∑ j ∈ S, s l j ≤ ∑ j ∈ S, ((if x j = a then 1 + δ else 0) + ε) :=
        Finset.sum_le_sum hpoint
      _ = ((S.filter (fun j => x j = a)).card : ℝ) * (1 + δ) + (S.card : ℝ) * ε := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp
        ring
      _ ≤ 1 + δ + k * ε := by
        have hc : ((S.filter (fun j => x j = a)).card : ℝ) ≤ 1 := by exact_mod_cast hheavy
        have hs : (S.card : ℝ) ≤ k := by exact_mod_cast hS
        have hm := mul_le_mul_of_nonneg_right hc (by linarith : 0 ≤ 1 + δ)
        have he := mul_le_mul_of_nonneg_right hs hε
        nlinarith
