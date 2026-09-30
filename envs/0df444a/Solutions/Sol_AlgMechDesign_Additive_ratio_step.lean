-- Prove2me | solution 1 for AlgMechDesign.Additive.ratio_step
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:49:17.335977+00:00
-- url     : https://prove2.me/submissions/e71423e2-13cc-436d-98c2-f3593e912d8c

import Definitions.Def_AlgMechDesign_Additive_Model

set_option autoImplicit false
open AlgMechDesign.Additive Finset

theorem solution {n k : ℕ} [NeZero n] (i : Fin n) (x : Finset (Fin k)) (hx : x.card = n)
    (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    (∀ z : Fin k → Fin n, x ⊆ taskSet z i →
        (1 - ε) * n ≤ makespan (Function.update (fun _ _ => (1 : ℝ)) i
          (fun j => if j ∈ x then 1 - ε else ε)) z) ∧
      ∃ y : Fin k → Fin n,
        makespan (Function.update (fun _ _ => (1 : ℝ)) i
          (fun j => if j ∈ x then 1 - ε else ε)) y ≤ 1 + k * ε := by
  classical
  let t := Function.update (fun _ _ => (1 : ℝ)) i (fun j => if j ∈ x then 1 - ε else ε)
  constructor
  · intro z hz
    have hload : (1 - ε) * n ≤ load t z i := by
      unfold load
      calc
        (1 - ε) * n = ∑ _j ∈ x, (1 - ε) := by simp [hx]; ring
        _ = ∑ j ∈ x, t i j := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [t, hj]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hz (fun j hj hj' => by
          simp only [t, Function.update_self]
          split_ifs <;> linarith)
    exact hload.trans (Finset.le_sup' (load t z) (Finset.mem_univ i))
  · let e : x ≃ Fin n := Finset.equivFinOfCardEq hx
    let y : Fin k → Fin n := fun j => if h : j ∈ x then e ⟨j, h⟩ else i
    refine ⟨y, ?_⟩
    change makespan t y ≤ _
    unfold makespan
    apply Finset.sup'_le
    intro l hl
    let S := taskSet y l
    have hheavy : (S.filter (fun j => j ∈ x)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j hj q hq
      have hjx := (Finset.mem_filter.mp hj).2
      have hqx := (Finset.mem_filter.mp hq).2
      have hjl := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
      have hql := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
      have hej : e ⟨j, hjx⟩ = l := by simpa [y, hjx] using hjl
      have heq : e ⟨q, hqx⟩ = l := by simpa [y, hqx] using hql
      exact congrArg Subtype.val (e.injective (hej.trans heq.symm))
    have hS : S.card ≤ k := by
      simpa [S, taskSet] using Finset.card_le_card (Finset.filter_subset (fun j => y j = l) univ)
    have hpoint : ∀ j ∈ S, t l j ≤ (if j ∈ x then 1 else 0) + ε := by
      intro j hj
      have hjl := (Finset.mem_filter.mp hj).2
      by_cases he : j ∈ x
      · simp only [if_pos he]
        by_cases hli : l = i
        · simp [t, hli, he]
          linarith
        · simp [t, hli]
          linarith
      · have hil : i = l := by simpa [y, he] using hjl
        simp [t, ← hil, he]
    change ∑ j ∈ S, t l j ≤ _
    calc
      ∑ j ∈ S, t l j ≤ ∑ j ∈ S, ((if j ∈ x then (1 : ℝ) else 0) + ε) :=
        Finset.sum_le_sum hpoint
      _ = ((S.filter (fun j => j ∈ x)).card : ℝ) + (S.card : ℝ) * ε := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp
      _ ≤ 1 + k * ε := by
        have hc : ((S.filter (fun j => j ∈ x)).card : ℝ) ≤ 1 := by exact_mod_cast hheavy
        have hs : (S.card : ℝ) ≤ k := by exact_mod_cast hS
        have he := mul_le_mul_of_nonneg_right hs (le_of_lt hε₀)
        linarith
