-- Prove2me | solution 1 for Apery.inner_table_k_93_124
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T18:30:30.009901+00:00
-- url     : https://prove2.me/submissions/222885a7-6195-4a4c-ab35-8b0bd2ae1c88

/-
# Inner table k-ranges, pieces 93-124 (source `Apery/Growth/InnerSum.lean`)

A block of the certificate `inner_table_k`: for each piece and $
t_i \le x < t_{i+1}$ the floor is frozen by `nat_floor_of_bounds`. Port of
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0 (split for size).
-/

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

set_option autoImplicit false

section Port0
set_option autoImplicit false
set_option maxHeartbeats 4000000

open Finset

namespace Apery

lemma nat_floor_of_bounds {x : ℝ} {q : ℕ} (h1 : (q : ℝ) ≤ x) (h2 : x < q + 1) : ⌊x⌋₊ = q := by
  rw [Nat.floor_eq_iff (by linarith)]; exact ⟨h1, h2⟩

theorem inner_table_k_93_124 : ∀ i, 93 ≤ i → i ≤ 124 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), -2 * (⌊x⌋₊ : ℤ) - 6 ≤ kIn i ∧ kIn i ≤ 8 * (⌊x⌋₊ : ℤ) + 20 := by
  intro i _ _ x hx
  interval_cases i
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 15) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 15) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 15) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 16) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 16) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 16) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 16) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 16) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 16) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 16) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 16) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 16) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 17) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 17) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 17) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 17) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 17) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 17) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 17) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 18) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 18) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 18) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 18) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 18) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 18) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 18) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 19) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 19) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 19) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 19) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 19) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num
  · simp only [tIn, tInL, kIn, kInL, List.getD_cons_succ, List.getD_cons_zero, Set.mem_Ico] at hx ⊢
    push_cast at hx
    rw [nat_floor_of_bounds (q := 19) (by norm_num; linarith [hx.1]) (by norm_num; linarith [hx.2])]
    norm_num

end Apery
end Port0


open Finset in
/-- The platform target `Apery.inner_table_k_93_124`, restated at top level as `solution`. -/
theorem solution : ∀ i, 93 ≤ i → i ≤ 124 → ∀ x ∈ Set.Ico (Apery.tIn i) (Apery.tIn (i + 1)),
    -2 * (⌊x⌋₊ : ℤ) - 6 ≤ Apery.kIn i ∧ Apery.kIn i ≤ 8 * (⌊x⌋₊ : ℤ) + 20 :=
  Apery.inner_table_k_93_124
