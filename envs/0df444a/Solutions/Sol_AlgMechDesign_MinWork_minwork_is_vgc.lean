-- Prove2me | solution 1 for AlgMechDesign.MinWork.minwork_is_vgc
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:37:25.886832+00:00
-- url     : https://prove2.me/submissions/d6a3526a-2221-4ee6-8640-6be20cccb61c

import Definitions.Def_AlgMechDesign_MinWork_Model
import Definitions.Def_AlgMechDesign_MinWork_Mechanism

set_option autoImplicit false
open AlgMechDesign.MinWork Finset

private theorem sum_load {n k : ℕ} (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) :
    ∑ i, load t x i = ∑ j, t (x j) j := by
  simp only [load, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp

theorem solution {n k : ℕ} (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hmin : IsMinWorkAlloc alloc)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) :
    (∀ x : Fin k → Fin n, ∑ i, -(load t x i) ≤ ∑ i, -(load t (alloc t) i)) ∧
    (∀ i : Fin n,
      minWorkPay hn alloc t i =
        ∑ i' ∈ univ.erase i, -(load t (alloc t) i') + ∑ j, secondBest hn t i j) ∧
    (∀ (i : Fin n) (ti' : Fin k → ℝ),
      ∑ j, secondBest hn (Function.update t i ti') i j = ∑ j, secondBest hn t i j) := by
  constructor
  · intro x
    simp only [Finset.sum_neg_distrib, sum_load]
    apply neg_le_neg
    apply Finset.sum_le_sum
    intro j hj
    exact hmin t j (x j)
  constructor
  · intro i
    have hbest : ∀ j, alloc t j ≠ i → secondBest hn t i j = t (alloc t j) j := by
      intro j hj
      apply le_antisymm
      · exact Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)
      · exact Finset.le_inf' (erase_nonempty hn i) (fun l => t l j) (fun l hl => hmin t j l)
    have hexcept : ∑ i' ∈ univ.erase i, -(load t (alloc t) i') =
        ∑ j, if alloc t j = i then 0 else -(t (alloc t j) j) := by
      simp_rw [load, Finset.sum_filter, ← Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases he : alloc t j = i
      · simp [he]
      · simp [he]
    rw [hexcept, ← Finset.sum_add_distrib]
    unfold minWorkPay
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases he : alloc t j = i
    · simp [he]
    · simp [he, hbest j he]
  · intro i ti'
    apply Finset.sum_congr rfl
    intro j hj
    unfold secondBest
    apply Finset.inf'_congr (erase_nonempty hn i) rfl
    intro l hl
    have he := (Finset.mem_erase.mp hl).1
    simp [he]
