-- Prove2me | solution 1 for AlgMechDesign.MinWork.minwork_n_approx
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:30:03.191405+00:00
-- url     : https://prove2.me/submissions/81ef07f0-7027-44f4-8b5e-8fd3e339d67c

import Definitions.Def_AlgMechDesign_MinWork_Model
import Definitions.Def_AlgMechDesign_MinWork_Mechanism

set_option autoImplicit false
open AlgMechDesign.MinWork

private theorem upper_bound {n k : ℕ} [NeZero n]
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hmin : IsMinWorkAlloc alloc)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) :
    makespan t (alloc t) ≤ ∑ j, minTime t j := by
  have heq : ∀ j, t (alloc t j) j = minTime t j := by
    intro j
    apply le_antisymm
    · exact Finset.le_inf' Finset.univ_nonempty (fun i => t i j) (fun i hi => hmin t j i)
    · exact Finset.inf'_le _ (Finset.mem_univ _)
  have hn : ∀ j, 0 ≤ minTime t j := by
    intro j
    rw [← heq j]
    exact le_of_lt (ht _ _)
  unfold makespan
  apply Finset.sup'_le
  intro i hi
  unfold load
  calc
    ∑ j ∈ Finset.univ.filter (fun j => alloc t j = i), t i j =
        ∑ j ∈ Finset.univ.filter (fun j => alloc t j = i), minTime t j := by
      apply Finset.sum_congr rfl
      intro j hj
      have h := (Finset.mem_filter.mp hj).2
      simpa [h] using heq j
    _ ≤ ∑ j, minTime t j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro j hj hj'
        exact hn j

private theorem lower_bound {n k : ℕ} [NeZero n]
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (y : Fin k → Fin n) :
    1 / (n : ℝ) * ∑ j, minTime t j ≤ makespan t y := by
  have hsum : ∑ j, minTime t j ≤ ∑ i, load t y i := by
    have hpartition : ∑ i, load t y i = ∑ j, t (y j) j := by
      simp only [load, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      simp
    rw [hpartition]
    apply Finset.sum_le_sum
    intro j hj
    exact Finset.inf'_le _ (Finset.mem_univ (y j))
  have hbound : ∑ i, load t y i ≤ (n : ℝ) * makespan t y := by
    calc
      ∑ i, load t y i ≤ ∑ _i : Fin n, makespan t y := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.le_sup' (load t y) hi
      _ = (n : ℝ) * makespan t y := by simp
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ hn).mpr
  nlinarith [hsum.trans hbound]

theorem solution {n k : ℕ} [NeZero n]
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hmin : IsMinWorkAlloc alloc) :
    IsApprox (n : ℝ) alloc := by
  intro t ht y
  have hu := upper_bound alloc hmin t ht
  have hl := lower_bound t ht y
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [one_div_mul_eq_div] at hl
  have hl' := (div_le_iff₀ hn).mp hl
  nlinarith
