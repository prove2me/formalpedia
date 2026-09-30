-- Prove2me | solution 1 for AlgMechDesign.MinWork.makespan_le_sum_minTime
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:30:02.415843+00:00
-- url     : https://prove2.me/submissions/02b65463-4429-4d86-af18-39173f202951

import Definitions.Def_AlgMechDesign_MinWork_Model
import Definitions.Def_AlgMechDesign_MinWork_Mechanism

set_option autoImplicit false
open AlgMechDesign.MinWork

theorem solution {n k : ℕ} [NeZero n]
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
