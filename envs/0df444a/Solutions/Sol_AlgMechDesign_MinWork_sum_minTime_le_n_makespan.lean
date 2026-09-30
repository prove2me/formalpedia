-- Prove2me | solution 1 for AlgMechDesign.MinWork.sum_minTime_le_n_makespan
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:28:31.353486+00:00
-- url     : https://prove2.me/submissions/6463f4c0-001b-4f79-9940-2163666a26bf

import Definitions.Def_AlgMechDesign_MinWork_Model
import Definitions.Def_AlgMechDesign_MinWork_Mechanism

set_option autoImplicit false
open AlgMechDesign.MinWork

theorem solution {n k : ℕ} [NeZero n]
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
