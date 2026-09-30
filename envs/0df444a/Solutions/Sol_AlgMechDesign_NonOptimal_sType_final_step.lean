-- Prove2me | solution 1 for AlgMechDesign.NonOptimal.sType_final_step
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:54:54.740436+00:00
-- url     : https://prove2.me/submissions/7a8998f0-d458-4aeb-835a-27646862128e

import Definitions.Def_AlgMechDesign_NonOptimal_Model

set_option autoImplicit false
open AlgMechDesign.NonOptimal Finset

theorem solution {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (ht : IsType t)
    (o : Fin k → Fin n) (ho : IsOptimalFor t o) (M : ℝ) (hM : ∀ i j, t i j ≤ M) :
    makespan (sType t o M) o = makespan t o ∧ IsOptimalFor (sType t o M) o ∧
      ∀ y : Fin k → Fin n, y ≠ o → M ≤ makespan (sType t o M) y := by
  have hpoint : ∀ i j, t i j ≤ sType t o M i j := by
    intro i j
    unfold sType offOpt
    split_ifs
    · exact le_rfl
    · exact hM i j
  have heq : makespan (sType t o M) o = makespan t o := by
    unfold makespan
    congr 1
    funext i
    unfold load
    apply Finset.sum_congr rfl
    intro j hj
    simp [sType, offOpt, (Finset.mem_filter.mp hj).2]
  refine ⟨heq, ?_, ?_⟩
  · intro y
    rw [heq]
    apply (ho y).trans
    unfold makespan
    apply Finset.sup'_mono_fun
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact hpoint i j
  · intro y hyo
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hyo
    have hterm : sType t o M (y j) j = M := by simp [sType, offOpt, Ne.symm hj]
    have hload : M ≤ load (sType t o M) y (y j) := by
      calc
        M = sType t o M (y j) j := hterm.symm
        _ ≤ load (sType t o M) y (y j) := by
          unfold load
          apply Finset.single_le_sum
          · intro q hq
            exact (le_of_lt (ht (y j) q)).trans (hpoint (y j) q)
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    exact hload.trans (Finset.le_sup' (load (sType t o M) y) (Finset.mem_univ _))
