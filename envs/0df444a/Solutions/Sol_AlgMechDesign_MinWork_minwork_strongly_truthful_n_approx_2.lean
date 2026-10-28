-- Prove2me | solution 2 for AlgMechDesign.MinWork.minwork_strongly_truthful_n_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:50:37.5329+00:00
-- url     : https://prove2.me/submissions/b0654a8e-b09d-4ce0-a41a-3ce6ac65841f

import Mathlib
import Definitions.Def_AlgMechDesign_MinWork_Model
import Definitions.Def_AlgMechDesign_MinWork_Mechanism
import Theorems.Thm_AlgMechDesign_MinWork_sum_minTime_le_n_makespan
import Theorems.Thm_AlgMechDesign_MinWork_minwork_strongly_truthful
import Theorems.Thm_AlgMechDesign_MinWork_makespan_le_sum_minTime

-- carved verbatim out of submission 84f7b313-2a56-4825-8fe1-7a541357a6f2, lines 181-185

section
set_option autoImplicit false
open AlgMechDesign.MinWork Finset

private theorem n_approx {n k : ℕ} [NeZero n]
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hmin : IsMinWorkAlloc alloc) :
    IsApprox (n : ℝ) alloc := by
  intro t ht y
  have hu := AlgMechDesign.MinWork.makespan_le_sum_minTime alloc hmin t ht
  have hl := AlgMechDesign.MinWork.sum_minTime_le_n_makespan t ht y
  have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [one_div_mul_eq_div] at hl
  have hl' := (div_le_iff₀ hn).mp hl
  nlinarith

theorem solution {n k : ℕ} [NeZero n] (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hmin : IsMinWorkAlloc alloc) :
    IsStronglyTruthful alloc (minWorkPay hn alloc) ∧ IsApprox (n : ℝ) alloc := by
  exact ⟨AlgMechDesign.MinWork.minwork_strongly_truthful hn alloc hmin, n_approx alloc hmin⟩

end
