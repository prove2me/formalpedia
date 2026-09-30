-- Prove2me | solution 1 for AlgMechDesign.CompBonus.optimality_corrStar
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:03:38.92098+00:00
-- url     : https://prove2.me/submissions/ecece09d-5d24-450f-854a-e14c7f7aa99f

import Definitions.Def_AlgMechDesign_CompBonus_Model
import Definitions.Def_AlgMechDesign_CompBonus_Mechanism

set_option autoImplicit false
open AlgMechDesign.CompBonus

private theorem gT_corrStar_eq {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ)
    (x : Fin k → Fin n) : gT x (corrStar x t) = makespan t x := by
  unfold gT makespan load corrStar
  congr 1
  funext l
  apply Finset.sum_congr rfl
  intro j hj
  have h := (Finset.mem_filter.mp hj).2
  rw [h]

theorem solution {n k : ℕ} [NeZero n]
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hopt : IsOptimalAlloc alloc)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n) (ti' : Fin k → ℝ)
    (hti' : IsAgentType ti') :
    -gT (alloc (Function.update t i ti')) (corrStar (alloc (Function.update t i ti')) t) ≤
      -gT (alloc t) (corrStar (alloc t) t) := by
  simpa only [gT_corrStar_eq] using neg_le_neg (hopt t ht (alloc (Function.update t i ti')))
