-- Prove2me | solution 1 for AlgMechDesign.Rounding.ghat_is_makespan
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:18:32.204524+00:00
-- url     : https://prove2.me/submissions/e556ccea-82a3-4318-8e31-3754c55e7c01

import Definitions.Def_AlgMechDesign_Rounding_Model
import Definitions.Def_AlgMechDesign_Rounding_Mechanism

set_option autoImplicit false
open AlgMechDesign.Rounding

theorem solution {n k : ℕ} [NeZero n] (δ : ℝ)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) :
    (∀ (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ),
      gT x (roundVec δ (corrStar x d)) = makespan (roundType δ d) x) ∧
    (∀ (d : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k) (i : Fin n),
      utility alloc (roundingPay δ alloc) d E i =
        -gT (alloc d) (roundVec δ (corr i (alloc d) d (actualTimes alloc d E)))) := by
  constructor
  · intro x d
    unfold gT makespan load corrStar roundVec roundType
    congr 1
    funext l
    apply Finset.sum_congr rfl
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    simpa only [h]
  · intro d E i
    simp [utility, roundingPay, compensation, roundedBonus]

