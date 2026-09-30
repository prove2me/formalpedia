-- Prove2me | solution 1 for AlgMechDesign.CompBonus.cb_utility_eq_bonus
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:03:37.685003+00:00
-- url     : https://prove2.me/submissions/3b5096c6-513d-4c70-97ac-c3f97f138b8a

import Definitions.Def_AlgMechDesign_CompBonus_Model
import Definitions.Def_AlgMechDesign_CompBonus_Mechanism

set_option autoImplicit false
open AlgMechDesign.CompBonus

theorem solution {n k : ℕ} [NeZero n]
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (d : Fin n → Fin k → ℝ)
    (E : Fin n → ExecPlan n k) (i : Fin n) :
    utility alloc (cbPay alloc) d E i = bonus alloc d (actualTimes alloc d E) i := by
  simp [utility, cbPay, compensation]
