-- Prove2me | solution 1 for AlgMechDesign.CompBonus.bonus_max_minimal_exec
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:03:38.297541+00:00
-- url     : https://prove2.me/submissions/5c0149b8-a847-4ec8-82c3-c074c2f77566

import Definitions.Def_AlgMechDesign_CompBonus_Model
import Definitions.Def_AlgMechDesign_CompBonus_Mechanism

set_option autoImplicit false
open AlgMechDesign.CompBonus

theorem solution {n k : ℕ} [NeZero n] (x : Fin k → Fin n)
    (t : Fin n → Fin k → ℝ) (i : Fin n) (tt : Fin k → ℝ)
    (htt : ∀ j, x j = i → t i j ≤ tt j) :
    -gT x (corr i x t tt) ≤ -gT x (corrStar x t) := by
  apply neg_le_neg
  unfold gT
  apply Finset.sup'_mono_fun
  intro l hl
  apply Finset.sum_le_sum
  intro j hj
  dsimp [corr, corrStar]
  by_cases he : x j = i
  · simpa [he] using htt j he
  · simp [he]
