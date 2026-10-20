-- Prove2me | solution 1 for AngelDevil.angelWins_iff_two_le
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-19T13:22:43.114272+00:00
-- url     : https://prove2.me/submissions/4a294f28-9ba8-4c8a-99ca-e34ba71f08b3

import Definitions.Def_AngelDevil_KingGuard
import Definitions.Def_AngelDevil_FiniteGame
import Mathlib.Tactic.FinCases
import Theorems.Thm_AngelDevil_power_one_devil_wins
import Theorems.Thm_AngelDevil_angelWins_mono
import Theorems.Thm_AngelDevil_power_ge_two_wins

set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

namespace AngelDevil

theorem power_one_not_wins : ¬ AngelWins 1 := by
  obtain ⟨D,hD⟩ := power_one_devil_wins
  rintro ⟨A,hA⟩
  exact hD A (hA D)

end AngelDevil

theorem solution (p : Nat) : AngelDevil.AngelWins p ↔ 2 ≤ p := by
  constructor
  · intro h
    by_contra hp
    exact AngelDevil.power_one_not_wins (AngelDevil.angelWins_mono (by omega) h)
  · exact AngelDevil.power_ge_two_wins p
