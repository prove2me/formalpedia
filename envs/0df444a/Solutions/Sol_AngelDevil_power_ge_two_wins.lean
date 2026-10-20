-- Prove2me | solution 1 for AngelDevil.power_ge_two_wins
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-19T13:22:39.173134+00:00
-- url     : https://prove2.me/submissions/ce542f0a-304a-4da3-9123-50224a3fb2c0

import Definitions.Def_AngelDevil_KingGuard
import Definitions.Def_AngelDevil_FiniteGame
import Mathlib.Tactic.FinCases
import Theorems.Thm_AngelDevil_angelWins_mono
import Theorems.Thm_AngelDevil_power_two_wins

set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

namespace AngelDevil



end AngelDevil

theorem solution (p : Nat) (hp : 2 ≤ p) : AngelDevil.AngelWins p :=
  AngelDevil.angelWins_mono hp AngelDevil.power_two_wins
