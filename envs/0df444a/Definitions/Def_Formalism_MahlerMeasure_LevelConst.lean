-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_LevelConst
-- name    : Formalism_MahlerMeasure_LevelConst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:09:11.20527+00:00
-- url     : https://prove2.me/theorems/6a29501f-b135-4893-8280-f9dc9b0faac1
-- title:
--   Level Const
-- statement:
--   Definitions and structural lemmas for Level Const, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/LevelConst.lean

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM
def LevelConst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (a r o n z j : ℕ), 1 ≤ a → 1 ≤ r → o + n + z + 1 ≤ 8 * a →
    j ≤ o → j ≤ n →
    |((padicValRat p
        (((j.factorial ^ 2 * (o + n + r + z + 1 - 2 * j + j - 1).choose j * z.factorial *
            (o - j).factorial * (n - j).factorial : ℕ) : ℚ) /
          (((z + o).factorial * n.factorial : ℕ) : ℚ)) : ℤ) : ℝ)| ≤ 3 * lgV2 p a r
end Formalism.GM


