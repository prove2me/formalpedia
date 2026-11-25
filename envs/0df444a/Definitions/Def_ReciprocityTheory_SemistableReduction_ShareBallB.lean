-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB
-- name    : ReciprocityTheory_SemistableReduction_ShareBallB
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:38:26.685072+00:00
-- url     : https://prove2.me/theorems/33864087-e9cc-4da4-83b4-9dca3d6ef10d
-- title:
--   Share Ball B
-- statement:
--   Definitions and structural lemmas for Share Ball B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareBallB.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open Matrix
def sbDp (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun k => if (k : ℕ) < p then 1 else 0
def sbDn (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun k => if (k : ℕ) < p then 0 else 1
end ReciprocityTheory.MultiplicativeHeights


