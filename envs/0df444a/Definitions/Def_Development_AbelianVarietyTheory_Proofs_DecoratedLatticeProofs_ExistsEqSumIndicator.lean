-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqSumIndicator
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqSumIndicator
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T10:27:32.939962+00:00
-- url     : https://prove2.me/theorems/d47d1224-b0be-4759-9da3-2e06a882d9ea
-- title:
--   Exists Eq Sum Indicator
-- statement:
--   Definitions and structural lemmas for Exists Eq Sum Indicator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsEqSumIndicator.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.DoubleCosetIndicator
def dc {G : Type} [Group G] (R K : Subgroup G) (t : G) : Set G :=
  {x : G | ∃ r ∈ R, ∃ κ ∈ K, x = r * t * κ}
end GlobalTheory.DoubleCosetIndicator


