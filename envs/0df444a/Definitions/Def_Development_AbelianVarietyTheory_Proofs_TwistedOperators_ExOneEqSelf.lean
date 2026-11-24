-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExOneEqSelf
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExOneEqSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:08.025815+00:00
-- url     : https://prove2.me/theorems/e633c5a3-7ff0-404f-a06a-c8deaeef11d3
-- title:
--   Ex One Eq Self
-- statement:
--   Definitions and structural lemmas for Ex One Eq Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExOneEqSelf.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.LocAsm
def exOne {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) : ∀ b, X b → ℂ := fun b x =>
  match b, x with
  | .ex _ _, _ => 1
  | .theta i j, x => φ (.theta i j) x
end GlobalTheory.LocAsm


