-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_EqEvalOfDirDerivVanish
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_EqEvalOfDirDerivVanish
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:35.900081+00:00
-- url     : https://prove2.me/theorems/45c01e69-4d92-4b84-b6a3-a96799e4d968
-- title:
--   Eq Eval Of Dir Deriv Vanish
-- statement:
--   Definitions and structural lemmas for Eq Eval Of Dir Deriv Vanish, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/EqEvalOfDirDerivVanish.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
namespace GlobalTheory.PolyOfDeriv
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end GlobalTheory.PolyOfDeriv


