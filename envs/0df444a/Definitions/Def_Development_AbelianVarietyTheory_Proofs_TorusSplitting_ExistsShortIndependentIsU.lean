-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsShortIndependentIsU
-- name    : Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsShortIndependentIsU
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:44.640829+00:00
-- url     : https://prove2.me/theorems/0aa8a7a8-b457-4ac3-b285-8ddcb61e28a5
-- title:
--   Exists Short Independent Is U
-- statement:
--   Definitions and structural lemmas for Exists Short Independent Is U, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExistsShortIndependentIsU.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace
namespace GlobalTheory
noncomputable section
section lin
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}
end lin
end
end GlobalTheory


