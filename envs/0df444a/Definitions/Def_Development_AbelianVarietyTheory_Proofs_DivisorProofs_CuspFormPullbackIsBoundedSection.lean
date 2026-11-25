-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CuspFormPullbackIsBoundedSection
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CuspFormPullbackIsBoundedSection
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:31:30.478487+00:00
-- url     : https://prove2.me/theorems/55e9d5c5-4bc7-4fc0-9384-9e0b4b2d33fb
-- title:
--   Cusp Form Pullback Is Bounded Section
-- statement:
--   Definitions and structural lemmas for Cusp Form Pullback Is Bounded Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspFormPullbackIsBoundedSection.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_TwoLevelLogarithm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix
namespace GlobalTheory.PullBdd
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end
end GlobalTheory.PullBdd


