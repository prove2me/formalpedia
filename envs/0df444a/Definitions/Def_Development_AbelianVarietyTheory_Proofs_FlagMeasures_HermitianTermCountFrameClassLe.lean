-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianTermCountFrameClassLe
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianTermCountFrameClassLe
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T07:08:30.097892+00:00
-- url     : https://prove2.me/theorems/130a7446-cef4-52a3-9fed-0be2f4e745db
-- title:
--   Hermitian Term Count Frame Class Le
-- statement:
--   Definitions and structural lemmas for Hermitian Term Count Frame Class Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianTermCountFrameClassLe.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFramesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_GluingCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardGluingHomKernelsLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.TermCount
end GlobalTheory.HL.TermCount


