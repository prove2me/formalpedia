-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameClassTermsLeOverlatticeMassesStatement
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameClassTermsLeOverlatticeMassesStatement
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T07:27:46.715996+00:00
-- url     : https://prove2.me/theorems/11e9bc74-f168-49d3-940c-3d1fe3550281
-- title:
--   Hermitian Frame Class Terms Le Overlattice Masses Statement
-- statement:
--   Definitions and structural lemmas for Hermitian Frame Class Terms Le Overlattice Masses Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFrameClassTermsLeOverlatticeMassesStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameClassTermsLeOverlatticeMasses
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
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


