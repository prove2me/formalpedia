-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AmpSqLeOfHermitianTermTypesCauchySchwarz
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_AmpSqLeOfHermitianTermTypesCauchySchwarz
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:37:59.050963+00:00
-- url     : https://prove2.me/theorems/84ad647c-1cac-5f6d-809d-fefbc63adce3
-- title:
--   Amp Sq Le Of Hermitian Term Types Cauchy Schwarz
-- statement:
--   Definitions and structural lemmas for Amp Sq Le Of Hermitian Term Types Cauchy Schwarz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AmpSqLeOfHermitianTermTypesCauchySchwarz.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexEqCardMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AmpSqLeCardMulSum
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
namespace GlobalTheory.HL.TypesCS
end GlobalTheory.HL.TypesCS


