-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameClassesTotalWeightLe
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameClassesTotalWeightLe
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T07:04:42.005811+00:00
-- url     : https://prove2.me/theorems/8bc4e51e-1e6d-5ed1-a6df-b80f82100d41
-- title:
--   Hermitian Frame Classes Total Weight Le
-- statement:
--   Definitions and structural lemmas for Hermitian Frame Classes Total Weight Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFrameClassesTotalWeightLe.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RmulMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumClsLeEncard
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
namespace GlobalTheory.HL.TotalWeight
end GlobalTheory.HL.TotalWeight


