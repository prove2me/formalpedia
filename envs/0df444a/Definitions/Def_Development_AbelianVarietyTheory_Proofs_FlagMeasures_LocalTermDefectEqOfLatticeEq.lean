-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalTermDefectEqOfLatticeEq
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalTermDefectEqOfLatticeEq
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T07:02:08.475711+00:00
-- url     : https://prove2.me/theorems/635dc170-cf6f-4ce5-bbaf-a6a4f6abf51b
-- title:
--   Local Term Defect Eq Of Lattice Eq
-- statement:
--   Definitions and structural lemmas for Local Term Defect Eq Of Lattice Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LocalTermDefectEqOfLatticeEq.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermsCorrespond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDatumEqOfSameLatticeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.LocDefect
end GlobalTheory.HL.LocDefect


