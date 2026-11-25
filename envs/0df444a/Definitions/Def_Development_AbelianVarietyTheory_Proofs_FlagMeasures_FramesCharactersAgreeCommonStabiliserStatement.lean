-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliserStatement
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:13:58.900418+00:00
-- url     : https://prove2.me/theorems/77d91358-2e50-438d-b137-8edde89cedf4
-- title:
--   Frames Characters Agree Common Stabiliser Statement
-- statement:
--   Definitions and structural lemmas for Frames Characters Agree Common Stabiliser Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramesCharactersAgreeCommonStabiliserStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliser
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
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


