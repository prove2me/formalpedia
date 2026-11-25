-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLatticesStatement
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLatticesStatement
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:25.362774+00:00
-- url     : https://prove2.me/theorems/b251fa49-859b-4cdf-8984-6bd08c58289c
-- title:
--   Frame Pair Coordinates Transport Inner Lattices Statement
-- statement:
--   Definitions and structural lemmas for Frame Pair Coordinates Transport Inner Lattices Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramePairCoordinatesTransportInnerLatticesStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLattices
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
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


