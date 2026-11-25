-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameCoordinatesTransportInnerLattices
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameCoordinatesTransportInnerLattices
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:17.936903+00:00
-- url     : https://prove2.me/theorems/378da3f0-9cae-4a4c-bd55-3250d9c5e33b
-- title:
--   Hermitian Frame Coordinates Transport Inner Lattices
-- statement:
--   Definitions and structural lemmas for Hermitian Frame Coordinates Transport Inner Lattices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFrameCoordinatesTransportInnerLattices.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLattices
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
namespace GlobalTheory.HL.CoordInnerFst
open CoordInnerSnd
end GlobalTheory.HL.CoordInnerFst


