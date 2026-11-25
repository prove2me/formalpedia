-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDefiniteSpaceIsometryOfAdaptedPairStatement
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDefiniteSpaceIsometryOfAdaptedPairStatement
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:02:26.19054+00:00
-- url     : https://prove2.me/theorems/911c2cd5-03f4-5456-bc58-2f8f10928735
-- title:
--   Exists Definite Space Isometry Of Adapted Pair Statement
-- statement:
--   Definitions and structural lemmas for Exists Definite Space Isometry Of Adapted Pair Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDefiniteSpaceIsometryOfAdaptedPairStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDefiniteSpaceIsometryOfAdaptedPair
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical


