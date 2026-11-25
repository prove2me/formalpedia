-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EmbeddedDatumInvariantUnderUnipotentStatement
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_EmbeddedDatumInvariantUnderUnipotentStatement
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:55:47.042884+00:00
-- url     : https://prove2.me/theorems/70727ff9-9cb8-5c6c-8b71-a2729717d2ca
-- title:
--   Embedded Datum Invariant Under Unipotent Statement
-- statement:
--   Definitions and structural lemmas for Embedded Datum Invariant Under Unipotent Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EmbeddedDatumInvariantUnderUnipotentStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EmbeddedDatumInvariantUnderUnipotent
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


