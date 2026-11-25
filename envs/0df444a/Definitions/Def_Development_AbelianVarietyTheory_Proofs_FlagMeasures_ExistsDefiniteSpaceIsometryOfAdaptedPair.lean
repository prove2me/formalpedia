-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDefiniteSpaceIsometryOfAdaptedPair
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDefiniteSpaceIsometryOfAdaptedPair
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:26.545148+00:00
-- url     : https://prove2.me/theorems/9a40daaa-3899-4a3e-b4cc-11b307fb09ad
-- title:
--   Exists Definite Space Isometry Of Adapted Pair
-- statement:
--   Definitions and structural lemmas for Exists Definite Space Isometry Of Adapted Pair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsDefiniteSpaceIsometryOfAdaptedPair.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
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
open Formalism.HermitianLatticeCounting.P
namespace GlobalTheory.DegAsm.IndIsom
variable {K V W : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {H : HermSpace K V} {r : ℕ}
end GlobalTheory.DegAsm.IndIsom
namespace GlobalTheory.DegAsm
open IndIsom
end GlobalTheory.DegAsm


