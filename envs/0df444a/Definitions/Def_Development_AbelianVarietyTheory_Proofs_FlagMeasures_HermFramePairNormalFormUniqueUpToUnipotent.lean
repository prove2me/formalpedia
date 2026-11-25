-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormUniqueUpToUnipotent
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormUniqueUpToUnipotent
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:12.64551+00:00
-- url     : https://prove2.me/theorems/d9246cdd-f6ca-4a4c-ba97-ef80547d12a2
-- title:
--   Herm Frame Pair Normal Form Unique Up To Unipotent
-- statement:
--   Definitions and structural lemmas for Herm Frame Pair Normal Form Unique Up To Unipotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormUniqueUpToUnipotent.lean

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
namespace GlobalTheory.DegAsm.NFUnique
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
def Cmp (H : HermSpace K V) (p q : V × V) : Prop := H.B p.1 q.1 = H.B p.2 q.2
variable [NumberField K]
variable [FiniteDimensional K V]
end GlobalTheory.DegAsm.NFUnique
namespace GlobalTheory.DegAsm
end GlobalTheory.DegAsm


