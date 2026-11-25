-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemOfForall
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemOfForall
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T04:09:05.40283+00:00
-- url     : https://prove2.me/theorems/61f51b9e-fc1a-4c4c-8bf6-bf8d33b19d8d
-- title:
--   Mem Of Forall
-- statement:
--   Definitions and structural lemmas for Mem Of Forall, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemOfForall.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open scoped nonZeroDivisors
namespace GlobalTheory.DegCnt.IdealPow
variable {K : Type} [Field K] [NumberField K] {𝔡 : Ideal (𝓞 K)}
variable [StarRing K]
end GlobalTheory.DegCnt.IdealPow


