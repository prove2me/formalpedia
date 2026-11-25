-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolEqInfMulSupAndMono
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolEqInfMulSupAndMono
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:10:28.712986+00:00
-- url     : https://prove2.me/theorems/b95cfc40-c970-5b08-a572-8156a7bea235
-- title:
--   Inv Vol Eq Inf Mul Sup And Mono
-- statement:
--   Definitions and structural lemmas for Inv Vol Eq Inf Mul Sup And Mono, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/InvVolEqInfMulSupAndMono.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
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
namespace GlobalTheory.IndexProd
end GlobalTheory.IndexProd


