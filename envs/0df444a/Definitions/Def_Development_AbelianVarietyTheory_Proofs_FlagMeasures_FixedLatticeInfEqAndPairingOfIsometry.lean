-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FixedLatticeInfEqAndPairingOfIsometry
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_FixedLatticeInfEqAndPairingOfIsometry
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T04:34:22.526699+00:00
-- url     : https://prove2.me/theorems/25cf92b4-3b16-4a59-a468-744cc53eef74
-- title:
--   Fixed Lattice Inf Eq And Pairing Of Isometry
-- statement:
--   Definitions and structural lemmas for Fixed Lattice Inf Eq And Pairing Of Isometry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FixedLatticeInfEqAndPairingOfIsometry.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
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
namespace GlobalTheory.DegCnt
end GlobalTheory.DegCnt


