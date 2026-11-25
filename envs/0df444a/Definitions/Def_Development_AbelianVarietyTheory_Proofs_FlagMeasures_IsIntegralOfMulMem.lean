-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfMulMem
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfMulMem
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:12:18.819189+00:00
-- url     : https://prove2.me/theorems/d00bb2e2-5111-4990-9a87-d8362af62388
-- title:
--   Is Integral Of Mul Mem
-- statement:
--   Definitions and structural lemmas for Is Integral Of Mul Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsIntegralOfMulMem.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
namespace GlobalTheory.DegCnt.NormOneCount
variable {K : Type} [Field K] [NumberField K]
end GlobalTheory.DegCnt.NormOneCount


