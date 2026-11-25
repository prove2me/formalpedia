-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsShortVectorIntegralHermitianLatticeRankOne
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsShortVectorIntegralHermitianLatticeRankOne
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:53:47.230808+00:00
-- url     : https://prove2.me/theorems/a7c0307a-b9b3-4ac4-bd52-a9ba7773f5a0
-- title:
--   Exists Short Vector Integral Hermitian Lattice Rank One
-- statement:
--   Definitions and structural lemmas for Exists Short Vector Integral Hermitian Lattice Rank One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsShortVectorIntegralHermitianLatticeRankOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RegulatorLeSumSmallIdealsInClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.Mass.ShortVector
open GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end GlobalTheory.Mass.ShortVector


