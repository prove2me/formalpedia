-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedAlongLine
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedAlongLine
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T04:48:08.745158+00:00
-- url     : https://prove2.me/theorems/0d319be2-61d0-5e6a-b266-d664f681bd28
-- title:
--   Card Hermitian Lattices Glued Along Line
-- statement:
--   Definitions and structural lemmas for Card Hermitian Lattices Glued Along Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianLatticesGluedAlongLine.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
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
namespace GlobalTheory.Mass.LineGlue
section Line
variable {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
end Line
end GlobalTheory.Mass.LineGlue


