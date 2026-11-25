-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveHermitianSublatticeDiscriminantGenerato
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveHermitianSublatticeDiscriminantGenerato
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:10:08.196258+00:00
-- url     : https://prove2.me/theorems/67bb8fd6-c386-48c8-baa7-1baa374738ff
-- title:
--   Primitive Hermitian Sublattice Discriminant Generato
-- statement:
--   Definitions and structural lemmas for Primitive Hermitian Sublattice Discriminant Generato, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveHermitianSublatticeDiscriminantGenerato.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCountStatement
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
namespace GlobalTheory.Mass.PrimDisc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end GlobalTheory.Mass.PrimDisc


