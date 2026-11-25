-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FewOrbitsSubspacesHermitianLatticeDiscriminant
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_FewOrbitsSubspacesHermitianLatticeDiscriminant
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T07:13:03.754288+00:00
-- url     : https://prove2.me/theorems/a04a503f-3be9-54d3-9c79-d26004202401
-- title:
--   Few Orbits Subspaces Hermitian Lattice Discriminant
-- statement:
--   Definitions and structural lemmas for Few Orbits Subspaces Hermitian Lattice Discriminant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FewOrbitsSubspacesHermitianLatticeDiscriminant.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteHermitianIsometricOfSameBadPrimesStatement
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
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
noncomputable section
namespace GlobalTheory.Mass.FewOrbits
end GlobalTheory.Mass.FewOrbits


