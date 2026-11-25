-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateInvariantsCyclotomicTwist
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateInvariantsCyclotomicTwist
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T15:19:19.147879+00:00
-- url     : https://prove2.me/theorems/4ccecdc5-8357-477e-82a3-55d9d75ebdf6
-- title:
--   Tate Invariants Cyclotomic Twist
-- statement:
--   Definitions and structural lemmas for Tate Invariants Cyclotomic Twist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TateInvariantsCyclotomicTwist.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValIntStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerGeneratorMatrixPerturbationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
namespace GlobalTheory.CyclotomicTowerSubgroupInclusions
variable {l : ℕ} [Fact l.Prime]
end GlobalTheory.CyclotomicTowerSubgroupInclusions


