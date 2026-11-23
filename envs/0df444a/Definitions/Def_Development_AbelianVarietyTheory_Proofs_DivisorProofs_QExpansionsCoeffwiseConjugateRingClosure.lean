-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionsCoeffwiseConjugateRingClosure
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionsCoeffwiseConjugateRingClosure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:24.651803+00:00
-- url     : https://prove2.me/theorems/bf59fb54-5948-4fde-ba7a-983b370c7a2d
-- title:
--   QExpansions Coeffwise Conjugate Ring Closure
-- statement:
--   Definitions and structural lemmas for QExpansions Coeffwise Conjugate Ring Closure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionsCoeffwiseConjugateRingClosure.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
namespace GlobalTheory.QFam
variable {g : ℂ ≃+* ℂ} {N : ℕ}
end GlobalTheory.QFam


