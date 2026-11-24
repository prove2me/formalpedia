-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsShortBasisAdaptedOfSubsetSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:47.77152+00:00
-- url     : https://prove2.me/theorems/0fac1121-2cbc-455d-b5ee-d40bf244ce67
-- title:
--   Exists Short Basis Adapted Of Subset Span
-- statement:
--   Definitions and structural lemmas for Exists Short Basis Adapted Of Subset Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsShortBasisAdaptedOfSubsetSpan.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
namespace GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
end GlobalTheory


