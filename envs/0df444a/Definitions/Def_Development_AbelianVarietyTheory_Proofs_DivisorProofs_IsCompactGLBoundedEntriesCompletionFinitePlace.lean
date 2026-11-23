-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactGLBoundedEntriesCompletionFinitePlace
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCompactGLBoundedEntriesCompletionFinitePlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:23.074516+00:00
-- url     : https://prove2.me/theorems/86aafb92-9c29-4058-86eb-a7431edec933
-- title:
--   Is Compact GLBounded Entries Completion Finite Place
-- statement:
--   Definitions and structural lemmas for Is Compact GLBounded Entries Completion Finite Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCompactGLBoundedEntriesCompletionFinitePlace.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
noncomputable section
namespace GlobalTheory.BoundedGL
variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
end GlobalTheory.BoundedGL


