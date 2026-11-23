-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:28:47.545526+00:00
-- url     : https://prove2.me/theorems/8ebfe14c-deb0-49a7-8cbd-155170dd2639
-- title:
--   Comm Of Bezout
-- statement:
--   Definitions and structural lemmas for Comm Of Bezout, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommOfBezout.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorOfSeparableCharpolyField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorGeneratedAlgebraStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory.UnitDiscAlg
section Basic
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
end Basic
end GlobalTheory.UnitDiscAlg


