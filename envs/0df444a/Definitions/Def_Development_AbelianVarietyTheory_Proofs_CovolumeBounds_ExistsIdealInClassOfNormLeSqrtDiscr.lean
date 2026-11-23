-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:23.971274+00:00
-- url     : https://prove2.me/theorems/8cc182b3-77ab-4503-9b9e-3fb1e93a8e1a
-- title:
--   Exists Ideal In Class Of Norm Le Sqrt Discr
-- statement:
--   Definitions and structural lemmas for Exists Ideal In Class Of Norm Le Sqrt Discr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Real NumberField ArithmeticFunction.zeta
open Module NumberField Finset
namespace GlobalTheory
variable (K : Type*) [Field K] [NumberField K]
end GlobalTheory


