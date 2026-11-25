-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceLocalIndexColength
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceLocalIndexColength
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:03.653337+00:00
-- url     : https://prove2.me/theorems/7e036f4e-b0c7-4aac-b5b0-585dfd3c1348
-- title:
--   Function Field Place Local Index Colength
-- statement:
--   Definitions and structural lemmas for Function Field Place Local Index Colength, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceLocalIndexColength.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceIsDVRAndResidueEqGroundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
namespace GlobalTheory.Nef.LocalIndex
open GlobalTheory.Nef.OrdCalc
variable {k F : Type} [Field k] [Field F] [Algebra k F]
end GlobalTheory.Nef.LocalIndex


