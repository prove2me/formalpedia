-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:51.675855+00:00
-- url     : https://prove2.me/theorems/1c145407-7d33-451f-b787-8e3ea2fe1ac8
-- title:
--   Mod FMul Pos Principal
-- statement:
--   Definitions and structural lemmas for Mod FMul Pos Principal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModFMulPosPrincipal.lean

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
namespace GlobalTheory.CMVal.IdeleModule
variable {E : Type} [Field E] [NumberField E]
end GlobalTheory.CMVal.IdeleModule


