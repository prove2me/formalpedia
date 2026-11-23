-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:18.128446+00:00
-- url     : https://prove2.me/theorems/056399c7-6c30-4e0b-8536-dcf4ed5f967b
-- title:
--   Fin Part Eq One Of Level
-- statement:
--   Definitions and structural lemmas for Fin Part Eq One Of Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfLevel.lean

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
namespace GlobalTheory.CMVal.OrderUnits
variable {E : Type} [Field E] [NumberField E]
end GlobalTheory.CMVal.OrderUnits


