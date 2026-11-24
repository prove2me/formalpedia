-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:41.198291+00:00
-- url     : https://prove2.me/theorems/67567ee9-f526-4dc4-a7ec-f8149bc27f76
-- title:
--   Is Clopen Is Compact Maps Pair
-- statement:
--   Definitions and structural lemmas for Is Clopen Is Compact Maps Pair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClopenIsCompactMapsPair.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
namespace GlobalTheory.LatPair
open SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable [Fintype n] [Fintype n']
end GlobalTheory.LatPair


