-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrder
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrder
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:12.831333+00:00
-- url     : https://prove2.me/theorems/41c12251-9c6d-40c3-9697-66657aad053d
-- title:
--   Idelic Ring Class Lattice One Eq Order
-- statement:
--   Definitions and structural lemmas for Idelic Ring Class Lattice One Eq Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdelicRingClassLatticeOneEqOrder.lean

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
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
namespace GlobalTheory.CMVal.HatCap
variable {E : Type} [Field E] [NumberField E]
end GlobalTheory.CMVal.HatCap


