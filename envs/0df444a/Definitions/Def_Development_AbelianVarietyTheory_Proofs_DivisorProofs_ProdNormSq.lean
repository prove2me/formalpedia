-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:33.862801+00:00
-- url     : https://prove2.me/theorems/4c88f9d4-c857-4939-b869-62bb11a559b5
-- title:
--   Prod Norm Sq
-- statement:
--   Definitions and structural lemmas for Prod Norm Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdNormSq.lean

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
namespace GlobalTheory.CMVal.TermUnit
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
end GlobalTheory.CMVal.TermUnit


