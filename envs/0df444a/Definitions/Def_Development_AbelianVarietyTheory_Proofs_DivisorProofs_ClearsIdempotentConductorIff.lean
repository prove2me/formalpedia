-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentConductorIff
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClearsIdempotentConductorIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:53:10.246185+00:00
-- url     : https://prove2.me/theorems/c46849f9-65ea-4ffd-9080-a4831c7f2bbb
-- title:
--   Clears Idempotent Conductor Iff
-- statement:
--   Definitions and structural lemmas for Clears Idempotent Conductor Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClearsIdempotentConductorIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
namespace GlobalTheory.CondAway
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.CondAway


