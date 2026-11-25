-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsExtensionAdditiveFnPDivGroup
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsExtensionAdditiveFnPDivGroup
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:58:24.799012+00:00
-- url     : https://prove2.me/theorems/40905f5c-1a19-4b63-8e35-d40378d2a98e
-- title:
--   Exists Extension Additive Fn PDiv Group
-- statement:
--   Definitions and structural lemmas for Exists Extension Additive Fn PDiv Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsExtensionAdditiveFnPDivGroup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulPEqOfTranslInvariantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TranslCoactionFreeCoassocCounitalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoactionEqAddOfPrimitiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
namespace GlobalTheory
namespace PDivGroup
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)
end PDivGroup
end GlobalTheory


