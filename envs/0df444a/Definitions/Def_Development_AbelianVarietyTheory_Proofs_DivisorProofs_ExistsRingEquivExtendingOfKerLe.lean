-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingEquivExtendingOfKerLe
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingEquivExtendingOfKerLe
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:00:40.292797+00:00
-- url     : https://prove2.me/theorems/6fc607d6-a59a-4f8d-b1b5-508019d6818b
-- title:
--   Exists Ring Equiv Extending Of Ker Le
-- statement:
--   Definitions and structural lemmas for Exists Ring Equiv Extending Of Ker Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingEquivExtendingOfKerLe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
def FieldCopy (k : Type) : Type := k
instance FieldCopy.instField (k : Type) [h : Field k] : Field (FieldCopy k) := h
instance FieldCopy.instIsAlgClosed (k : Type) [Field k] [h : IsAlgClosed k] :
    IsAlgClosed (FieldCopy k) := h
end GlobalTheory


