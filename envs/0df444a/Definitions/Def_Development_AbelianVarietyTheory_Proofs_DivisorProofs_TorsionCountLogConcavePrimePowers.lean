-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountLogConcavePrimePowers
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountLogConcavePrimePowers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:43.204384+00:00
-- url     : https://prove2.me/theorems/35b6f444-9fa4-4bdf-aa8b-d47bda69d706
-- title:
--   Torsion Count Log Concave Prime Powers
-- statement:
--   Definitions and structural lemmas for Torsion Count Log Concave Prime Powers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionCountLogConcavePrimePowers.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace GlobalTheory
def killedBy {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (I : Ideal R) :
    AddSubgroup M where
  carrier := {x | ∀ a ∈ I, a • x = 0}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := fun hx hy a ha => by rw [smul_add, hx a ha, hy a ha, add_zero]
  neg_mem' := fun hx a ha => by rw [smul_neg, hx a ha, neg_zero]
end GlobalTheory


