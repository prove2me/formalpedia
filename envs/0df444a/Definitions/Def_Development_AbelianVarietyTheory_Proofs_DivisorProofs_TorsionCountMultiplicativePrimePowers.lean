-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountMultiplicativePrimePowers
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountMultiplicativePrimePowers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:23.094887+00:00
-- url     : https://prove2.me/theorems/fd43baea-42bd-422d-a969-f79c08f04456
-- title:
--   Torsion Count Multiplicative Prime Powers
-- statement:
--   Definitions and structural lemmas for Torsion Count Multiplicative Prime Powers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionCountMultiplicativePrimePowers.lean

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
namespace GlobalTheory.PrimaryTorsionBlocks
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
def killedBy (I : Ideal R) : AddSubgroup M where
  carrier := {x | ∀ a ∈ I, a • x = 0}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := fun {x y} hx hy a ha => by
    show a • (x + y) = 0
    rw [smul_add, hx a ha, hy a ha, add_zero]
  neg_mem' := fun {x} hx a ha => by
    show a • (-x) = 0
    rw [smul_neg, hx a ha, neg_zero]
def annOf (x : M) : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M x)
end GlobalTheory.PrimaryTorsionBlocks
namespace GlobalTheory
end GlobalTheory


