-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsLeftCoactionIffIsCoactionComm
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsLeftCoactionIffIsCoactionComm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:37.4398+00:00
-- url     : https://prove2.me/theorems/06e37293-98ff-4e4e-9bec-8c5b82bdcdda
-- title:
--   Is Left Coaction Iff Is Coaction Comm
-- statement:
--   Definitions and structural lemmas for Is Left Coaction Iff Is Coaction Comm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsLeftCoactionIffIsCoactionComm.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra
namespace GlobalTheory
variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type*} [AddCommMonoid M] [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M']
structure IsCoaction (ρ : M →ₗ[R] M ⊗[R] C) : Prop where

  coassoc : ∀ m, TensorProduct.assoc R M C C (ρ.rTensor C (ρ m)) =
    (comul : C →ₗ[R] C ⊗[R] C).lTensor M (ρ m)

  counit : ∀ m, (counit : C →ₗ[R] R).lTensor M (ρ m) = m ⊗ₜ[R] (1 : R)
structure IsLeftCoaction (ρ : M →ₗ[R] C ⊗[R] M) : Prop where

  coassoc : ∀ m, TensorProduct.assoc R C C M ((comul : C →ₗ[R] C ⊗[R] C).rTensor M (ρ m)) =
    ρ.lTensor C (ρ m)

  counit : ∀ m, (counit : C →ₗ[R] R).rTensor M (ρ m) = (1 : R) ⊗ₜ[R] m
def coactionWeightSpace (ρ : M →ₗ[R] M ⊗[R] C) (g : C) : Submodule R M :=
  LinearMap.eqLocus ρ ((TensorProduct.mk R M C).flip g)
end GlobalTheory


