-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivationFamilyCotangentBasis
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivationFamilyCotangentBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:37.343366+00:00
-- url     : https://prove2.me/theorems/ccb8c64b-3f3f-4c3e-ad66-8bb2a948c60b
-- title:
--   Derivation Family Cotangent Basis
-- statement:
--   Definitions and structural lemmas for Derivation Family Cotangent Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivationFamilyCotangentBasis.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
namespace GlobalTheory.CoordsAlg
noncomputable def cotFun {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A)
    (f : I →ₗ[R] R) (hf : ∀ x : I, (x : A) ∈ I ^ 2 → f x = 0) : Module.Dual R I.Cotangent :=
  ((I • ⊤ : Submodule A I).restrictScalars R).liftQ f (fun x hx => by
      refine LinearMap.mem_ker.mpr (hf x ?_)
      rw [← Ideal.toCotangent_eq_zero]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hx) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R (I • ⊤ : Submodule A I)).symm.toLinearMap
end GlobalTheory.CoordsAlg


