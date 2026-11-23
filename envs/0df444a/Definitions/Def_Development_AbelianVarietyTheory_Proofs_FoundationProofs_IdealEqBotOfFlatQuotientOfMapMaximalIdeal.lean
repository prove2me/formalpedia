-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:31.111009+00:00
-- url     : https://prove2.me/theorems/f5b4e4b2-2e57-4614-8a35-9874ffbf9635
-- title:
--   Ideal Eq Bot Of Flat Quotient Of Map Maximal Ideal
-- statement:
--   Definitions and structural lemmas for Ideal Eq Bot Of Flat Quotient Of Map Maximal Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
namespace GlobalTheory
universe u v w
namespace LocalFlat
variable {A : Type u} [CommRing A]
def RelationsLift (I : Ideal A) (M : Type w) [AddCommGroup M] [Module A M] : Prop :=
  ∀ (F : Type u) [AddCommGroup F] [Module A F] (f : F →ₗ[A] A) (x : M ⊗[A] F),
    TensorProduct.rid A M (f.lTensor M x) ∈ I • (⊤ : Submodule A M) →
      x ∈ range ((Submodule.comap f I).subtype.lTensor M)
variable {M : Type w} [AddCommGroup M] [Module A M]
end LocalFlat
open IsLocalRing
section LocalCriterion
variable {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
variable {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Algebra T A] [Algebra T B] [IsLocalRing B] [IsLocalHom (algebraMap T B)] [Module.Flat T B]
end LocalCriterion
section Endomorphism
variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B] {φ : A →+* B} {I : Ideal A} {J : Ideal B}
theorem pow_le_comap_pow_of_le (hle : I ≤ J.comap φ) (n : ℕ) : I ^ n ≤ (J ^ n).comap φ :=
  (Ideal.pow_right_mono hle n).trans (Ideal.le_comap_pow φ n)
variable [IsNoetherianRing A] {φ : A →+* A}
end Endomorphism
section Descent
variable {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
end Descent
end GlobalTheory


