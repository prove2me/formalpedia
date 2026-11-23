-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:21.608664+00:00
-- url     : https://prove2.me/theorems/76215150-6928-4f3e-9743-afac57fdf404
-- title:
--   Exists Basic Open Eq Zero Of Mem IInf Pow Smul
-- statement:
--   Definitions and structural lemmas for Exists Basic Open Eq Zero Of Mem IInf Pow Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
namespace GlobalTheory
section Krull
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable [IsNoetherianRing A] [Module.Finite A M]
end Krull
section Associated
variable {A : Type*} [CommRing A] [IsNoetherianRing A] {M : Type*} [AddCommGroup M] [Module A M]
end Associated
section Flat
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]
variable [Module B M] [IsScalarTower A B M] [Module.Flat A M]
variable [Module.Flat A B]
end Flat
section Symbolic
variable {R : Type*} [CommRing R]
noncomputable def symbolicPower (P : Ideal R) [P.IsPrime] (m : ℕ) : Ideal R :=
  (IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ m).comap
    (algebraMap R (Localization.AtPrime P))
end Symbolic
section Extension
variable {R : Type*} [CommRing R] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
variable (v : Valuation R Γ₀) (I : Ideal R) {π : Γ₀}
end Extension
section LocalExtension
open IsLocalRing
variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
section Multiplicative
variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
end Multiplicative
section Additive
variable {Γ : Type*} [LinearOrderedAddCommMonoidWithTop Γ]
end Additive
end LocalExtension
universe u v w
end GlobalTheory


