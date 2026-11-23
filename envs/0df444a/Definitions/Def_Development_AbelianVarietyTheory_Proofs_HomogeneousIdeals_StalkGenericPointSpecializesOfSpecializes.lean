-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_StalkGenericPointSpecializesOfSpecializes
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_StalkGenericPointSpecializesOfSpecializes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:21.667182+00:00
-- url     : https://prove2.me/theorems/19db4e0b-c530-45bd-8e06-30c9e0f23b5f
-- title:
--   Stalk Generic Point Specializes Of Specializes
-- statement:
--   Definitions and structural lemmas for Stalk Generic Point Specializes Of Specializes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/StalkGenericPointSpecializesOfSpecializes.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory IsLocalRing
universe u
namespace GlobalTheory
section Generisation
variable {Z : Scheme.{u}} (η : Z) [IsDomain (Z.presheaf.stalk η)]
noncomputable def stalkGenericPoint : Z :=
  Z.fromSpecStalk η (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Z.presheaf.stalk η))
variable [IsDiscreteValuationRing (Z.presheaf.stalk η)]
end Generisation
section ResidueCharacteristic
end ResidueCharacteristic
section LocalSource
variable {Z : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing R]
variable {η ξ : Z} [IsDomain (Z.presheaf.stalk η)] [IsDiscreteValuationRing (Z.presheaf.stalk η)]
end LocalSource
section ThetaShiftProofs
open PowerSeries
noncomputable def powerSeriesPrimeX (O : Type u) [CommRing O] [IsDomain O] :
    Spec (CommRingCat.of O⟦X⟧) :=
  (⟨Ideal.span {X}, span_X_isPrime⟩ : PrimeSpectrum O⟦X⟧)
variable {Z : Scheme.{u}} {η ξ : Z} [IsDomain (Z.presheaf.stalk η)]
  [IsDiscreteValuationRing (Z.presheaf.stalk η)]
  {O : Type u} [CommRing O] [IsDomain O] [IsLocalRing O]
end ThetaShiftProofs
section Model
open PowerSeries
end Model
end GlobalTheory


