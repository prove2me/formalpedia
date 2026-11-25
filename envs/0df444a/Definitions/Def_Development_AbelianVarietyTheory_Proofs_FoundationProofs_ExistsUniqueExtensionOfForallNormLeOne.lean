-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:00:19.352862+00:00
-- url     : https://prove2.me/theorems/753311aa-efbe-588f-b7ac-f5e8ca63d023
-- title:
--   Exists Unique Extension Of Forall Norm Le One
-- statement:
--   Definitions and structural lemmas for Exists Unique Extension Of Forall Norm Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open IsLocalRing
section Affine
variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
  [Algebra.FiniteType ℤ A]
omit [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A] in

theorem isUnit_val_comp_of_ne_zero {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (y : A →+* integralClosure ℤ_[p] K) {a : A} (h : y a ≠ 0) :
    IsUnit ((algebraMap (integralClosure ℤ_[p] K) K).comp y a) :=
  IsUnit.mk0 _ fun h0 => h (Subtype.ext h0)
variable {a : A} {S : Type*} [CommRing S] [Algebra A S] [IsLocalization.Away a S]
end Affine
section Scheme
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
local notation "genericPt(" p ", " K ", " y ")" =>
  Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y
variable {Z : Scheme.{0}} [IsIntegral Z] (π : Z ⟶ Spec (.of ℤ)) [Flat π] [LocallyOfFiniteType π]
include π
end Scheme
end GlobalTheory


