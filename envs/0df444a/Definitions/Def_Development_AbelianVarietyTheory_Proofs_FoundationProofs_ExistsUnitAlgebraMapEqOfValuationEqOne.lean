-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:31:53.453161+00:00
-- url     : https://prove2.me/theorems/12f20f5c-8407-4cf6-92be-fdb591e89d4a
-- title:
--   Exists Unit Algebra Map Eq Of Valuation Eq One
-- statement:
--   Definitions and structural lemmas for Exists Unit Algebra Map Eq Of Valuation Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUnitAlgebraMapEqOfValuationEqOne.lean

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
namespace GlobalTheory.PrimeElement
variable {R : Type*} [CommRing R] {π : R}
section AtPrime
variable [(Ideal.span {π}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
  [IsLocalization.AtPrime S (Ideal.span {π})]
end AtPrime
section Inter
variable [(Ideal.span {π}).IsPrime]
  (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  (K : Type*) [CommRing K] [IsDomain K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K]
end Inter
section Valuation
variable [(Ideal.span {π}).IsPrime]
  {A : Type*} [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  [IsDomain S] [IsDiscreteValuationRing S]
  (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K] [IsFractionRing S K]
end Valuation
end GlobalTheory.PrimeElement


