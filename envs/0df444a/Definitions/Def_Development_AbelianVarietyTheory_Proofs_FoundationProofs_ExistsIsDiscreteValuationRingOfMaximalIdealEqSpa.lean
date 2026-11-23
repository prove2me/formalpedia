-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:21.951839+00:00
-- url     : https://prove2.me/theorems/5683e6af-dcc0-454b-9ccb-d0d18ed5ff88
-- title:
--   Exists Is Discrete Valuation Ring Of Maximal Ideal Eq Spa
-- statement:
--   Definitions and structural lemmas for Exists Is Discrete Valuation Ring Of Maximal Ideal Eq Spa, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa.lean

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
open Polynomial IsLocalRing
open scoped TensorProduct
section Lift
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
end Lift
section SeparablePoints
variable {R A B K : Type*} [CommRing R] [CommRing A] [CommRing B] [Field K]
  [Algebra R A] [Algebra R B] [Algebra R K]
end SeparablePoints
section QuasiSection
universe u
variable {R : Type*} {A B : Type u} {K : Type*} [CommRing R] [CommRing A] [CommRing B] [Field K]
  [Algebra R A] [Algebra R B] [Algebra R K] [IsLocalRing B] [Algebra B K] [IsScalarTower R B K]
  [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]
  [Algebra.IsSeparable (ResidueField B) K]
end QuasiSection
section LocalForms
universe u
variable {B W : Type u} {K : Type*} [CommRing B] [CommRing W] [Field K] [IsLocalRing B]
  [Algebra B W] [Algebra B K] [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]
end LocalForms
section LocalHenselian
universe u
variable {B W : Type u} {K : Type*} [CommRing B] [CommRing W] [Field K] [HenselianLocalRing B]
  [Algebra B W] [Algebra B K] [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]
  [Algebra.IsSeparable (ResidueField B) K]
end LocalHenselian
section DiscreteValuation
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
end DiscreteValuation
end GlobalTheory


