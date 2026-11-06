-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorResidueTransport
-- name    : QEC_Coding_AlgebraicGeometry_Residues_Direct_FactorResidueTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T18:37:08.667736+00:00
-- url     : https://prove2.me/theorems/237a6404-7a2d-40f9-820f-523f48c1483d
-- title:
--   Factor Residue Transport
-- statement:
--   Definitions and structural lemmas for Factor Residue Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/FactorResidueTransport.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport
open scoped Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
noncomputable local instance directFactorResidueTransport_constantAlgebra : Algebra k F := AffinePlace.constantAlgebra k F
attribute [local instance] directFactorResidueTransport_constantAlgebra
abbrev R : Type _ := k[X]
abbrev B : Type _ := _root_.FunctionField.ringOfIntegers k F
local instance directFactorResidueTransport_isTorsionFree : Module.IsTorsionFree (R k) (B k F) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (_root_.FunctionField.ringOfIntegers.algebraMap_injective k F)
attribute [local instance] directFactorResidueTransport_isTorsionFree
open DirectIntegralDifferentialResidue
noncomputable def directFactorLocalizationEquiv
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    Localization.AtPrime (P : Ideal (B k F)) ≃+*
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).valuationRing := by
  let C : AffinePlace.carrier k F := directFactorPlace k F p P
  change Localization.AtPrime C.asIdeal ≃+* (C.valuation F).valuationSubring
  let e₁ : Localization.AtPrime C.asIdeal ≃+*
      C.valuationSubringAtPrime F :=
    (Localization.algEquiv C.asIdeal.primeCompl
      (C.valuationSubringAtPrime F)).toRingEquiv
  let hsub : (C.valuationSubringAtPrime F).toSubring =
      (C.valuation F).valuationSubring.toSubring :=
    congrArg ValuationSubring.toSubring
      C.valuationSubringAtPrime_eq_valuationSubring
  let e₂ : C.valuationSubringAtPrime F ≃+*
      (C.valuation F).valuationSubring :=
    RingEquiv.subringCongr hsub
  exact e₁.trans e₂
noncomputable def directFactorResidueEquiv
    (p : IsDedekindDomain.HeightOneSpectrum (R k))
    (P : (factors (Ideal.map (algebraMap (R k) (B k F)) p.asIdeal)).toFinset) :
    (P : Ideal (B k F)).ResidueField ≃+*
      (AffinePlace.globalPlace k F (directFactorPlace k F p P)).residueField :=
  IsLocalRing.ResidueField.mapEquiv (directFactorLocalizationEquiv k F p P)
end QEC.Coding.AlgebraicGeometry.DirectFactorResidueTransport


