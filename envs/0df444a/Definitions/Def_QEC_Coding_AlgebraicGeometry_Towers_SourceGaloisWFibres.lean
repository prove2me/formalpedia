-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibres
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibres
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:55:55.497885+00:00
-- url     : https://prove2.me/theorems/b51cbfdb-81c4-4c32-b260-651b9c7e713d
-- title:
--   Source Galois WFibres
-- statement:
--   Definitions and structural lemmas for Source Galois WFibres, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWFibres.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing

set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
abbrev SourceGaloisWPlaceValuationRing (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) : Type :=
  P.valuationRing
noncomputable local instance (priority := 2000)
    sourceGaloisWPlaceValuationRingBaseModule (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Module (SourceGaloisWPlaceValuationRing m P) (SourceGaloisWClosureField m) :=
  @Algebra.toModule (SourceGaloisWPlaceValuationRing m P)
    (SourceGaloisWClosureField m) _ _
      (inferInstance : Algebra (SourceGaloisWPlaceValuationRing m P)
        (SourceGaloisWClosureField m))
attribute [local instance 2000] sourceGaloisWPlaceValuationRingBaseModule
noncomputable local instance (priority := 2000)
    sourceGaloisWPlaceValuationRingBaseFaithfulSMul (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    FaithfulSMul (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWClosureField m) :=
  (faithfulSMul_iff_algebraMap_injective
    (SourceGaloisWPlaceValuationRing m P) (SourceGaloisWClosureField m)).2
      (ValuationSubring.subtype_injective P.valuationRing)
attribute [local instance 2000] sourceGaloisWPlaceValuationRingBaseFaithfulSMul
noncomputable local instance (priority := 3000)
    sourceGaloisWClosureFieldClosureAlgebra (m : ℕ) :
    Algebra (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  (SourceGaloisWClosureField m).val.toRingHom.toAlgebra
attribute [local instance 3000] sourceGaloisWClosureFieldClosureAlgebra
noncomputable local instance (priority := 3000)
    sourceGaloisWClosureFieldClosureSMul (m : ℕ) :
    SMul (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  (sourceGaloisWClosureFieldClosureAlgebra m).toSMul
attribute [local instance 3000] sourceGaloisWClosureFieldClosureSMul
noncomputable local instance (priority := 3000)
    sourceGaloisWClosureFieldClosureModule (m : ℕ) :
    Module (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  @Algebra.toModule (SourceGaloisWClosureField m) (SourceGaloisClosureField m) _ _
    (sourceGaloisWClosureFieldClosureAlgebra m)
attribute [local instance 3000] sourceGaloisWClosureFieldClosureModule
noncomputable local instance (priority := 3000)
    sourceGaloisWClosureFieldClosureFree (m : ℕ) :
    Module.Free (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  Module.Free.of_divisionRing (SourceGaloisWClosureField m) (SourceGaloisClosureField m)
attribute [local instance 3000] sourceGaloisWClosureFieldClosureFree
noncomputable local instance (priority := 3000)
    sourceGaloisWClosureFieldBaseFree (m : ℕ) :
    Module.Free GaloisBaseField (SourceGaloisWClosureField m) :=
  Module.Free.of_divisionRing GaloisBaseField (SourceGaloisWClosureField m)
attribute [local instance 3000] sourceGaloisWClosureFieldBaseFree
noncomputable local instance (priority := 3000)
    sourceGaloisWClosureFieldClosureFaithfulSMul (m : ℕ) :
    FaithfulSMul (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  (faithfulSMul_iff_algebraMap_injective
    (SourceGaloisWClosureField m) (SourceGaloisClosureField m)).2
      (SourceGaloisWClosureField m).val.injective
attribute [local instance 3000] sourceGaloisWClosureFieldClosureFaithfulSMul
noncomputable local instance sourceGaloisWClosureFieldClosureScalarTower
    (m : ℕ) :
    IsScalarTower GaloisBaseField (SourceGaloisWClosureField m)
      (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisWClosureFieldClosureScalarTower
noncomputable local instance
    sourceGaloisWClosureFieldClosureTorsionFree (m : ℕ) :
    Module.IsTorsionFree (SourceGaloisWClosureField m)
      (SourceGaloisClosureField m) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (SourceGaloisWClosureField m).val.injective
attribute [local instance] sourceGaloisWClosureFieldClosureTorsionFree
noncomputable local instance
    sourceGaloisWClosureFieldClosureFiniteDimensional (m : ℕ) :
    FiniteDimensional (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  FiniteDimensional.right GaloisBaseField (SourceGaloisWClosureField m)
    (SourceGaloisClosureField m)
attribute [local instance] sourceGaloisWClosureFieldClosureFiniteDimensional
noncomputable local instance sourceGaloisWClosureFieldClosureIsGalois
    (m : ℕ) :
    IsGalois (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  IsGalois.tower_top_of_isGalois GaloisBaseField
    (SourceGaloisWClosureField m) (SourceGaloisClosureField m)
attribute [local instance] sourceGaloisWClosureFieldClosureIsGalois
noncomputable local instance (priority := 2000)
    sourceGaloisWPlaceValuationRingClosureAlgebra (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Algebra (SourceGaloisWPlaceValuationRing m P) (SourceGaloisClosureField m) :=
  ((algebraMap (SourceGaloisWClosureField m) (SourceGaloisClosureField m)).comp
    (algebraMap (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWClosureField m))).toAlgebra
attribute [local instance 2000] sourceGaloisWPlaceValuationRingClosureAlgebra
noncomputable local instance (priority := 2000)
    sourceGaloisWPlaceValuationRingClosureSMul (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    SMul (SourceGaloisWPlaceValuationRing m P) (SourceGaloisClosureField m) :=
  (sourceGaloisWPlaceValuationRingClosureAlgebra m P).toSMul
attribute [local instance 2000] sourceGaloisWPlaceValuationRingClosureSMul
noncomputable local instance (priority := 2000)
    sourceGaloisWPlaceValuationRingClosureModule (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Module (SourceGaloisWPlaceValuationRing m P) (SourceGaloisClosureField m) :=
  @Algebra.toModule (SourceGaloisWPlaceValuationRing m P)
    (SourceGaloisClosureField m) _ _
      (sourceGaloisWPlaceValuationRingClosureAlgebra m P)
attribute [local instance 2000] sourceGaloisWPlaceValuationRingClosureModule
abbrev SourceGaloisWPlaceIntegralClosure (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) : Type :=
  integralClosure (SourceGaloisWPlaceValuationRing m P) (SourceGaloisClosureField m)
noncomputable local instance sourceGaloisWPlaceBaseScalarTower (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsScalarTower (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWClosureField m) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisWPlaceBaseScalarTower
noncomputable local instance
    sourceGaloisWPlaceIntegralClosureFractionTower (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsScalarTower (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWPlaceIntegralClosure m P) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisWPlaceIntegralClosureFractionTower
noncomputable local instance sourceGaloisWRelativeGalFinite (m : ℕ) :
    Finite Gal((SourceGaloisClosureField m) / (SourceGaloisWClosureField m)) :=
  Fintype.finite
    (AlgEquiv.fintype (SourceGaloisWClosureField m) (SourceGaloisClosureField m))
attribute [local instance] sourceGaloisWRelativeGalFinite
noncomputable local instance sourceGaloisWPlaceIntegralClosureTorsionFree
    (m : ℕ) (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Module.IsTorsionFree (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWPlaceIntegralClosure m P) := by
  letI : Module.IsTorsionFree (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisClosureField m) :=
    Module.IsTorsionFree.trans_faithfulSMul
      (SourceGaloisWPlaceValuationRing m P) (SourceGaloisWClosureField m)
        (SourceGaloisClosureField m)
  exact IsIntegralClosure.isTorsionFree
    (SourceGaloisWPlaceValuationRing m P) (SourceGaloisClosureField m)
attribute [local instance] sourceGaloisWPlaceIntegralClosureTorsionFree
noncomputable local instance sourceGaloisWPlaceIntegralClosureFaithfulSMul
    (m : ℕ) (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    FaithfulSMul (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWPlaceIntegralClosure m P) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 (by
    intro a b hab
    apply ValuationSubring.subtype_injective P.valuationRing
    apply (SourceGaloisWClosureField m).val.injective
    exact congrArg (fun z : SourceGaloisWPlaceIntegralClosure m P =>
      (z : SourceGaloisClosureField m)) hab)
attribute [local instance] sourceGaloisWPlaceIntegralClosureFaithfulSMul
noncomputable local instance sourceGaloisWPlaceIntegralClosureFinite
    (m : ℕ) (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    Module.Finite (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWPlaceIntegralClosure m P) := by
  letI : IsDiscreteValuationRing (SourceGaloisWPlaceValuationRing m P) :=
    P.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite (SourceGaloisWPlaceValuationRing m P)
    (SourceGaloisWClosureField m) (SourceGaloisClosureField m)
      (SourceGaloisWPlaceIntegralClosure m P)
attribute [local instance] sourceGaloisWPlaceIntegralClosureFinite
noncomputable local instance
    sourceGaloisWPlaceIntegralClosureIsFractionRing (m : ℕ)
    (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsFractionRing (SourceGaloisWPlaceIntegralClosure m P)
      (SourceGaloisClosureField m) :=
  integralClosure.isFractionRing_of_finite_extension
    (SourceGaloisWClosureField m) (SourceGaloisClosureField m)
attribute [local instance] sourceGaloisWPlaceIntegralClosureIsFractionRing
noncomputable local instance sourceGaloisWPlaceIntegralClosureIsDedekind
    (m : ℕ) (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsDedekindDomain (SourceGaloisWPlaceIntegralClosure m P) := by
  letI : IsDiscreteValuationRing (SourceGaloisWPlaceValuationRing m P) :=
    P.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain (SourceGaloisWPlaceValuationRing m P)
    (SourceGaloisWClosureField m) (SourceGaloisClosureField m)
attribute [local instance] sourceGaloisWPlaceIntegralClosureIsDedekind
noncomputable local instance sourceGaloisWPlaceIntegralClosureAction
    (m : ℕ) (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    MulSemiringAction
      Gal((SourceGaloisClosureField m) / (SourceGaloisWClosureField m))
      (SourceGaloisWPlaceIntegralClosure m P) :=
  IsIntegralClosure.MulSemiringAction (SourceGaloisWPlaceValuationRing m P)
    (SourceGaloisWClosureField m) (SourceGaloisClosureField m)
      (SourceGaloisWPlaceIntegralClosure m P)
attribute [local instance] sourceGaloisWPlaceIntegralClosureAction
noncomputable local instance sourceGaloisWPlaceIntegralClosureIsGaloisGroup
    (m : ℕ) (P : GlobalPlace F256 (SourceGaloisWClosureField m)) :
    IsGaloisGroup
      Gal((SourceGaloisClosureField m) / (SourceGaloisWClosureField m))
      (SourceGaloisWPlaceValuationRing m P)
      (SourceGaloisWPlaceIntegralClosure m P) :=
  IsGaloisGroup.of_isFractionRing
    Gal((SourceGaloisClosureField m) / (SourceGaloisWClosureField m))
    (SourceGaloisWPlaceValuationRing m P) (SourceGaloisWPlaceIntegralClosure m P)
    (SourceGaloisWClosureField m) (SourceGaloisClosureField m)
attribute [local instance] sourceGaloisWPlaceIntegralClosureIsGaloisGroup
abbrev SourceGaloisWZeroIntegralClosure (m : ℕ) : Type :=
  SourceGaloisWPlaceIntegralClosure m (sourceGaloisWClosureZeroPlace m)
abbrev SourceGaloisWInfinityIntegralClosure (m : ℕ) : Type :=
  SourceGaloisWPlaceIntegralClosure m (sourceGaloisWClosureInfinityPlace m)
abbrev SourceGaloisWZeroPrime (m : ℕ) :
    Set (Ideal (SourceGaloisWZeroIntegralClosure m)) :=
  (IsLocalRing.maximalIdeal
    (sourceGaloisWClosureZeroPlace m).valuationRing).primesOver
      (SourceGaloisWZeroIntegralClosure m)
abbrev SourceGaloisWInfinityPrime (m : ℕ) :
    Set (Ideal (SourceGaloisWInfinityIntegralClosure m)) :=
  (IsLocalRing.maximalIdeal
    (sourceGaloisWClosureInfinityPlace m).valuationRing).primesOver
      (SourceGaloisWInfinityIntegralClosure m)
noncomputable def sourceGaloisWZeroRamificationIndex (m : ℕ) : ℕ :=
  (IsLocalRing.maximalIdeal
    (sourceGaloisWClosureZeroPlace m).valuationRing).ramificationIdxIn
      (SourceGaloisWZeroIntegralClosure m)
noncomputable def sourceGaloisWInfinityRamificationIndex (m : ℕ) : ℕ :=
  (IsLocalRing.maximalIdeal
    (sourceGaloisWClosureInfinityPlace m).valuationRing).ramificationIdxIn
      (SourceGaloisWInfinityIntegralClosure m)
noncomputable def sourceGaloisWZeroInertiaDegree (m : ℕ) : ℕ :=
  (IsLocalRing.maximalIdeal
    (sourceGaloisWClosureZeroPlace m).valuationRing).inertiaDegIn
      (SourceGaloisWZeroIntegralClosure m)
noncomputable def sourceGaloisWInfinityInertiaDegree (m : ℕ) : ℕ :=
  (IsLocalRing.maximalIdeal
    (sourceGaloisWClosureInfinityPlace m).valuationRing).inertiaDegIn
      (SourceGaloisWInfinityIntegralClosure m)
noncomputable def sourceGaloisWRelativeDegree (m : ℕ) : ℕ :=
  Module.finrank (SourceGaloisWClosureField m) (SourceGaloisClosureField m)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


