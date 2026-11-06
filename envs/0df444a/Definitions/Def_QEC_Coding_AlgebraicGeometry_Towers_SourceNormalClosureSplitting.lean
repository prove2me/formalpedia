-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureSplitting
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureSplitting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:34:25.947192+00:00
-- url     : https://prove2.me/theorems/9ecca4a2-3e39-4933-9771-d2b34332b948
-- title:
--   Source Normal Closure Splitting
-- statement:
--   Definitions and structural lemmas for Source Normal Closure Splitting, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceNormalClosureSplitting.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSeedSplittingIdeals
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Coset.Card
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepDistinguishedCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepFieldEmbedding
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepReciprocalRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_comapAlgEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepDistinguishedCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepFieldEmbedding
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepReciprocalRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.comapAlgEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open scoped Pointwise
noncomputable local instance (priority := 3000)
    sourceGaloisClosureFieldBaseAlgebraPinned (m : ℕ) :
    Algebra GaloisBaseField (SourceGaloisClosureField m) :=
  sourceGaloisClosureFieldAlgebra m
attribute [local instance 3000] sourceGaloisClosureFieldBaseAlgebraPinned
noncomputable local instance (priority := 3000)
    sourceGaloisClosureFieldBaseSMulPinned (m : ℕ) :
    SMul GaloisBaseField (SourceGaloisClosureField m) :=
  (sourceGaloisClosureFieldBaseAlgebraPinned m).toSMul
attribute [local instance 3000] sourceGaloisClosureFieldBaseSMulPinned
noncomputable local instance (priority := 3000)
    sourceGaloisClosureFieldBaseModulePinned (m : ℕ) :
    Module GaloisBaseField (SourceGaloisClosureField m) :=
  @Algebra.toModule GaloisBaseField (SourceGaloisClosureField m) _ _
    (sourceGaloisClosureFieldBaseAlgebraPinned m)
attribute [local instance 3000] sourceGaloisClosureFieldBaseModulePinned
noncomputable local instance (priority := 3000)
    sourceGaloisClosureGalFinite (m : ℕ) :
    Finite Gal((SourceGaloisClosureField m) / GaloisBaseField) :=
  Fintype.finite
    (AlgEquiv.fintype GaloisBaseField (SourceGaloisClosureField m))
attribute [local instance 3000] sourceGaloisClosureGalFinite
noncomputable local instance (priority := 2000)
    sourceGaloisClosureBaseValuationRingBaseModule :
    Module SourceSeedBaseValuationRing GaloisBaseField :=
  @Algebra.toModule SourceSeedBaseValuationRing GaloisBaseField _ _
    (inferInstance : Algebra SourceSeedBaseValuationRing GaloisBaseField)
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingBaseModule
noncomputable local instance (priority := 2000)
    sourceGaloisClosureBaseValuationRingBaseFaithfulSMul :
    FaithfulSMul SourceSeedBaseValuationRing GaloisBaseField :=
  (faithfulSMul_iff_algebraMap_injective
    SourceSeedBaseValuationRing GaloisBaseField).2
      (ValuationSubring.subtype_injective
        sourceSeedFixedBaseOnePlace.valuationRing)
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingBaseFaithfulSMul
noncomputable local instance (priority := 2000)
    sourceGaloisClosureSeedBaseValuationRingAlgebra (m : ℕ) :
    Algebra SourceSeedBaseValuationRing (SourceField m) :=
  ((algebraMap GaloisBaseField (SourceField m)).comp
    (algebraMap SourceSeedBaseValuationRing GaloisBaseField)).toAlgebra
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingAlgebra
noncomputable local instance (priority := 2000)
    sourceGaloisClosureSeedBaseValuationRingSMul (m : ℕ) :
    SMul SourceSeedBaseValuationRing (SourceField m) :=
  (sourceGaloisClosureSeedBaseValuationRingAlgebra m).toSMul
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingSMul
noncomputable local instance (priority := 2000)
    sourceGaloisClosureSeedBaseValuationRingModule (m : ℕ) :
    Module SourceSeedBaseValuationRing (SourceField m) :=
  @Algebra.toModule SourceSeedBaseValuationRing (SourceField m) _ _
    (sourceGaloisClosureSeedBaseValuationRingAlgebra m)
attribute [local instance 2000] sourceGaloisClosureSeedBaseValuationRingModule
noncomputable local instance (priority := 2000)
    sourceGaloisClosureBaseValuationRingAlgebra (m : ℕ) :
    Algebra SourceSeedBaseValuationRing (SourceGaloisClosureField m) :=
  ((algebraMap GaloisBaseField (SourceGaloisClosureField m)).comp
    (algebraMap SourceSeedBaseValuationRing GaloisBaseField)).toAlgebra
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingAlgebra
noncomputable local instance (priority := 2000)
    sourceGaloisClosureBaseValuationRingSMul (m : ℕ) :
    SMul SourceSeedBaseValuationRing (SourceGaloisClosureField m) :=
  (sourceGaloisClosureBaseValuationRingAlgebra m).toSMul
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingSMul
noncomputable local instance (priority := 2000)
    sourceGaloisClosureBaseValuationRingModule (m : ℕ) :
    Module SourceSeedBaseValuationRing (SourceGaloisClosureField m) :=
  @Algebra.toModule SourceSeedBaseValuationRing (SourceGaloisClosureField m) _ _
    (sourceGaloisClosureBaseValuationRingAlgebra m)
attribute [local instance 2000] sourceGaloisClosureBaseValuationRingModule
abbrev SourceGaloisClosureIntegralClosure (m : ℕ) : Type :=
  integralClosure SourceSeedBaseValuationRing (SourceGaloisClosureField m)
noncomputable local instance sourceGaloisClosureBaseScalarTower (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing GaloisBaseField
      (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisClosureBaseScalarTower
noncomputable local instance sourceGaloisClosureSeedBaseScalarTower
    (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing GaloisBaseField (SourceField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisClosureSeedBaseScalarTower
noncomputable local instance sourceSeedIntegralClosureFractionTower
    (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing
      (SourceSeedIntegralClosure m) (SourceField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceSeedIntegralClosureFractionTower
noncomputable local instance sourceGaloisClosureIntegralClosureFractionTower
    (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisClosureIntegralClosureFractionTower
noncomputable def sourceSeedIntegralClosureToClosure (m : ℕ) :
    SourceSeedIntegralClosure m →ₐ[SourceSeedBaseValuationRing]
      SourceGaloisClosureIntegralClosure m :=
  ((sourceGaloisSeedToClosure m).restrictScalars
    SourceSeedBaseValuationRing).mapIntegralClosure
noncomputable local instance sourceSeedIntegralClosureClosureAlgebra
    (m : ℕ) :
    Algebra (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m) :=
  (sourceSeedIntegralClosureToClosure m).toRingHom.toAlgebra
attribute [local instance] sourceSeedIntegralClosureClosureAlgebra
noncomputable local instance (priority := 2000)
    sourceSeedIntegralClosureClosureSMul (m : ℕ) :
    SMul (SourceSeedIntegralClosure m) (SourceGaloisClosureIntegralClosure m) :=
  (sourceSeedIntegralClosureClosureAlgebra m).toSMul
attribute [local instance 2000] sourceSeedIntegralClosureClosureSMul
noncomputable local instance (priority := 2000)
    sourceSeedIntegralClosureClosureModule (m : ℕ) :
    Module (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m) :=
  @Algebra.toModule (SourceSeedIntegralClosure m)
    (SourceGaloisClosureIntegralClosure m) _ _
      (sourceSeedIntegralClosureClosureAlgebra m)
attribute [local instance 2000] sourceSeedIntegralClosureClosureModule
theorem sourceSeedIntegralClosureToClosure_coe (m : ℕ)
    (x : SourceSeedIntegralClosure m) :
    ((algebraMap (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m) x :
        SourceGaloisClosureIntegralClosure m) : SourceGaloisClosureField m) =
      sourceGaloisSeedToClosure m (x : SourceField m) :=
  rfl
noncomputable local instance
    sourceGaloisClosureIntegralClosureScalarTower (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing
      (SourceSeedIntegralClosure m) (SourceGaloisClosureIntegralClosure m) :=
  IsScalarTower.of_algebraMap_eq' <| by
    apply RingHom.ext
    intro r
    apply IsIntegralClosure.algebraMap_injective
      (SourceGaloisClosureIntegralClosure m) SourceSeedBaseValuationRing
        (SourceGaloisClosureField m)
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply
      SourceSeedBaseValuationRing (SourceGaloisClosureIntegralClosure m)
        (SourceGaloisClosureField m)]
    change algebraMap SourceSeedBaseValuationRing (SourceGaloisClosureField m) r =
      ((algebraMap (SourceSeedIntegralClosure m)
        (SourceGaloisClosureIntegralClosure m)
          (algebraMap SourceSeedBaseValuationRing
            (SourceSeedIntegralClosure m) r) :
              SourceGaloisClosureIntegralClosure m) : SourceGaloisClosureField m)
    rw [sourceSeedIntegralClosureToClosure_coe]
    change algebraMap SourceSeedBaseValuationRing (SourceGaloisClosureField m) r =
      sourceGaloisSeedToClosure m
        (algebraMap (SourceSeedIntegralClosure m) (SourceField m)
          (algebraMap SourceSeedBaseValuationRing
            (SourceSeedIntegralClosure m) r))
    rw [← IsScalarTower.algebraMap_apply SourceSeedBaseValuationRing
        (SourceSeedIntegralClosure m) (SourceField m),
      IsScalarTower.algebraMap_apply SourceSeedBaseValuationRing
        GaloisBaseField (SourceField m),
      (sourceGaloisSeedToClosure m).commutes,
      ← IsScalarTower.algebraMap_apply SourceSeedBaseValuationRing
        GaloisBaseField (SourceGaloisClosureField m)]
attribute [local instance] sourceGaloisClosureIntegralClosureScalarTower
noncomputable local instance sourceGaloisClosureIntegralOverSeedIntegral
    (m : ℕ) :
    Algebra.IsIntegral (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m) :=
  Algebra.IsIntegral.tower_top SourceSeedBaseValuationRing
attribute [local instance] sourceGaloisClosureIntegralOverSeedIntegral
theorem sourceSeedIntegralClosureToClosure_injective (m : ℕ) :
    Function.Injective (algebraMap (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m)) := by
  intro x y hxy
  apply Subtype.ext
  apply (sourceGaloisSeedToClosure m).injective
  calc
    sourceGaloisSeedToClosure m (x : SourceField m) =
        ((algebraMap (SourceSeedIntegralClosure m)
          (SourceGaloisClosureIntegralClosure m) x :
            SourceGaloisClosureIntegralClosure m) : SourceGaloisClosureField m) :=
      (sourceSeedIntegralClosureToClosure_coe m x).symm
    _ = ((algebraMap (SourceSeedIntegralClosure m)
          (SourceGaloisClosureIntegralClosure m) y :
            SourceGaloisClosureIntegralClosure m) : SourceGaloisClosureField m) :=
      congrArg (fun z : SourceGaloisClosureIntegralClosure m =>
        (z : SourceGaloisClosureField m)) hxy
    _ = sourceGaloisSeedToClosure m (y : SourceField m) :=
      sourceSeedIntegralClosureToClosure_coe m y
noncomputable local instance sourceGaloisClosureIntegralOverSeedTorsionFree
    (m : ℕ) :
    Module.IsTorsionFree (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (sourceSeedIntegralClosureToClosure_injective m)
attribute [local instance] sourceGaloisClosureIntegralOverSeedTorsionFree
noncomputable local instance sourceGaloisClosureIntegralClosureTorsionFree
    (m : ℕ) :
    Module.IsTorsionFree SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) := by
  letI : Module.IsTorsionFree SourceSeedBaseValuationRing
      (SourceGaloisClosureField m) := by
    apply Module.IsTorsionFree.comap
      (R := SourceSeedBaseValuationRing)
      (S := SourceGaloisClosureField m)
      (M := SourceGaloisClosureField m)
      (algebraMap SourceSeedBaseValuationRing (SourceGaloisClosureField m))
    · intro r hr
      have hinjective : Function.Injective
          (algebraMap SourceSeedBaseValuationRing
            (SourceGaloisClosureField m)) :=
        (algebraMap GaloisBaseField (SourceGaloisClosureField m)).injective.comp
          (ValuationSubring.subtype_injective
            sourceSeedFixedBaseOnePlace.valuationRing)
      exact IsRegular.of_ne_zero fun hzero =>
        hr.ne_zero (hinjective (by simpa only [map_zero] using hzero))
    · intro r x
      simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
  exact IsIntegralClosure.isTorsionFree
    SourceSeedBaseValuationRing (SourceGaloisClosureField m)
attribute [local instance] sourceGaloisClosureIntegralClosureTorsionFree
noncomputable local instance sourceGaloisClosureIntegralClosureFinite
    (m : ℕ) :
    Module.Finite SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite SourceSeedBaseValuationRing
    GaloisBaseField (SourceGaloisClosureField m)
      (SourceGaloisClosureIntegralClosure m)
attribute [local instance] sourceGaloisClosureIntegralClosureFinite
noncomputable local instance
    sourceGaloisClosureIntegralClosureIsFractionRing (m : ℕ) :
    IsFractionRing (SourceGaloisClosureIntegralClosure m)
      (SourceGaloisClosureField m) :=
  integralClosure.isFractionRing_of_finite_extension
    GaloisBaseField (SourceGaloisClosureField m)
attribute [local instance] sourceGaloisClosureIntegralClosureIsFractionRing
noncomputable local instance sourceGaloisClosureIntegralClosureIsDedekind
    (m : ℕ) : IsDedekindDomain (SourceGaloisClosureIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain SourceSeedBaseValuationRing
    GaloisBaseField (SourceGaloisClosureField m)
attribute [local instance] sourceGaloisClosureIntegralClosureIsDedekind
noncomputable local instance sourceGaloisClosureIntegralClosureAction
    (m : ℕ) :
    MulSemiringAction
      Gal((SourceGaloisClosureField m) / GaloisBaseField)
      (SourceGaloisClosureIntegralClosure m) :=
  IsIntegralClosure.MulSemiringAction SourceSeedBaseValuationRing
    GaloisBaseField (SourceGaloisClosureField m)
      (SourceGaloisClosureIntegralClosure m)
attribute [local instance] sourceGaloisClosureIntegralClosureAction
noncomputable local instance (priority := 3000)
    sourceGaloisClosureIntegralClosureSMul (m : ℕ) :
    SMul Gal((SourceGaloisClosureField m) / GaloisBaseField)
      (SourceGaloisClosureIntegralClosure m) :=
  (sourceGaloisClosureIntegralClosureAction m).toDistribMulAction.toMulAction.toSMul
attribute [local instance 3000] sourceGaloisClosureIntegralClosureSMul
noncomputable local instance (priority := 3000)
    sourceGaloisClosureIntegralClosureIdealAction (m : ℕ) :
    MulSemiringAction
      Gal((SourceGaloisClosureField m) / GaloisBaseField)
      (Ideal (SourceGaloisClosureIntegralClosure m)) :=
  Ideal.pointwiseMulSemiringAction
attribute [local instance 3000] sourceGaloisClosureIntegralClosureIdealAction
noncomputable local instance (priority := 4000)
    sourceGaloisClosureIntegralClosureIdealMulAction (m : ℕ) :
    MulAction
      Gal((SourceGaloisClosureField m) / GaloisBaseField)
      (Ideal (SourceGaloisClosureIntegralClosure m)) :=
  (sourceGaloisClosureIntegralClosureIdealAction m).toDistribMulAction.toMulAction
attribute [local instance 4000] sourceGaloisClosureIntegralClosureIdealMulAction
noncomputable local instance
    sourceGaloisClosureIntegralClosureActionCommutesWithBase (m : ℕ) :
    SMulCommClass
      Gal((SourceGaloisClosureField m) / GaloisBaseField)
      SourceSeedBaseValuationRing (SourceGaloisClosureIntegralClosure m) where
  smul_comm g r x := by
    apply IsIntegralClosure.algebraMap_injective
      (SourceGaloisClosureIntegralClosure m) SourceSeedBaseValuationRing
        (SourceGaloisClosureField m)
    calc
      algebraMap (SourceGaloisClosureIntegralClosure m) (SourceGaloisClosureField m)
          (g • (r • x)) =
          g (algebraMap (SourceGaloisClosureIntegralClosure m)
            (SourceGaloisClosureField m) (r • x)) :=
        algebraMap_galRestrict_apply
          SourceSeedBaseValuationRing g (r • x)
      _ = g (algebraMap SourceSeedBaseValuationRing
            (SourceGaloisClosureField m) r *
          algebraMap (SourceGaloisClosureIntegralClosure m)
            (SourceGaloisClosureField m) x) := by
        rw [Algebra.smul_def, map_mul,
          IsScalarTower.algebraMap_apply SourceSeedBaseValuationRing
            (SourceGaloisClosureIntegralClosure m) (SourceGaloisClosureField m)]
      _ = algebraMap SourceSeedBaseValuationRing
            (SourceGaloisClosureField m) r *
          g (algebraMap (SourceGaloisClosureIntegralClosure m)
            (SourceGaloisClosureField m) x) := by
        rw [map_mul]
        congr 1
        exact g.commutes (r : GaloisBaseField)
      _ = algebraMap SourceSeedBaseValuationRing
            (SourceGaloisClosureField m) r *
          algebraMap (SourceGaloisClosureIntegralClosure m)
            (SourceGaloisClosureField m) (g • x) := by
        congr 1
        exact (algebraMap_galRestrict_apply
          SourceSeedBaseValuationRing g x).symm
      _ = algebraMap (SourceGaloisClosureIntegralClosure m)
          (SourceGaloisClosureField m) (r • (g • x)) := by
        rw [Algebra.smul_def, map_mul,
          IsScalarTower.algebraMap_apply SourceSeedBaseValuationRing
            (SourceGaloisClosureIntegralClosure m) (SourceGaloisClosureField m)]
attribute [local instance] sourceGaloisClosureIntegralClosureActionCommutesWithBase
noncomputable local instance sourceGaloisClosureIntegralClosureIsGaloisGroup
    (m : ℕ) :
    IsGaloisGroup
      Gal((SourceGaloisClosureField m) / GaloisBaseField)
      SourceSeedBaseValuationRing (SourceGaloisClosureIntegralClosure m) :=
  IsGaloisGroup.of_isFractionRing
    Gal((SourceGaloisClosureField m) / GaloisBaseField)
    SourceSeedBaseValuationRing (SourceGaloisClosureIntegralClosure m)
    GaloisBaseField (SourceGaloisClosureField m)
attribute [local instance] sourceGaloisClosureIntegralClosureIsGaloisGroup
abbrev sourceSeedClosureFieldRange (m : ℕ) :
    IntermediateField GaloisBaseField (SourceGaloisClosureField m) :=
  (sourceGaloisSeedToClosure m).fieldRange
noncomputable local instance (priority := 3000)
    sourceSeedClosureFieldRangeAlgebra (m : ℕ) :
    Algebra GaloisBaseField (sourceSeedClosureFieldRange m) :=
  IntermediateField.algebra' (sourceSeedClosureFieldRange m)
attribute [local instance 3000] sourceSeedClosureFieldRangeAlgebra
noncomputable local instance (priority := 3000)
    sourceSeedClosureFieldRangeSMul (m : ℕ) :
    SMul GaloisBaseField (sourceSeedClosureFieldRange m) :=
  (sourceSeedClosureFieldRangeAlgebra m).toSMul
attribute [local instance 3000] sourceSeedClosureFieldRangeSMul
noncomputable local instance (priority := 3000)
    sourceSeedClosureFieldRangeModule (m : ℕ) :
    Module GaloisBaseField (sourceSeedClosureFieldRange m) :=
  @Algebra.toModule GaloisBaseField (sourceSeedClosureFieldRange m) _ _
    (sourceSeedClosureFieldRangeAlgebra m)
attribute [local instance 3000] sourceSeedClosureFieldRangeModule
abbrev sourceSeedClosureFixingSubgroup (m : ℕ) :
    Subgroup Gal((SourceGaloisClosureField m) / GaloisBaseField) :=
  (sourceSeedClosureFieldRange m).fixingSubgroup
theorem sourceSeedClosureFixingSubgroup_smul_algebraMap (m : ℕ)
    (h : sourceSeedClosureFixingSubgroup m)
    (b : SourceSeedIntegralClosure m) :
    (h : Gal((SourceGaloisClosureField m) / GaloisBaseField)) •
        algebraMap (SourceSeedIntegralClosure m)
          (SourceGaloisClosureIntegralClosure m) b =
      algebraMap (SourceSeedIntegralClosure m)
        (SourceGaloisClosureIntegralClosure m) b := by
  apply IsIntegralClosure.algebraMap_injective
    (SourceGaloisClosureIntegralClosure m) SourceSeedBaseValuationRing
      (SourceGaloisClosureField m)
  have hcoe : algebraMap (SourceGaloisClosureIntegralClosure m)
      (SourceGaloisClosureField m)
        (algebraMap (SourceSeedIntegralClosure m)
          (SourceGaloisClosureIntegralClosure m) b) =
      sourceGaloisSeedToClosure m (b : SourceField m) := by
    change ((algebraMap (SourceSeedIntegralClosure m)
      (SourceGaloisClosureIntegralClosure m) b :
        SourceGaloisClosureIntegralClosure m) : SourceGaloisClosureField m) = _
    exact sourceSeedIntegralClosureToClosure_coe m b
  calc
    algebraMap (SourceGaloisClosureIntegralClosure m) (SourceGaloisClosureField m)
        ((h : Gal((SourceGaloisClosureField m) / GaloisBaseField)) •
          algebraMap (SourceSeedIntegralClosure m)
            (SourceGaloisClosureIntegralClosure m) b) =
        (h : Gal((SourceGaloisClosureField m) / GaloisBaseField))
          (algebraMap (SourceGaloisClosureIntegralClosure m)
            (SourceGaloisClosureField m)
              (algebraMap (SourceSeedIntegralClosure m)
                (SourceGaloisClosureIntegralClosure m) b)) :=
      algebraMap_galRestrict_apply SourceSeedBaseValuationRing
        (h : Gal((SourceGaloisClosureField m) / GaloisBaseField)) _
    _ = (h : Gal((SourceGaloisClosureField m) / GaloisBaseField))
        (sourceGaloisSeedToClosure m (b : SourceField m)) := by rw [hcoe]
    _ = sourceGaloisSeedToClosure m (b : SourceField m) :=
      h.2 ⟨sourceGaloisSeedToClosure m (b : SourceField m), ⟨(b : SourceField m), rfl⟩⟩
    _ = algebraMap (SourceGaloisClosureIntegralClosure m)
        (SourceGaloisClosureField m)
          (algebraMap (SourceSeedIntegralClosure m)
            (SourceGaloisClosureIntegralClosure m) b) := hcoe.symm
theorem sourceSeedClosureFixingSubgroup_contraction_eq (m : ℕ)
    (P : Ideal (SourceGaloisClosureIntegralClosure m))
    (h : sourceSeedClosureFixingSubgroup m) :
    (((h : Gal((SourceGaloisClosureField m) / GaloisBaseField)) • P).under
        (SourceSeedIntegralClosure m)) =
      P.under (SourceSeedIntegralClosure m) := by
  ext b
  have hfix :
      ((h : Gal((SourceGaloisClosureField m) / GaloisBaseField))⁻¹) •
          algebraMap (SourceSeedIntegralClosure m)
            (SourceGaloisClosureIntegralClosure m) b =
        algebraMap (SourceSeedIntegralClosure m)
          (SourceGaloisClosureIntegralClosure m) b := by
    simpa only [Subgroup.coe_inv] using
      (sourceSeedClosureFixingSubgroup_smul_algebraMap m h⁻¹ b)
  rw [Ideal.mem_under, Ideal.mem_under,
    Ideal.mem_pointwise_smul_iff_inv_smul_mem, hfix]
noncomputable def sourceGaloisClosureConjugateContraction (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m))
    (g : Gal((SourceGaloisClosureField m) / GaloisBaseField)) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceSeedIntegralClosure m) := by
  let p : Ideal SourceSeedBaseValuationRing :=
    IsLocalRing.maximalIdeal SourceSeedBaseValuationRing
  let Q : Ideal (SourceGaloisClosureIntegralClosure m) := g⁻¹ • P.1
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver p := P.2.2
  letI : Q.IsPrime := by
    dsimp only [Q]
    infer_instance
  letI : Q.LiesOver p := by
    dsimp only [Q]
    exact Ideal.LiesOver.smul
      (A := SourceSeedBaseValuationRing) (P := P.1) (g := g⁻¹)
  letI : (Q.under (SourceSeedIntegralClosure m)).LiesOver p :=
    Ideal.under_liesOver_of_liesOver (SourceSeedIntegralClosure m) Q p
  exact Ideal.primesOver.mk p (Q.under (SourceSeedIntegralClosure m))
theorem sourceGaloisClosureConjugateContraction_eq_of_leftRel (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m))
    (x y : Gal((SourceGaloisClosureField m) / GaloisBaseField))
    (hxy : QuotientGroup.leftRel (sourceSeedClosureFixingSubgroup m) x y) :
    sourceGaloisClosureConjugateContraction m P x =
      sourceGaloisClosureConjugateContraction m P y := by
  let h : sourceSeedClosureFixingSubgroup m :=
    ⟨x⁻¹ * y, QuotientGroup.leftRel_apply.mp hxy⟩
  have hy : y = x * (h : Gal((SourceGaloisClosureField m) / GaloisBaseField)) := by
    simp only [h, mul_inv_cancel_left]
  apply Subtype.ext
  change (x⁻¹ • P.1).under (SourceSeedIntegralClosure m) =
    (y⁻¹ • P.1).under (SourceSeedIntegralClosure m)
  calc
    (x⁻¹ • P.1).under (SourceSeedIntegralClosure m) =
        (((h⁻¹ : sourceSeedClosureFixingSubgroup m) :
            Gal((SourceGaloisClosureField m) / GaloisBaseField)) •
          (x⁻¹ • P.1)).under (SourceSeedIntegralClosure m) :=
      (sourceSeedClosureFixingSubgroup_contraction_eq m
        (x⁻¹ • P.1) h⁻¹).symm
    _ = (y⁻¹ • P.1).under (SourceSeedIntegralClosure m) := by
      have hginv :
          (((h⁻¹ : sourceSeedClosureFixingSubgroup m) :
              Gal((SourceGaloisClosureField m) / GaloisBaseField)) * x⁻¹) = y⁻¹ := by
        rw [hy, mul_inv_rev]
        rfl
      have haction :
          (((h⁻¹ : sourceSeedClosureFixingSubgroup m) :
              Gal((SourceGaloisClosureField m) / GaloisBaseField)) •
            (x⁻¹ • P.1)) = y⁻¹ • P.1 := by
        rw [← hginv]
        ext z
        simp only [Ideal.mem_pointwise_smul_iff_inv_smul_mem,
          mul_inv_rev]
        let a : Gal((SourceGaloisClosureField m) / GaloisBaseField) := x⁻¹⁻¹
        let b : Gal((SourceGaloisClosureField m) / GaloisBaseField) :=
          (((h⁻¹ : sourceSeedClosureFixingSubgroup m) :
            Gal((SourceGaloisClosureField m) / GaloisBaseField))⁻¹)
        change a • (b • z) ∈ P.1 ↔ (a * b) • z ∈ P.1
        have hz : a • (b • z) = (a * b) • z :=
          ((sourceGaloisClosureIntegralClosureAction m).toDistribMulAction.toMulAction
            |>.mul_smul a b z).symm
        rw [hz]
      exact congrArg
        (fun I : Ideal (SourceGaloisClosureIntegralClosure m) =>
          I.under (SourceSeedIntegralClosure m)) haction
noncomputable def sourceGaloisClosureCosetContraction (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    (Gal((SourceGaloisClosureField m) / GaloisBaseField) ⧸
        sourceSeedClosureFixingSubgroup m) →
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
        (SourceSeedIntegralClosure m) :=
  Quotient.lift (sourceGaloisClosureConjugateContraction m P)
    (sourceGaloisClosureConjugateContraction_eq_of_leftRel m P)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


