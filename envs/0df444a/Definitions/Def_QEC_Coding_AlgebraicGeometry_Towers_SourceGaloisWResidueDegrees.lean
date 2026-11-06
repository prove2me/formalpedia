-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWResidueDegrees
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWResidueDegrees
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T04:59:31.819764+00:00
-- url     : https://prove2.me/theorems/d7fede67-61df-488c-958b-e1ae99efd8aa
-- title:
--   Source Galois WResidue Degrees
-- statement:
--   Definitions and structural lemmas for Source Galois WResidue Degrees, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWResidueDegrees.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWGlobalPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneQuotientResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinityResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ResidueFinrankInertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceGaloisWFieldGenerator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldEquivRatFunc_X
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalInfinity_constantsToResidue_surjective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuationRing_isDiscreteValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceGaloisWFieldGenerator
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFieldEquivRatFunc_X
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
abbrev sourceGaloisWResidueDegrees_W (m : ℕ) := SourceGaloisWClosureField m
abbrev sourceGaloisWResidueDegrees_E (m : ℕ) := SourceGaloisClosureField m
noncomputable local instance (priority := 3000)
    sourceGaloisWResidueDegrees_wClosureAlgebra (m : ℕ) : Algebra (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m) :=
  (sourceGaloisWResidueDegrees_W m).val.toRingHom.toAlgebra
attribute [local instance 3000] sourceGaloisWResidueDegrees_wClosureAlgebra
noncomputable local instance (priority := 3000)
    sourceGaloisWResidueDegrees_wClosureSMul (m : ℕ) : SMul (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m) :=
  (sourceGaloisWResidueDegrees_wClosureAlgebra m).toSMul
attribute [local instance 3000] sourceGaloisWResidueDegrees_wClosureSMul
noncomputable local instance (priority := 3000)
    sourceGaloisWResidueDegrees_wClosureModule (m : ℕ) : Module (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m) :=
  @Algebra.toModule (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m) _ _ (sourceGaloisWResidueDegrees_wClosureAlgebra m)
attribute [local instance 3000] sourceGaloisWResidueDegrees_wClosureModule
noncomputable local instance (priority := 3000)
    sourceGaloisWResidueDegrees_wClosureFree (m : ℕ) : Module.Free (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m) :=
  Module.Free.of_divisionRing (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m)
attribute [local instance 3000] sourceGaloisWResidueDegrees_wClosureFree
noncomputable local instance (priority := 3000)
    sourceGaloisWResidueDegrees_wBaseFree (m : ℕ) : Module.Free GaloisBaseField (sourceGaloisWResidueDegrees_W m) :=
  Module.Free.of_divisionRing GaloisBaseField (sourceGaloisWResidueDegrees_W m)
attribute [local instance 3000] sourceGaloisWResidueDegrees_wBaseFree
noncomputable local instance (priority := 3000)
    sourceGaloisWResidueDegrees_wClosureFaithfulSMul (m : ℕ) : FaithfulSMul (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m) :=
  (faithfulSMul_iff_algebraMap_injective (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m)).2 (sourceGaloisWResidueDegrees_W m).val.injective
attribute [local instance 3000] sourceGaloisWResidueDegrees_wClosureFaithfulSMul
noncomputable local instance sourceGaloisWResidueDegrees_wClosureScalarTower (m : ℕ) :
    IsScalarTower GaloisBaseField (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisWResidueDegrees_wClosureScalarTower
noncomputable local instance sourceGaloisWResidueDegrees_wClosureTorsionFree (m : ℕ) :
    Module.IsTorsionFree (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (sourceGaloisWResidueDegrees_W m).val.injective
attribute [local instance] sourceGaloisWResidueDegrees_wClosureTorsionFree
noncomputable local instance sourceGaloisWResidueDegrees_wClosureFiniteDimensional (m : ℕ) :
    FiniteDimensional (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m) :=
  FiniteDimensional.right GaloisBaseField (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m)
attribute [local instance] sourceGaloisWResidueDegrees_wClosureFiniteDimensional
noncomputable local instance sourceGaloisWResidueDegrees_wClosureIsGalois (m : ℕ) :
    IsGalois (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m) :=
  IsGalois.tower_top_of_isGalois GaloisBaseField (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m)
attribute [local instance] sourceGaloisWResidueDegrees_wClosureIsGalois
noncomputable local instance sourceGaloisWResidueDegrees_closurePolynomialAlgebra (m : ℕ) :
    Algebra (Polynomial F256) (sourceGaloisWResidueDegrees_E m) :=
  ((algebraMap (RatFunc F256) (sourceGaloisWResidueDegrees_E m)).comp
    (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra
attribute [local instance] sourceGaloisWResidueDegrees_closurePolynomialAlgebra
noncomputable local instance sourceGaloisWResidueDegrees_closurePolynomialRatFuncScalarTower (m : ℕ) :
    IsScalarTower (Polynomial F256) (RatFunc F256) (sourceGaloisWResidueDegrees_E m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisWResidueDegrees_closurePolynomialRatFuncScalarTower
noncomputable local instance sourceGaloisWResidueDegrees_closureRatFuncIsSeparable (m : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (sourceGaloisWResidueDegrees_E m) :=
  IsGalois.to_isSeparable
attribute [local instance] sourceGaloisWResidueDegrees_closureRatFuncIsSeparable
abbrev sourceGaloisWResidueDegrees_O (m : ℕ) (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) := Q.valuationRing
noncomputable local instance (priority := 2000)
    sourceGaloisWResidueDegrees_oBaseModule (m : ℕ) (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) :
    Module (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_W m) :=
  @Algebra.toModule (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_W m) _ _
    (inferInstance : Algebra (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_W m))
attribute [local instance 2000] sourceGaloisWResidueDegrees_oBaseModule
noncomputable local instance (priority := 2000)
    sourceGaloisWResidueDegrees_oBaseFaithfulSMul (m : ℕ) (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) :
    FaithfulSMul (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_W m) :=
  (faithfulSMul_iff_algebraMap_injective (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_W m)).2
    (ValuationSubring.subtype_injective Q.valuationRing)
attribute [local instance 2000] sourceGaloisWResidueDegrees_oBaseFaithfulSMul
noncomputable local instance (priority := 2000)
    sourceGaloisWResidueDegrees_oClosureAlgebra (m : ℕ) (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) :
    Algebra (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_E m) :=
  ((algebraMap (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m)).comp (algebraMap (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_W m))).toAlgebra
attribute [local instance 2000] sourceGaloisWResidueDegrees_oClosureAlgebra
noncomputable local instance (priority := 2000)
    sourceGaloisWResidueDegrees_oClosureSMul (m : ℕ) (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) :
    SMul (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_E m) :=
  (sourceGaloisWResidueDegrees_oClosureAlgebra m Q).toSMul
attribute [local instance 2000] sourceGaloisWResidueDegrees_oClosureSMul
noncomputable local instance (priority := 2000)
    sourceGaloisWResidueDegrees_oClosureModule (m : ℕ) (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) :
    Module (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_E m) :=
  @Algebra.toModule (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_E m) _ _ (sourceGaloisWResidueDegrees_oClosureAlgebra m Q)
attribute [local instance 2000] sourceGaloisWResidueDegrees_oClosureModule
noncomputable local instance sourceGaloisWResidueDegrees_oBaseScalarTower (m : ℕ)
    (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) : IsScalarTower (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisWResidueDegrees_oBaseScalarTower
abbrev sourceGaloisWResidueDegrees_C (m : ℕ) (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) :=
  integralClosure (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_E m)
noncomputable local instance sourceGaloisWResidueDegrees_oIntegralClosureFractionTower (m : ℕ)
    (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) : IsScalarTower (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_C m Q) (sourceGaloisWResidueDegrees_E m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisWResidueDegrees_oIntegralClosureFractionTower
noncomputable local instance sourceGaloisWResidueDegrees_oIntegralClosureTorsionFree (m : ℕ)
    (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) : Module.IsTorsionFree (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_C m Q) := by
  letI : Module.IsTorsionFree (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_E m) :=
    Module.IsTorsionFree.trans_faithfulSMul (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m)
  exact IsIntegralClosure.isTorsionFree (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_E m)
attribute [local instance] sourceGaloisWResidueDegrees_oIntegralClosureTorsionFree
noncomputable local instance sourceGaloisWResidueDegrees_oIntegralClosureFinite (m : ℕ)
    (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) : Module.Finite (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_C m Q) := by
  letI : IsDiscreteValuationRing (sourceGaloisWResidueDegrees_O m Q) :=
    Q.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m) (sourceGaloisWResidueDegrees_C m Q)
attribute [local instance] sourceGaloisWResidueDegrees_oIntegralClosureFinite
noncomputable local instance sourceGaloisWResidueDegrees_oIntegralClosureIsFractionRing (m : ℕ)
    (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) : IsFractionRing (sourceGaloisWResidueDegrees_C m Q) (sourceGaloisWResidueDegrees_E m) :=
  integralClosure.isFractionRing_of_finite_extension (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m)
attribute [local instance] sourceGaloisWResidueDegrees_oIntegralClosureIsFractionRing
noncomputable local instance sourceGaloisWResidueDegrees_oIntegralClosureIsDedekind (m : ℕ)
    (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) : IsDedekindDomain (sourceGaloisWResidueDegrees_C m Q) := by
  letI : IsDiscreteValuationRing (sourceGaloisWResidueDegrees_O m Q) :=
    Q.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m)
attribute [local instance] sourceGaloisWResidueDegrees_oIntegralClosureIsDedekind
noncomputable local instance sourceGaloisWResidueDegrees_wRelativeGalFinite (m : ℕ) :
    Finite Gal((sourceGaloisWResidueDegrees_E m) / (sourceGaloisWResidueDegrees_W m)) :=
  Fintype.finite (AlgEquiv.fintype (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m))
attribute [local instance] sourceGaloisWResidueDegrees_wRelativeGalFinite
noncomputable local instance sourceGaloisWResidueDegrees_oIntegralClosureAction (m : ℕ)
    (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) :
    MulSemiringAction Gal((sourceGaloisWResidueDegrees_E m) / (sourceGaloisWResidueDegrees_W m)) (sourceGaloisWResidueDegrees_C m Q) :=
  IsIntegralClosure.MulSemiringAction (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m) (sourceGaloisWResidueDegrees_C m Q)
attribute [local instance] sourceGaloisWResidueDegrees_oIntegralClosureAction
noncomputable local instance sourceGaloisWResidueDegrees_oIntegralClosureIsGaloisGroup (m : ℕ)
    (Q : GlobalPlace F256 (sourceGaloisWResidueDegrees_W m)) :
    IsGaloisGroup Gal((sourceGaloisWResidueDegrees_E m) / (sourceGaloisWResidueDegrees_W m)) (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_C m Q) :=
  IsGaloisGroup.of_isFractionRing Gal((sourceGaloisWResidueDegrees_E m) / (sourceGaloisWResidueDegrees_W m))
    (sourceGaloisWResidueDegrees_O m Q) (sourceGaloisWResidueDegrees_C m Q) (sourceGaloisWResidueDegrees_W m) (sourceGaloisWResidueDegrees_E m)
attribute [local instance] sourceGaloisWResidueDegrees_oIntegralClosureIsGaloisGroup
noncomputable def sourceGaloisWResidueDegrees_comapValuationRingEquiv
    {k K L : Type*} [_root_.Field k] [Finite k] [_root_.Field K] [Algebra k K]
    [_root_.Field L] [Algebra k L] (e : K ≃ₐ[k] L) (Q : GlobalPlace k L) :
    (GlobalPlace.comapAlgEquiv e Q).valuationRing ≃+* Q.valuationRing where
  toFun x := ⟨e x, x.property⟩
  invFun x := ⟨e.symm x, by
    change Q.valuation (e (e.symm x)) ≤ 1
    rw [e.apply_symm_apply]
    exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    exact e.apply_symm_apply x
  map_mul' _ _ := by
    apply Subtype.ext
    exact map_mul e _ _
  map_add' _ _ := by
    apply Subtype.ext
    exact map_add e _ _
instance sourceGaloisWResidueDegrees_comapValuationRingEquiv_isLocalHom
    {k K L : Type*} [_root_.Field k] [Finite k] [_root_.Field K] [Algebra k K]
    [_root_.Field L] [Algebra k L] (e : K ≃ₐ[k] L) (Q : GlobalPlace k L) :
    IsLocalHom (sourceGaloisWResidueDegrees_comapValuationRingEquiv e Q).toRingHom :=
  ⟨fun x hx => by
    simpa using hx.map (sourceGaloisWResidueDegrees_comapValuationRingEquiv e Q).symm.toRingHom⟩
noncomputable def sourceGaloisWResidueDegrees_comapResidueEquiv
    {k K L : Type*} [_root_.Field k] [Finite k] [_root_.Field K] [Algebra k K]
    [_root_.Field L] [Algebra k L] (e : K ≃ₐ[k] L) (Q : GlobalPlace k L) :
    GlobalPlace.residueField (GlobalPlace.comapAlgEquiv e Q) ≃+*
      GlobalPlace.residueField Q :=
  IsLocalRing.ResidueField.mapEquiv (sourceGaloisWResidueDegrees_comapValuationRingEquiv e Q)
theorem sourceGaloisWResidueDegrees_comapResidueEquiv_residue
    {k K L : Type*} [_root_.Field k] [Finite k] [_root_.Field K] [Algebra k K]
    [_root_.Field L] [Algebra k L] (e : K ≃ₐ[k] L) (Q : GlobalPlace k L)
    (z : (GlobalPlace.comapAlgEquiv e Q).valuationRing) :
    sourceGaloisWResidueDegrees_comapResidueEquiv e Q ((GlobalPlace.comapAlgEquiv e Q).residue z) =
      Q.residue (sourceGaloisWResidueDegrees_comapValuationRingEquiv e Q z) := by
  unfold sourceGaloisWResidueDegrees_comapResidueEquiv
  exact IsLocalRing.ResidueField.map_residue
    (sourceGaloisWResidueDegrees_comapValuationRingEquiv e Q).toRingHom z
theorem sourceGaloisWResidueDegrees_comapResidueEquiv_constants
    {k K L : Type*} [_root_.Field k] [Finite k] [_root_.Field K] [Algebra k K]
    [_root_.Field L] [Algebra k L] (e : K ≃ₐ[k] L) (Q : GlobalPlace k L)
    (a : k) :
    sourceGaloisWResidueDegrees_comapResidueEquiv e Q
        (GlobalPlace.constantsToResidue (GlobalPlace.comapAlgEquiv e Q) a) =
      GlobalPlace.constantsToResidue Q a := by
  change sourceGaloisWResidueDegrees_comapResidueEquiv e Q
      ((GlobalPlace.comapAlgEquiv e Q).residue
        (GlobalPlace.constantsToValuationRing
          (GlobalPlace.comapAlgEquiv e Q) a)) =
    Q.residue (GlobalPlace.constantsToValuationRing Q a)
  rw [sourceGaloisWResidueDegrees_comapResidueEquiv_residue]
  apply congrArg Q.residue
  apply Subtype.ext
  exact e.commutes a
noncomputable def sourceGaloisWResidueDegrees_rationalPlaceComapAlgEquiv
    {k K L : Type*} [_root_.Field k] [Finite k] [_root_.Field K] [Algebra k K]
    [_root_.Field L] [Algebra k L] (e : K ≃ₐ[k] L)
    (Q : RationalPlace k L) : RationalPlace k K where
  place := GlobalPlace.comapAlgEquiv e Q.place
  constantsEquiv := Q.constantsEquiv.trans (sourceGaloisWResidueDegrees_comapResidueEquiv e Q.place).symm
  constantsEquiv_apply a := by
    apply (sourceGaloisWResidueDegrees_comapResidueEquiv e Q.place).injective
    change sourceGaloisWResidueDegrees_comapResidueEquiv e Q.place
        ((sourceGaloisWResidueDegrees_comapResidueEquiv e Q.place).symm (Q.constantsEquiv a)) = _
    rw [RingEquiv.apply_symm_apply, Q.constantsEquiv_apply,
      sourceGaloisWResidueDegrees_comapResidueEquiv_constants]
noncomputable def sourceGaloisWResidueDegrees_rationalInfinityRationalPlace :
    RationalPlace F256 (RatFunc F256) where
  place := GlobalPlace.rationalInfinity F256
  constantsEquiv := RingEquiv.ofBijective
    (GlobalPlace.constantsToResidue (GlobalPlace.rationalInfinity F256))
    ⟨RingHom.injective _,
      GlobalPlace.rationalInfinity_constantsToResidue_surjective⟩
  constantsEquiv_apply _ := rfl
noncomputable local instance sourceGaloisWResidueDegrees_sourceGaloisWFieldConstantTower :
    IsScalarTower F256 GaloisBaseField SourceGaloisWField :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisWResidueDegrees_sourceGaloisWFieldConstantTower
noncomputable local instance sourceGaloisWResidueDegrees_sourceGaloisWClosureFieldConstantTower (m : ℕ) :
    IsScalarTower F256 GaloisBaseField (sourceGaloisWResidueDegrees_W m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisWResidueDegrees_sourceGaloisWClosureFieldConstantTower
noncomputable def sourceGaloisWResidueDegrees_wFieldEquivClosureOverF256 (m : ℕ) :
    SourceGaloisWField ≃ₐ[F256] sourceGaloisWResidueDegrees_W m :=
  (sourceGaloisWFieldEquivClosureField m).restrictScalars F256
noncomputable def sourceGaloisWResidueDegrees_sourceGaloisWClosureZeroRationalPlace (m : ℕ) :
    RationalPlace F256 (sourceGaloisWResidueDegrees_W m) :=
  sourceGaloisWResidueDegrees_rationalPlaceComapAlgEquiv (sourceGaloisWResidueDegrees_wFieldEquivClosureOverF256 m).symm
    (sourceGaloisWResidueDegrees_rationalPlaceComapAlgEquiv sourceGaloisWFieldEquivRatFunc.symm
      zeroBaseRationalPlace)
noncomputable def sourceGaloisWResidueDegrees_sourceGaloisWClosureInfinityRationalPlace (m : ℕ) :
    RationalPlace F256 (sourceGaloisWResidueDegrees_W m) :=
  sourceGaloisWResidueDegrees_rationalPlaceComapAlgEquiv (sourceGaloisWResidueDegrees_wFieldEquivClosureOverF256 m).symm
    (sourceGaloisWResidueDegrees_rationalPlaceComapAlgEquiv sourceGaloisWFieldEquivRatFunc.symm
      sourceGaloisWResidueDegrees_rationalInfinityRationalPlace)
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


