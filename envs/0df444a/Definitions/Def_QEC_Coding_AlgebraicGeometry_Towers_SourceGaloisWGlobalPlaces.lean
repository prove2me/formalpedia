-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWGlobalPlaces
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWGlobalPlaces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:59:31.146595+00:00
-- url     : https://prove2.me/theorems/3809bc5d-116e-4eb6-8056-f45c35071540
-- title:
--   Source Galois WGlobal Places
-- statement:
--   Definitions and structural lemmas for Source Galois WGlobal Places, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWGlobalPlaces.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWFibres
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_mem_valuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
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
abbrev W (m : ℕ) := SourceGaloisWClosureField m
abbrev E (m : ℕ) := SourceGaloisClosureField m
noncomputable local instance (priority := 3000)
    wClosureAlgebra (m : ℕ) : Algebra (W m) (E m) :=
  (W m).val.toRingHom.toAlgebra
attribute [local instance 3000] wClosureAlgebra
noncomputable local instance (priority := 3000)
    wClosureSMul (m : ℕ) : SMul (W m) (E m) :=
  (wClosureAlgebra m).toSMul
attribute [local instance 3000] wClosureSMul
noncomputable local instance (priority := 3000)
    wClosureModule (m : ℕ) : Module (W m) (E m) :=
  @Algebra.toModule (W m) (E m) _ _ (wClosureAlgebra m)
attribute [local instance 3000] wClosureModule
noncomputable local instance (priority := 3000)
    wClosureFree (m : ℕ) : Module.Free (W m) (E m) :=
  Module.Free.of_divisionRing (W m) (E m)
attribute [local instance 3000] wClosureFree
noncomputable local instance (priority := 3000)
    wBaseFree (m : ℕ) : Module.Free GaloisBaseField (W m) :=
  Module.Free.of_divisionRing GaloisBaseField (W m)
attribute [local instance 3000] wBaseFree
noncomputable local instance (priority := 3000)
    wClosureFaithfulSMul (m : ℕ) : FaithfulSMul (W m) (E m) :=
  (faithfulSMul_iff_algebraMap_injective (W m) (E m)).2 (W m).val.injective
attribute [local instance 3000] wClosureFaithfulSMul
noncomputable local instance wClosureScalarTower (m : ℕ) :
    IsScalarTower GaloisBaseField (W m) (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] wClosureScalarTower
noncomputable local instance wClosureTorsionFree (m : ℕ) :
    Module.IsTorsionFree (W m) (E m) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (W m).val.injective
attribute [local instance] wClosureTorsionFree
noncomputable local instance wClosureFiniteDimensional (m : ℕ) :
    FiniteDimensional (W m) (E m) :=
  FiniteDimensional.right GaloisBaseField (W m) (E m)
attribute [local instance] wClosureFiniteDimensional
noncomputable local instance wClosureIsGalois (m : ℕ) :
    IsGalois (W m) (E m) :=
  IsGalois.tower_top_of_isGalois GaloisBaseField (W m) (E m)
attribute [local instance] wClosureIsGalois
abbrev O (m : ℕ) (Q : GlobalPlace F256 (W m)) := Q.valuationRing
noncomputable local instance (priority := 2000)
    oBaseModule (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    Module (O m Q) (W m) :=
  @Algebra.toModule (O m Q) (W m) _ _
    (inferInstance : Algebra (O m Q) (W m))
attribute [local instance 2000] oBaseModule
noncomputable local instance (priority := 2000)
    oBaseFaithfulSMul (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    FaithfulSMul (O m Q) (W m) :=
  (faithfulSMul_iff_algebraMap_injective (O m Q) (W m)).2
    (ValuationSubring.subtype_injective Q.valuationRing)
attribute [local instance 2000] oBaseFaithfulSMul
noncomputable local instance (priority := 2000)
    oClosureAlgebra (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    Algebra (O m Q) (E m) :=
  ((algebraMap (W m) (E m)).comp (algebraMap (O m Q) (W m))).toAlgebra
attribute [local instance 2000] oClosureAlgebra
noncomputable local instance (priority := 2000)
    oClosureSMul (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    SMul (O m Q) (E m) :=
  (oClosureAlgebra m Q).toSMul
attribute [local instance 2000] oClosureSMul
noncomputable local instance (priority := 2000)
    oClosureModule (m : ℕ) (Q : GlobalPlace F256 (W m)) :
    Module (O m Q) (E m) :=
  @Algebra.toModule (O m Q) (E m) _ _ (oClosureAlgebra m Q)
attribute [local instance 2000] oClosureModule
noncomputable local instance oBaseScalarTower (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : IsScalarTower (O m Q) (W m) (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] oBaseScalarTower
abbrev C (m : ℕ) (Q : GlobalPlace F256 (W m)) :=
  integralClosure (O m Q) (E m)
noncomputable local instance oIntegralClosureFractionTower (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : IsScalarTower (O m Q) (C m Q) (E m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] oIntegralClosureFractionTower
noncomputable local instance oIntegralClosureTorsionFree (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : Module.IsTorsionFree (O m Q) (C m Q) := by
  letI : Module.IsTorsionFree (O m Q) (E m) :=
    Module.IsTorsionFree.trans_faithfulSMul (O m Q) (W m) (E m)
  exact IsIntegralClosure.isTorsionFree (O m Q) (E m)
attribute [local instance] oIntegralClosureTorsionFree
noncomputable local instance oIntegralClosureFaithfulSMul (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : FaithfulSMul (O m Q) (C m Q) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 (by
    intro a b hab
    apply ValuationSubring.subtype_injective Q.valuationRing
    apply (W m).val.injective
    exact congrArg (fun z : C m Q => (z : E m)) hab)
attribute [local instance] oIntegralClosureFaithfulSMul
noncomputable local instance oIntegralClosureFinite (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : Module.Finite (O m Q) (C m Q) := by
  letI : IsDiscreteValuationRing (O m Q) :=
    Q.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite (O m Q) (W m) (E m) (C m Q)
attribute [local instance] oIntegralClosureFinite
noncomputable local instance oIntegralClosureIsFractionRing (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : IsFractionRing (C m Q) (E m) :=
  integralClosure.isFractionRing_of_finite_extension (W m) (E m)
attribute [local instance] oIntegralClosureIsFractionRing
noncomputable local instance oIntegralClosureIsDedekind (m : ℕ)
    (Q : GlobalPlace F256 (W m)) : IsDedekindDomain (C m Q) := by
  letI : IsDiscreteValuationRing (O m Q) :=
    Q.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain (O m Q) (W m) (E m)
attribute [local instance] oIntegralClosureIsDedekind
noncomputable def sourceGaloisWZeroUpperHeightOne (m : ℕ) (P : SourceGaloisWZeroPrime m) :
    IsDedekindDomain.HeightOneSpectrum (SourceGaloisWZeroIntegralClosure m) := by
  let O := (sourceGaloisWClosureZeroPlace m).valuationRing
  letI : IsDiscreteValuationRing O :=
    (sourceGaloisWClosureZeroPlace m).valuationRing_isDiscreteValuationRing
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver (IsLocalRing.maximalIdeal O) := P.2.2
  exact
    { asIdeal := P.1
      isPrime := P.2.1
      ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
        (IsDiscreteValuationRing.not_a_field O) P.1 }
noncomputable def sourceGaloisWInfinityUpperHeightOne (m : ℕ)
    (P : SourceGaloisWInfinityPrime m) :
    IsDedekindDomain.HeightOneSpectrum (SourceGaloisWInfinityIntegralClosure m) := by
  let O := (sourceGaloisWClosureInfinityPlace m).valuationRing
  letI : IsDiscreteValuationRing O :=
    (sourceGaloisWClosureInfinityPlace m).valuationRing_isDiscreteValuationRing
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver (IsLocalRing.maximalIdeal O) := P.2.2
  exact
    { asIdeal := P.1
      isPrime := P.2.1
      ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
        (IsDiscreteValuationRing.not_a_field O) P.1 }
@[simp]
theorem sourceGaloisWZeroUpperHeightOne_asIdeal (m : ℕ) (P : SourceGaloisWZeroPrime m) :
    (sourceGaloisWZeroUpperHeightOne m P).asIdeal = P.1 :=
  rfl
@[simp]
theorem sourceGaloisWInfinityUpperHeightOne_asIdeal (m : ℕ)
    (P : SourceGaloisWInfinityPrime m) :
    (sourceGaloisWInfinityUpperHeightOne m P).asIdeal = P.1 :=
  rfl
noncomputable def sourceGaloisWPlaceOfHeightOne (m : ℕ)
    (Q : GlobalPlace F256 (W m))
    (H : IsDedekindDomain.HeightOneSpectrum (C m Q)) :
    GlobalPlace F256 (E m) where
  valuation := H.valuation (E m)
  normalized := H.valuation_surjective (E m)
noncomputable def sourceGaloisWZeroPlaceOfPrime (m : ℕ) (P : SourceGaloisWZeroPrime m) :
    GlobalPlace F256 (SourceGaloisClosureField m) :=
  sourceGaloisWPlaceOfHeightOne m (sourceGaloisWClosureZeroPlace m)
    (sourceGaloisWZeroUpperHeightOne m P)
noncomputable def sourceGaloisWInfinityPlaceOfPrime (m : ℕ)
    (P : SourceGaloisWInfinityPrime m) : GlobalPlace F256 (SourceGaloisClosureField m) :=
  sourceGaloisWPlaceOfHeightOne m (sourceGaloisWClosureInfinityPlace m)
    (sourceGaloisWInfinityUpperHeightOne m P)
section SourceGaloisWOrderCertificate
attribute [local instance 5000]
  SubsemiringClass.toCommSemiring CommSemiring.toSemiring
  Semiring.toAddCommMonoid AddCommMonoid.toAddMonoid
  AddMonoid.toAddZeroClass AddZeroClass.toAddZero AddZero.toZero
  Zero.toOfNat0
theorem sourceGaloisWElement_ne_zero_of_order_eq_one (m : ℕ)
    (Q : GlobalPlace F256 (W m)) (x : W m) (hx : Q.order x = 1) :
    x ≠ 0 := by
  intro hzero
  have horder := hx
  rw [hzero] at horder
  simp [GlobalPlace.order] at horder
noncomputable def sourceGaloisWOrderOneElement (m : ℕ)
    (Q : GlobalPlace F256 (W m)) (x : W m) (hx : Q.order x = 1) :
    Q.valuationRing :=
  ⟨x, (Q.regularAt_iff_mem_valuationRing x).mp
    ((Q.regularAt_iff_order_nonnegative
      (sourceGaloisWElement_ne_zero_of_order_eq_one m Q x hx)).mpr (by omega))⟩
end SourceGaloisWOrderCertificate
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


