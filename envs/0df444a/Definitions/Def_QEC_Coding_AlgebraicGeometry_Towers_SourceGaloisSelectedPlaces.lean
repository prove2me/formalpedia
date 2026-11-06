-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:51:23.916401+00:00
-- url     : https://prove2.me/theorems/118f9618-0fab-4db3-96e2-fdbf452108b5
-- title:
--   Source Galois Selected Places
-- statement:
--   Definitions and structural lemmas for Source Galois Selected Places, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSelectedPlaces.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisFunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosureSplitting
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosure_inertiaDeg_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosure_primesOver_ncard_eq_finrank
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
noncomputable local instance (priority := 2000)
    galoisSelectedBaseValuationRingBaseModule :
    Module SourceSeedBaseValuationRing GaloisBaseField :=
  @Algebra.toModule SourceSeedBaseValuationRing GaloisBaseField _ _
    (inferInstance : Algebra SourceSeedBaseValuationRing GaloisBaseField)
attribute [local instance 2000] galoisSelectedBaseValuationRingBaseModule
noncomputable local instance (priority := 2000)
    galoisSelectedBaseValuationRingBaseFaithfulSMul :
    FaithfulSMul SourceSeedBaseValuationRing GaloisBaseField :=
  (faithfulSMul_iff_algebraMap_injective
    SourceSeedBaseValuationRing GaloisBaseField).2
      (ValuationSubring.subtype_injective
        sourceSeedFixedBaseOnePlace.valuationRing)
attribute [local instance 2000] galoisSelectedBaseValuationRingBaseFaithfulSMul
noncomputable local instance (priority := 2000)
    galoisSelectedBaseValuationRingAlgebra (m : ℕ) :
    Algebra SourceSeedBaseValuationRing (SourceGaloisClosureField m) :=
  ((algebraMap GaloisBaseField (SourceGaloisClosureField m)).comp
    (algebraMap SourceSeedBaseValuationRing GaloisBaseField)).toAlgebra
attribute [local instance 2000] galoisSelectedBaseValuationRingAlgebra
noncomputable local instance (priority := 2000)
    galoisSelectedBaseValuationRingSMul (m : ℕ) :
    SMul SourceSeedBaseValuationRing (SourceGaloisClosureField m) :=
  (galoisSelectedBaseValuationRingAlgebra m).toSMul
attribute [local instance 2000] galoisSelectedBaseValuationRingSMul
noncomputable local instance (priority := 2000)
    galoisSelectedBaseValuationRingModule (m : ℕ) :
    Module SourceSeedBaseValuationRing (SourceGaloisClosureField m) :=
  @Algebra.toModule SourceSeedBaseValuationRing (SourceGaloisClosureField m) _ _
    (galoisSelectedBaseValuationRingAlgebra m)
attribute [local instance 2000] galoisSelectedBaseValuationRingModule
noncomputable local instance galoisSelectedBaseScalarTower (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing GaloisBaseField
      (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] galoisSelectedBaseScalarTower
noncomputable local instance
    galoisSelectedIntegralClosureFractionTower (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) (SourceGaloisClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] galoisSelectedIntegralClosureFractionTower
noncomputable local instance
    galoisSelectedIntegralClosureTorsionFree (m : ℕ) :
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
attribute [local instance] galoisSelectedIntegralClosureTorsionFree
noncomputable local instance galoisSelectedIntegralClosureFinite
    (m : ℕ) :
    Module.Finite SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite SourceSeedBaseValuationRing
    GaloisBaseField (SourceGaloisClosureField m)
      (SourceGaloisClosureIntegralClosure m)
attribute [local instance] galoisSelectedIntegralClosureFinite
noncomputable local instance
    galoisSelectedIntegralClosureIsFractionRing (m : ℕ) :
    IsFractionRing (SourceGaloisClosureIntegralClosure m)
      (SourceGaloisClosureField m) :=
  integralClosure.isFractionRing_of_finite_extension
    GaloisBaseField (SourceGaloisClosureField m)
attribute [local instance] galoisSelectedIntegralClosureIsFractionRing
noncomputable local instance galoisSelectedIntegralClosureIsDedekind
    (m : ℕ) : IsDedekindDomain (SourceGaloisClosureIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain SourceSeedBaseValuationRing
    GaloisBaseField (SourceGaloisClosureField m)
attribute [local instance] galoisSelectedIntegralClosureIsDedekind
noncomputable def sourceSeedBaseOneValuationRingEquiv :
    SourceSeedBaseValuationRing ≃+*
      (baseRationalPlace (1 : BasePoint)).place.valuationRing where
  toFun x := ⟨galoisBaseFieldEquivRatFunc.symm x, by
    rw [GlobalPlace.mem_valuationRing_iff]
    exact (GlobalPlace.mem_valuationRing_iff
      sourceSeedFixedBaseOnePlace x).mp x.property⟩
  invFun x := ⟨galoisBaseFieldEquivRatFunc x, by
    rw [GlobalPlace.mem_valuationRing_iff]
    change (baseRationalPlace (1 : BasePoint)).place.valuation
      (galoisBaseFieldEquivRatFunc.symm
        (galoisBaseFieldEquivRatFunc x)) ≤ 1
    rw [galoisBaseFieldEquivRatFunc.symm_apply_apply]
    exact (GlobalPlace.mem_valuationRing_iff
      (baseRationalPlace (1 : BasePoint)).place x).mp x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact galoisBaseFieldEquivRatFunc.apply_symm_apply x
  right_inv x := by
    apply Subtype.ext
    exact galoisBaseFieldEquivRatFunc.symm_apply_apply x
  map_mul' _ _ := by
    apply Subtype.ext
    exact map_mul _ _ _
  map_add' _ _ := by
    apply Subtype.ext
    exact map_add _ _ _
instance sourceSeedBaseOneValuationRingEquiv_isLocalHom :
    IsLocalHom sourceSeedBaseOneValuationRingEquiv.toRingHom :=
  ⟨fun x hx => by
    simpa using hx.map sourceSeedBaseOneValuationRingEquiv.symm.toRingHom⟩
noncomputable def sourceSeedBaseOneResidueEquiv :
    GlobalPlace.residueField sourceSeedFixedBaseOnePlace ≃+*
      GlobalPlace.residueField (baseRationalPlace (1 : BasePoint)).place :=
  IsLocalRing.ResidueField.mapEquiv sourceSeedBaseOneValuationRingEquiv
theorem sourceSeedBaseOneResidueEquiv_residue
    (z : SourceSeedBaseValuationRing) :
    sourceSeedBaseOneResidueEquiv
        (GlobalPlace.residue sourceSeedFixedBaseOnePlace z) =
      GlobalPlace.residue (baseRationalPlace (1 : BasePoint)).place
        (sourceSeedBaseOneValuationRingEquiv z) := by
  unfold sourceSeedBaseOneResidueEquiv
  exact IsLocalRing.ResidueField.map_residue
    sourceSeedBaseOneValuationRingEquiv.toRingHom z
theorem sourceSeedBaseOneResidueEquiv_constants (a : F256) :
    sourceSeedBaseOneResidueEquiv
        (GlobalPlace.constantsToResidue sourceSeedFixedBaseOnePlace a) =
      GlobalPlace.constantsToResidue
        (baseRationalPlace (1 : BasePoint)).place a := by
  rw [show GlobalPlace.constantsToResidue sourceSeedFixedBaseOnePlace a =
      GlobalPlace.residue sourceSeedFixedBaseOnePlace
        (GlobalPlace.constantsToValuationRing
          sourceSeedFixedBaseOnePlace a) from rfl,
    sourceSeedBaseOneResidueEquiv_residue]
  apply congrArg
    (GlobalPlace.residue (baseRationalPlace (1 : BasePoint)).place)
  apply Subtype.ext
  exact galoisBaseFieldEquivRatFunc.symm.commutes a
noncomputable def sourceSeedFixedBaseOneRationalPlace :
    RationalPlace F256 GaloisBaseField where
  place := sourceSeedFixedBaseOnePlace
  constantsEquiv :=
    (baseRationalPlace (1 : BasePoint)).constantsEquiv.trans
      sourceSeedBaseOneResidueEquiv.symm
  constantsEquiv_apply a := by
    change sourceSeedBaseOneResidueEquiv.symm
        ((baseRationalPlace (1 : BasePoint)).constantsEquiv a) =
      GlobalPlace.constantsToResidue sourceSeedFixedBaseOnePlace a
    apply sourceSeedBaseOneResidueEquiv.injective
    rw [sourceSeedBaseOneResidueEquiv.apply_symm_apply,
      (baseRationalPlace (1 : BasePoint)).constantsEquiv_apply,
      sourceSeedBaseOneResidueEquiv_constants]
noncomputable def sourceGaloisClosureUpperHeightOne (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    IsDedekindDomain.HeightOneSpectrum (SourceGaloisClosureIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  letI : P.1.IsPrime := P.2.1
  letI : P.1.LiesOver
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing) := P.2.2
  exact
    { asIdeal := P.1
      isPrime := P.2.1
      ne_bot := Ideal.ne_bot_of_liesOver_of_ne_bot
        (IsDiscreteValuationRing.not_a_field SourceSeedBaseValuationRing) P.1 }
@[simp]
theorem sourceGaloisClosureUpperHeightOne_asIdeal (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    (sourceGaloisClosureUpperHeightOne m P).asIdeal = P.1 :=
  rfl
noncomputable def sourceGaloisClosurePlaceOfPrime (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    GlobalPlace F256 (SourceGaloisClosureField m) where
  valuation := (sourceGaloisClosureUpperHeightOne m P).valuation
    (SourceGaloisClosureField m)
  normalized := (sourceGaloisClosureUpperHeightOne m P).valuation_surjective
    (SourceGaloisClosureField m)
noncomputable def sourceGaloisClosureQuotientConstantsEquiv (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    F256 ≃+* HasQuotient.Quotient (SourceGaloisClosureIntegralClosure m)
      (P : Ideal (SourceGaloisClosureIntegralClosure m)) := by
  let O := SourceSeedBaseValuationRing
  let C := SourceGaloisClosureIntegralClosure m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  let R : Ideal C := P.1
  letI : IsDiscreteValuationRing O :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  letI : p.IsMaximal := by
    dsimp [p]
    infer_instance
  letI : R.IsMaximal := by
    dsimp [R]
    exact P.2.1.isMaximal
      (Ideal.ne_bot_of_mem_primesOver
        (IsDiscreteValuationRing.not_a_field O) P.2)
  letI : R.LiesOver p := P.2.2
  letI : _root_.Field (O ⧸ p) := Ideal.Quotient.field p
  letI : _root_.Field (C ⧸ R) := Ideal.Quotient.field R
  let quotientAlgebra : Algebra (O ⧸ p) (C ⧸ R) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def R p).le
  letI : Algebra (O ⧸ p) (C ⧸ R) := quotientAlgebra
  letI : SMul (O ⧸ p) (C ⧸ R) := quotientAlgebra.toSMul
  letI : Module (O ⧸ p) (C ⧸ R) :=
    @Algebra.toModule (O ⧸ p) (C ⧸ R) _ _ quotientAlgebra
  letI : Module.Free (O ⧸ p) (C ⧸ R) :=
    Module.Free.of_divisionRing (O ⧸ p) (C ⧸ R)
  have hfinrank : Module.finrank (O ⧸ p) (C ⧸ R) = 1 := by
    rw [← Ideal.inertiaDeg_algebraMap]
    exact sourceGaloisClosure_inertiaDeg_eq_one m P
  let e : (O ⧸ p) ≃+* (C ⧸ R) :=
    RingEquiv.ofBijective (algebraMap (O ⧸ p) (C ⧸ R))
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinrank)
  exact sourceSeedFixedBaseOneRationalPlace.constantsEquiv.trans e
noncomputable def sourceGaloisClosureQuotientResidueEquiv (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    HasQuotient.Quotient (SourceGaloisClosureIntegralClosure m)
        (P : Ideal (SourceGaloisClosureIntegralClosure m)) ≃+*
      GlobalPlace.residueField (sourceGaloisClosurePlaceOfPrime m P) := by
  let C := SourceGaloisClosureIntegralClosure m
  let E := SourceGaloisClosureField m
  let H := sourceGaloisClosureUpperHeightOne m P
  letI : IsFractionRing C E :=
    galoisSelectedIntegralClosureIsFractionRing m
  letI : H.asIdeal.IsMaximal := inferInstance
  letI : Algebra C (H.valuationSubringAtPrime E) :=
    IsDedekindDomain.HeightOneSpectrum.instAlgebraSubtypeMemValuationSubringValuationSubringAtPrime H
  letI : IsLocalization H.asIdeal.primeCompl
      (H.valuationSubringAtPrime E) :=
    IsDedekindDomain.HeightOneSpectrum.instIsLocalizationPrimeComplAsIdealSubtypeMemValuationSubringValuationSubringAtPrime H
  let e₁ : (C ⧸ H.asIdeal) ≃+*
      IsLocalRing.ResidueField (H.valuationSubringAtPrime E) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal H.asIdeal
      (H.valuationSubringAtPrime E)
  let e₂ : H.valuationSubringAtPrime E ≃+*
      (H.valuation E).valuationSubring := by
    rw [H.valuationSubringAtPrime_eq_valuationSubring]
  exact e₁.trans (IsLocalRing.ResidueField.mapEquiv e₂)
noncomputable def sourceGaloisClosureAbstractResidueEquiv (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    F256 ≃+* GlobalPlace.residueField (sourceGaloisClosurePlaceOfPrime m P) :=
  (sourceGaloisClosureQuotientConstantsEquiv m P).trans
    (sourceGaloisClosureQuotientResidueEquiv m P)
theorem sourceGaloisClosureConstantsToResidue_bijective (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    Function.Bijective
      (GlobalPlace.constantsToResidue (sourceGaloisClosurePlaceOfPrime m P)) := by
  let e := sourceGaloisClosureAbstractResidueEquiv m P
  letI : Finite
      (GlobalPlace.residueField (sourceGaloisClosurePlaceOfPrime m P)) :=
    Finite.of_equiv F256 e.toEquiv
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨(GlobalPlace.constantsToResidue
    (sourceGaloisClosurePlaceOfPrime m P)).injective, ?_⟩
  exact Nat.card_congr e.toEquiv
noncomputable def sourceGaloisClosureRationalPlaceOfPrime (m : ℕ)
    (P : (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)) :
    RationalPlace F256 (SourceGaloisClosureField m) where
  place := sourceGaloisClosurePlaceOfPrime m P
  constantsEquiv := RingEquiv.ofBijective
    (GlobalPlace.constantsToResidue (sourceGaloisClosurePlaceOfPrime m P))
    (sourceGaloisClosureConstantsToResidue_bijective m P)
  constantsEquiv_apply _ := rfl
def sourceGaloisClosureSelectedLength (m : ℕ) : ℕ :=
  Module.finrank GaloisBaseField (SourceGaloisClosureField m)
noncomputable def sourceGaloisClosureSelectedPrimeEquiv (m : ℕ) :
    Fin (sourceGaloisClosureSelectedLength m) ≃
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
        (SourceGaloisClosureIntegralClosure m) := by
  let S := (IsLocalRing.maximalIdeal
    SourceSeedBaseValuationRing).primesOver
      (SourceGaloisClosureIntegralClosure m)
  letI : Fintype S :=
    (IsDedekindDomain.primesOver_finite
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing)
      (SourceGaloisClosureIntegralClosure m)).fintype
  have hcard : Fintype.card S = sourceGaloisClosureSelectedLength m := by
    calc
      Fintype.card S = Nat.card S := Fintype.card_eq_nat_card
      _ = S.ncard := Nat.card_coe_set_eq _
      _ = Module.finrank GaloisBaseField (SourceGaloisClosureField m) :=
        sourceGaloisClosure_primesOver_ncard_eq_finrank m
      _ = sourceGaloisClosureSelectedLength m := rfl
  exact (finCongr hcard.symm).trans (Fintype.equivFin S).symm
noncomputable def sourceGaloisClosureSelectedRationalPlace (m : ℕ)
    (j : Fin (sourceGaloisClosureSelectedLength m)) :
    RationalPlace F256 (SourceGaloisClosureField m) :=
  sourceGaloisClosureRationalPlaceOfPrime m
    (sourceGaloisClosureSelectedPrimeEquiv m j)
noncomputable def sourceGaloisClosureSelectedPlaces (m : ℕ) :
    Finset (GlobalPlace F256 (SourceGaloisClosureField m)) := by
  classical
  exact Finset.univ.image fun j : Fin (sourceGaloisClosureSelectedLength m) =>
    (sourceGaloisClosureSelectedRationalPlace m j).place
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


