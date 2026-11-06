-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedDivisor
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedDivisor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:21:56.678735+00:00
-- url     : https://prove2.me/theorems/b5ddc59a-65ac-4cea-a7f2-c5fce183c297
-- title:
--   Source Galois Selected Divisor
-- statement:
--   Definitions and structural lemmas for Source Galois Selected Divisor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisSelectedDivisor.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_FinitePlaceDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_baseRationalPlace_order_algebraMap_polynomial
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceGaloisWFieldGenerator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedPlaces_card
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureGeneratorPoleDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWFieldEquivRatFunc_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityFibreDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityPlaceOfPrime_order_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityPrime_nonempty
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityRamificationIndex_pos
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroFibreDivisor_apply
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finitePlaceDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_algebraMap
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWClosureGeneratorPoleDivisor_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWFieldEquivRatFunc_X
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWInfinityFibreDivisor_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWZeroFibreDivisor_apply
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.finitePlaceDivisor_apply
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
open IntermediateField
open scoped BigOperators Polynomial RatFunc
noncomputable section
abbrev sourceGaloisSelectedDivisor_E (m : ℕ) := SourceGaloisClosureField m
noncomputable local instance sourceGaloisSelectedDivisor_closurePolynomialAlgebra (m : ℕ) :
    Algebra (Polynomial F256) (sourceGaloisSelectedDivisor_E m) :=
  ((algebraMap (RatFunc F256) (sourceGaloisSelectedDivisor_E m)).comp
    (algebraMap (Polynomial F256) (RatFunc F256))).toAlgebra
attribute [local instance] sourceGaloisSelectedDivisor_closurePolynomialAlgebra
noncomputable local instance sourceGaloisSelectedDivisor_closurePolynomialRatFuncScalarTower
    (m : ℕ) : IsScalarTower (Polynomial F256) (RatFunc F256) (sourceGaloisSelectedDivisor_E m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisSelectedDivisor_closurePolynomialRatFuncScalarTower
noncomputable local instance sourceGaloisSelectedDivisor_closureRatFuncIsSeparable (m : ℕ) :
    Algebra.IsSeparable (RatFunc F256) (sourceGaloisSelectedDivisor_E m) :=
  IsGalois.to_isSeparable
attribute [local instance] sourceGaloisSelectedDivisor_closureRatFuncIsSeparable
theorem sourceGaloisSelectedDivisor_sourceGaloisClosureSelectedPlaceAt_injective (m : ℕ) :
    Function.Injective (fun j : Fin (sourceGaloisClosureSelectedLength m) =>
      (sourceGaloisClosureSelectedRationalPlace m j).place) := by
  classical
  let P := fun j : Fin (sourceGaloisClosureSelectedLength m) =>
    (sourceGaloisClosureSelectedRationalPlace m j).place
  have hcard :
      (Finset.univ.image P).card =
        (Finset.univ : Finset (Fin (sourceGaloisClosureSelectedLength m))).card := by
    calc
      (Finset.univ.image P).card =
          sourceGaloisClosureSelectedLength m := by
        simpa only [sourceGaloisClosureSelectedPlaces, P] using
          sourceGaloisClosureSelectedPlaces_card m
      _ = (Finset.univ :
          Finset (Fin (sourceGaloisClosureSelectedLength m))).card := by simp
  have hinjOn : Set.InjOn P
      (↑(Finset.univ : Finset (Fin (sourceGaloisClosureSelectedLength m))) :
        Set (Fin (sourceGaloisClosureSelectedLength m))) :=
    Finset.card_image_iff.mp hcard
  intro i j hij
  exact hinjOn (Finset.mem_univ i) (Finset.mem_univ j) hij
noncomputable def sourceGaloisClosureSelectedDivisor (m : ℕ) :
    Divisor (GlobalPlace F256 (sourceGaloisSelectedDivisor_E m)) :=
  GlobalPlace.finitePlaceDivisor fun j : Fin (sourceGaloisClosureSelectedLength m) =>
    (sourceGaloisClosureSelectedRationalPlace m j).place
@[simp]
theorem sourceGaloisClosureSelectedDivisor_apply (m : ℕ)
    (j : Fin (sourceGaloisClosureSelectedLength m)) :
    sourceGaloisClosureSelectedDivisor m
        (sourceGaloisClosureSelectedRationalPlace m j).place = 1 := by
  exact GlobalPlace.finitePlaceDivisor_apply _
    (sourceGaloisSelectedDivisor_sourceGaloisClosureSelectedPlaceAt_injective m) j
noncomputable def sourceGaloisClosureSelectedVanishingFunction (m : ℕ) : sourceGaloisSelectedDivisor_E m :=
  ((sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m) : sourceGaloisSelectedDivisor_E m) ^ 15 - 1
theorem sourceGaloisSelectedDivisor_order_pow (m n : ℕ) (P : GlobalPlace F256 (sourceGaloisSelectedDivisor_E m))
    (x : sourceGaloisSelectedDivisor_E m) :
    P.order (x ^ n) = (n : ℤ) * P.order x := by
  unfold GlobalPlace.order
  rw [(P.valuation).map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring
theorem sourceGaloisClosureSelectedVanishingFunction_ne_zero (m : ℕ) :
    sourceGaloisClosureSelectedVanishingFunction m ≠ 0 := by
  let P : SourceGaloisWInfinityPrime m :=
    Classical.choice (sourceGaloisWInfinityPrime_nonempty m)
  let Q := sourceGaloisWInfinityPlaceOfPrime m P
  let w : sourceGaloisSelectedDivisor_E m :=
    (sourceGaloisWClosureGenerator m : SourceGaloisWClosureField m)
  intro hzero
  have hpow : w ^ 15 = 1 := by
    exact sub_eq_zero.mp (by
      simpa only [sourceGaloisClosureSelectedVanishingFunction, w] using hzero)
  have horderPow := sourceGaloisSelectedDivisor_order_pow m 15 Q w
  have horderW := sourceGaloisWInfinityPlaceOfPrime_order_generator m P
  have horderOne : Q.order (1 : sourceGaloisSelectedDivisor_E m) = 0 := by
    simpa only [map_one] using
      (Q.order_algebraMap (1 : F256) one_ne_zero)
  rw [hpow, horderOne, horderW] at horderPow
  have hramification := sourceGaloisWInfinityRamificationIndex_pos m
  omega
noncomputable def sourceGaloisClosureSelectedVanishingFunctionPoleDivisor (m : ℕ) :
    Divisor (GlobalPlace F256 (sourceGaloisSelectedDivisor_E m)) := by
  classical
  let f := sourceGaloisClosureSelectedVanishingFunction m
  exact if hf : f = 0 then 0
    else (-GlobalPlace.principalDivisor (k := F256) (F := sourceGaloisSelectedDivisor_E m)
      (Units.mk0 f hf)) ⊔ 0
noncomputable local instance (priority := 2000)
    sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingBaseModule :
    Module SourceSeedBaseValuationRing GaloisBaseField :=
  @Algebra.toModule SourceSeedBaseValuationRing GaloisBaseField _ _
    (inferInstance : Algebra SourceSeedBaseValuationRing GaloisBaseField)
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingBaseModule
noncomputable local instance (priority := 2000)
    sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingBaseFaithfulSMul :
    FaithfulSMul SourceSeedBaseValuationRing GaloisBaseField :=
  (faithfulSMul_iff_algebraMap_injective
    SourceSeedBaseValuationRing GaloisBaseField).2
      (ValuationSubring.subtype_injective
        sourceSeedFixedBaseOnePlace.valuationRing)
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingBaseFaithfulSMul
noncomputable local instance (priority := 2000)
    sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingAlgebra (m : ℕ) :
    Algebra SourceSeedBaseValuationRing (sourceGaloisSelectedDivisor_E m) :=
  ((algebraMap GaloisBaseField (sourceGaloisSelectedDivisor_E m)).comp
    (algebraMap SourceSeedBaseValuationRing GaloisBaseField)).toAlgebra
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingAlgebra
noncomputable local instance (priority := 2000)
    sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingSMul (m : ℕ) :
    SMul SourceSeedBaseValuationRing (sourceGaloisSelectedDivisor_E m) :=
  (sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingAlgebra m).toSMul
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingSMul
noncomputable local instance (priority := 2000)
    sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingModule (m : ℕ) :
    Module SourceSeedBaseValuationRing (sourceGaloisSelectedDivisor_E m) :=
  @Algebra.toModule SourceSeedBaseValuationRing (sourceGaloisSelectedDivisor_E m) _ _
    (sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingAlgebra m)
attribute [local instance 2000] sourceGaloisSelectedDivisor_selectedDivisorBaseValuationRingModule
noncomputable local instance sourceGaloisSelectedDivisor_selectedDivisorBaseScalarTower (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing GaloisBaseField (sourceGaloisSelectedDivisor_E m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorBaseScalarTower
noncomputable local instance sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureFractionTower
    (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) (sourceGaloisSelectedDivisor_E m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureFractionTower
noncomputable local instance sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureTorsionFree
    (m : ℕ) :
    Module.IsTorsionFree SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) := by
  letI : Module.IsTorsionFree SourceSeedBaseValuationRing (sourceGaloisSelectedDivisor_E m) := by
    apply Module.IsTorsionFree.comap
      (R := SourceSeedBaseValuationRing)
      (S := sourceGaloisSelectedDivisor_E m) (M := sourceGaloisSelectedDivisor_E m)
      (algebraMap SourceSeedBaseValuationRing (sourceGaloisSelectedDivisor_E m))
    · intro r hr
      have hinjective : Function.Injective
          (algebraMap SourceSeedBaseValuationRing (sourceGaloisSelectedDivisor_E m)) :=
        (algebraMap GaloisBaseField (sourceGaloisSelectedDivisor_E m)).injective.comp
          (ValuationSubring.subtype_injective
            sourceSeedFixedBaseOnePlace.valuationRing)
      exact IsRegular.of_ne_zero fun hzero =>
        hr.ne_zero (hinjective (by simpa only [map_zero] using hzero))
    · intro r x
      simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
  exact IsIntegralClosure.isTorsionFree
    SourceSeedBaseValuationRing (sourceGaloisSelectedDivisor_E m)
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureTorsionFree
noncomputable local instance sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureFinite
    (m : ℕ) :
    Module.Finite SourceSeedBaseValuationRing
      (SourceGaloisClosureIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite SourceSeedBaseValuationRing
    GaloisBaseField (sourceGaloisSelectedDivisor_E m) (SourceGaloisClosureIntegralClosure m)
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureFinite
noncomputable local instance sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureIsFractionRing
    (m : ℕ) :
    IsFractionRing (SourceGaloisClosureIntegralClosure m) (sourceGaloisSelectedDivisor_E m) :=
  integralClosure.isFractionRing_of_finite_extension GaloisBaseField (sourceGaloisSelectedDivisor_E m)
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureIsFractionRing
noncomputable local instance sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureIsDedekind
    (m : ℕ) : IsDedekindDomain (SourceGaloisClosureIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain SourceSeedBaseValuationRing
    GaloisBaseField (sourceGaloisSelectedDivisor_E m)
attribute [local instance] sourceGaloisSelectedDivisor_selectedDivisorIntegralClosureIsDedekind
theorem sourceGaloisSelectedDivisor_fixedBaseOnePlace_order_generator_sub_one :
    sourceSeedFixedBaseOnePlace.order
        (AdjoinSimple.gen F256 galoisBaseZ - 1) = 1 := by
  have hX : galoisBaseFieldEquivRatFunc RatFunc.X =
      AdjoinSimple.gen F256 galoisBaseZ := by
    apply Subtype.ext
    exact RatFunc.algEquivOfTranscendental_X
      galoisBaseZ galoisBaseZ_transcendental
  have hXsymm : galoisBaseFieldEquivRatFunc.symm
      (AdjoinSimple.gen F256 galoisBaseZ) = RatFunc.X := by
    rw [← hX, galoisBaseFieldEquivRatFunc.symm_apply_apply]
  rw [sourceSeedFixedBaseOnePlace, GlobalPlace.comapAlgEquiv_order,
    map_sub, map_one, hXsymm]
  have horder := baseRationalPlace_order_algebraMap_polynomial
    (1 : BasePoint) (Polynomial.X - Polynomial.C (1 : F256))
      (Polynomial.monic_X_sub_C (1 : F256)).ne_zero
  change (baseRationalPlace (1 : BasePoint)).place.order
      (algebraMap F256[X] (RatFunc F256)
        (Polynomial.X - Polynomial.C (1 : F256))) =
    ((Polynomial.X - Polynomial.C (1 : F256)).rootMultiplicity
      (1 : F256) : ℤ) at horder
  rw [Polynomial.rootMultiplicity_X_sub_C_self] at horder
  simp only [map_sub, RatFunc.algebraMap_X, map_one] at horder
  exact horder
theorem sourceGaloisSelectedDivisor_fixedBaseOnePlace_generator_sub_one_ne_zero :
    AdjoinSimple.gen F256 galoisBaseZ - 1 ≠ 0 := by
  intro hzero
  have horder := sourceGaloisSelectedDivisor_fixedBaseOnePlace_order_generator_sub_one
  rw [hzero] at horder
  simp [GlobalPlace.order] at horder
theorem sourceGaloisSelectedDivisor_fixedBaseOnePlace_valuation_generator_sub_one_lt_one :
    sourceSeedFixedBaseOnePlace.valuation
        (AdjoinSimple.gen F256 galoisBaseZ - 1) < 1 := by
  let x : GaloisBaseField := AdjoinSimple.gen F256 galoisBaseZ - 1
  have hx : x ≠ 0 := sourceGaloisSelectedDivisor_fixedBaseOnePlace_generator_sub_one_ne_zero
  have hvaluationNe : sourceSeedFixedBaseOnePlace.valuation x ≠ 0 :=
    sourceSeedFixedBaseOnePlace.valuation.ne_zero_iff.mpr hx
  have hlog : WithZero.log
      (sourceSeedFixedBaseOnePlace.valuation x) = -1 := by
    have horder := sourceGaloisSelectedDivisor_fixedBaseOnePlace_order_generator_sub_one
    unfold GlobalPlace.order at horder
    simpa only [x] using (show
      WithZero.log (sourceSeedFixedBaseOnePlace.valuation
        (AdjoinSimple.gen F256 galoisBaseZ - 1)) = -1 by omega)
  calc
    sourceSeedFixedBaseOnePlace.valuation x =
        WithZero.exp (WithZero.log
          (sourceSeedFixedBaseOnePlace.valuation x)) :=
      (WithZero.exp_log hvaluationNe).symm
    _ = WithZero.exp (-1 : ℤ) := by rw [hlog]
    _ < WithZero.exp (0 : ℤ) := WithZero.exp_lt_exp.mpr (by omega)
    _ = 1 := by simp
noncomputable def sourceGaloisSelectedDivisor_selectedBaseVanishingElement :
    SourceSeedBaseValuationRing :=
  ⟨AdjoinSimple.gen F256 galoisBaseZ - 1,
    (sourceSeedFixedBaseOnePlace.mem_valuationRing_iff _).mpr
      (le_of_lt sourceGaloisSelectedDivisor_fixedBaseOnePlace_valuation_generator_sub_one_lt_one)⟩
noncomputable def sourceGaloisSelectedDivisor_selectedVanishingIntegralElement (m : ℕ) :
    SourceGaloisClosureIntegralClosure m :=
  algebraMap SourceSeedBaseValuationRing
    (SourceGaloisClosureIntegralClosure m) sourceGaloisSelectedDivisor_selectedBaseVanishingElement
noncomputable def sourceGaloisSelectedDivisor_selectedVanishingFunctionZeroDivisor (m : ℕ) :
    Divisor (GlobalPlace F256 (sourceGaloisSelectedDivisor_E m)) :=
  GlobalPlace.principalDivisor (k := F256) (F := sourceGaloisSelectedDivisor_E m)
      (Units.mk0 (sourceGaloisClosureSelectedVanishingFunction m)
        (sourceGaloisClosureSelectedVanishingFunction_ne_zero m)) +
    sourceGaloisClosureSelectedVanishingFunctionPoleDivisor m
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


