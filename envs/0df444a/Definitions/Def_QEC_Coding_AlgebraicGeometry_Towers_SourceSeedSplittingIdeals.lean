-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSeedSplittingIdeals
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceSeedSplittingIdeals
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:30:21.323737+00:00
-- url     : https://prove2.me/theorems/d9a62737-33f2-4b0a-bd8b-e61396b28fba
-- title:
--   Source Seed Splitting Ideals
-- statement:
--   Definitions and structural lemmas for Source Seed Splitting Ideals, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSeedSplittingIdeals.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedBaseRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Valuation.LocalSubring
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisBaseField_seed_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedPlaceIndex_card
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedRationalPlace_injective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedRestrictedBasePlace_eq_baseOne
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_valuation_uniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_normalizedValuation_eq_of_isEquiv
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
noncomputable def sourceSeedFixedBaseOnePlace :
    GlobalPlace F256 GaloisBaseField :=
  GlobalPlace.comapAlgEquiv galoisBaseFieldEquivRatFunc.symm
    (baseRationalPlace (1 : BasePoint)).place
theorem sourceSeed_fixedBase_finrank (m : ℕ) :
    Module.finrank GaloisBaseField (SourceField m) = 240 * 16 ^ m :=
  sourceGaloisBaseField_seed_finrank m
abbrev SourceSeedBaseValuationRing : Type :=
  sourceSeedFixedBaseOnePlace.valuationRing
noncomputable local instance (priority := 2000)
    sourceSeedBaseValuationRingBaseModule :
    Module SourceSeedBaseValuationRing GaloisBaseField :=
  @Algebra.toModule SourceSeedBaseValuationRing GaloisBaseField _ _
    (inferInstance : Algebra SourceSeedBaseValuationRing GaloisBaseField)
attribute [local instance 2000] sourceSeedBaseValuationRingBaseModule
noncomputable local instance (priority := 2000)
    sourceSeedBaseValuationRingBaseFaithfulSMul :
    FaithfulSMul SourceSeedBaseValuationRing GaloisBaseField :=
  (faithfulSMul_iff_algebraMap_injective
    SourceSeedBaseValuationRing GaloisBaseField).2
      (ValuationSubring.subtype_injective
        sourceSeedFixedBaseOnePlace.valuationRing)
attribute [local instance 2000] sourceSeedBaseValuationRingBaseFaithfulSMul
noncomputable local instance (priority := 2000)
    sourceSeedBaseValuationRingAlgebra (m : ℕ) :
    Algebra SourceSeedBaseValuationRing (SourceField m) :=
  ((algebraMap GaloisBaseField (SourceField m)).comp
    (algebraMap SourceSeedBaseValuationRing GaloisBaseField)).toAlgebra
attribute [local instance 2000] sourceSeedBaseValuationRingAlgebra
noncomputable local instance (priority := 2000)
    sourceSeedBaseValuationRingSMul (m : ℕ) :
    SMul SourceSeedBaseValuationRing (SourceField m) :=
  (sourceSeedBaseValuationRingAlgebra m).toSMul
attribute [local instance 2000] sourceSeedBaseValuationRingSMul
noncomputable local instance (priority := 2000)
    sourceSeedBaseValuationRingModule (m : ℕ) :
    Module SourceSeedBaseValuationRing (SourceField m) :=
  @Algebra.toModule SourceSeedBaseValuationRing (SourceField m) _ _
    (sourceSeedBaseValuationRingAlgebra m)
attribute [local instance 2000] sourceSeedBaseValuationRingModule
abbrev SourceSeedIntegralClosure (m : ℕ) : Type :=
  integralClosure SourceSeedBaseValuationRing (SourceField m)
noncomputable local instance sourceSeedBaseScalarTower (m : ℕ) :
    IsScalarTower SourceSeedBaseValuationRing GaloisBaseField (SourceField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
attribute [local instance] sourceSeedBaseScalarTower
noncomputable local instance sourceSeedIntegralClosureTorsionFree
    (m : ℕ) :
    Module.IsTorsionFree SourceSeedBaseValuationRing
      (SourceSeedIntegralClosure m) := by
  letI : Module.IsTorsionFree SourceSeedBaseValuationRing (SourceField m) :=
    Module.IsTorsionFree.trans_faithfulSMul
      SourceSeedBaseValuationRing GaloisBaseField (SourceField m)
  exact IsIntegralClosure.isTorsionFree
    SourceSeedBaseValuationRing (SourceField m)
attribute [local instance] sourceSeedIntegralClosureTorsionFree
noncomputable local instance sourceSeedIntegralClosureFinite
    (m : ℕ) :
    Module.Finite SourceSeedBaseValuationRing
      (SourceSeedIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact IsIntegralClosure.finite SourceSeedBaseValuationRing
    GaloisBaseField (SourceField m) (SourceSeedIntegralClosure m)
attribute [local instance] sourceSeedIntegralClosureFinite
noncomputable local instance sourceSeedIntegralClosureIsFractionRing
    (m : ℕ) :
  IsFractionRing (SourceSeedIntegralClosure m) (SourceField m) :=
  integralClosure.isFractionRing_of_finite_extension
    GaloisBaseField (SourceField m)
attribute [local instance] sourceSeedIntegralClosureIsFractionRing
noncomputable local instance sourceSeedIntegralClosureIsDedekind
    (m : ℕ) : IsDedekindDomain (SourceSeedIntegralClosure m) := by
  letI : IsDiscreteValuationRing SourceSeedBaseValuationRing :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  exact integralClosure.isDedekindDomain SourceSeedBaseValuationRing
    GaloisBaseField (SourceField m)
attribute [local instance] sourceSeedIntegralClosureIsDedekind
theorem sourceSeedEmbedding_equiv_symm (m : ℕ)
    (x : GaloisBaseField) :
    sourceSelectedRatFuncEmbedding m (galoisBaseFieldEquivRatFunc.symm x) =
      algebraMap GaloisBaseField (SourceField m) x := by
  change sourceGaloisBaseFieldEmbedding m
      (galoisBaseFieldEquivRatFunc
        (galoisBaseFieldEquivRatFunc.symm x)) = _
  rw [galoisBaseFieldEquivRatFunc.apply_symm_apply]
  rfl
theorem sourceSeedValuation_isEquiv_comap
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSeedFixedBaseOnePlace.valuation.IsEquiv
      ((sourceSelectedRationalPlace m index).place.valuation.comap
        (algebraMap GaloisBaseField (SourceField m))) := by
  have hplace := sourceSelectedRestrictedBasePlace_eq_baseOne m index
  have hvaluation := congrArg GlobalPlace.valuation hplace
  have heq : sourceSeedFixedBaseOnePlace.valuation =
      (sourceSelectedRationalPlace m index).place.valuation.comap
        (algebraMap GaloisBaseField (SourceField m)) := by
    ext x
    change (baseRationalPlace (1 : BasePoint)).place.valuation
        (galoisBaseFieldEquivRatFunc.symm x) =
      (sourceSelectedRationalPlace m index).place.valuation
        (algebraMap GaloisBaseField (SourceField m) x)
    have hx := DFunLike.congr_fun hvaluation
      (galoisBaseFieldEquivRatFunc.symm x)
    change (sourceSelectedRationalPlace m index).place.valuation
        (sourceSelectedRatFuncEmbedding m
          (galoisBaseFieldEquivRatFunc.symm x)) =
      (baseRationalPlace (1 : BasePoint)).place.valuation
        (galoisBaseFieldEquivRatFunc.symm x) at hx
    rw [sourceSeedEmbedding_equiv_symm] at hx
    exact hx.symm
  rw [heq]
noncomputable abbrev sourceSeedValuationHasExtension
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSeedFixedBaseOnePlace.valuation.HasExtension
      (sourceSelectedRationalPlace m index).place.valuation where
  val_isEquiv_comap := sourceSeedValuation_isEquiv_comap m index
theorem sourceSeedIntegralClosure_le_valuationRing
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (integralClosure SourceSeedBaseValuationRing (SourceField m)).toSubring ≤
      (sourceSelectedRationalPlace m index).place.valuationRing.toSubring := by
  let P := sourceSeedFixedBaseOnePlace
  let Q := (sourceSelectedRationalPlace m index).place
  letI : P.valuation.HasExtension Q.valuation :=
    sourceSeedValuationHasExtension m index
  letI : IsIntegrallyClosedIn
      (sourceSelectedRationalPlace m index).place.valuationRing.toSubring
      (SourceField m) :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn
      (R := (sourceSelectedRationalPlace m index).place.valuationRing)
      (SourceField m)).mp inferInstance
  change (integralClosure P.valuationRing (SourceField m)).toSubring ≤
    Q.valuationRing.toSubring
  rw [Subring.integralClosure_le_iff]
  intro x
  exact Valuation.HasExtension.algebraMap_mem_valuationSubring
    P.valuation Q.valuation x
noncomputable def sourceSeedIntegralClosureToValuationRing
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    SourceSeedIntegralClosure m →+*
      (sourceSelectedRationalPlace m index).place.valuationRing := by
  let Q := (sourceSelectedRationalPlace m index).place
  exact (algebraMap (SourceSeedIntegralClosure m) (SourceField m)).codRestrict
    Q.valuationRing fun x =>
      sourceSeedIntegralClosure_le_valuationRing m index x.property
noncomputable def sourceSeedUpperIdeal
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    Ideal (SourceSeedIntegralClosure m) :=
  (IsLocalRing.maximalIdeal
    (sourceSelectedRationalPlace m index).place.valuationRing).comap
      (sourceSeedIntegralClosureToValuationRing m index)
theorem sourceSeedUpperIdeal_isPrime
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (sourceSeedUpperIdeal m index).IsPrime := by
  dsimp [sourceSeedUpperIdeal]
  exact (IsLocalRing.maximalIdeal
    (sourceSelectedRationalPlace m index).place.valuationRing).comap_isPrime _
theorem sourceSeedUpperIdeal_liesOver
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (sourceSeedUpperIdeal m index).LiesOver
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing) := by
  let P := sourceSeedFixedBaseOnePlace
  let Q := (sourceSelectedRationalPlace m index).place
  letI : P.valuation.HasExtension Q.valuation :=
    sourceSeedValuationHasExtension m index
  constructor
  change IsLocalRing.maximalIdeal P.valuationRing =
    (IsLocalRing.maximalIdeal Q.valuationRing).comap
      (algebraMap P.valuationRing Q.valuationRing)
  exact (Valuation.HasExtension.maximalIdeal_comap_algebraMap_eq_maximalIdeal
    P.valuation Q.valuation).symm
theorem sourceSeedUpperIdeal_ne_bot
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSeedUpperIdeal m index ≠ ⊥ := by
  let O := SourceSeedBaseValuationRing
  let C := SourceSeedIntegralClosure m
  let Q := (sourceSelectedRationalPlace m index).place
  obtain ⟨a, s, hs, hfrac⟩ :=
    IsFractionRing.div_surjective C Q.uniformizer
  have hs0 : algebraMap C (SourceField m) s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have hu0 : Q.uniformizer ≠ 0 := by
    apply Q.valuation.ne_zero_iff.mp
    rw [Q.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  have hu_lt_one : Q.valuation Q.uniformizer < 1 := by
    rw [Q.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hs_mem : algebraMap C (SourceField m) s ∈ Q.valuationRing :=
    sourceSeedIntegralClosure_le_valuationRing m index s.property
  have hs_le_one : Q.valuation (algebraMap C (SourceField m) s) ≤ 1 :=
    (Q.valuation.mem_valuationSubring_iff _).mp hs_mem
  have hprod : algebraMap C (SourceField m) a =
      Q.uniformizer * algebraMap C (SourceField m) s := by
    calc
      algebraMap C (SourceField m) a =
          (algebraMap C (SourceField m) a / algebraMap C (SourceField m) s) *
            algebraMap C (SourceField m) s :=
        (div_mul_cancel₀ _ hs0).symm
      _ = Q.uniformizer * algebraMap C (SourceField m) s := by rw [hfrac]
  have ha0 : a ≠ 0 := by
    intro ha
    have hzero : Q.uniformizer * algebraMap C (SourceField m) s = 0 := by
      simpa [ha] using hprod.symm
    exact (mul_ne_zero hu0 hs0) hzero
  have ha_lt_one : Q.valuation (algebraMap C (SourceField m) a) < 1 := by
    calc
      Q.valuation (algebraMap C (SourceField m) a) =
          Q.valuation Q.uniformizer *
            Q.valuation (algebraMap C (SourceField m) s) := by
        rw [hprod, Q.valuation.map_mul]
      _ ≤ Q.valuation Q.uniformizer * 1 :=
        mul_le_mul_of_nonneg_left hs_le_one
          (le_of_lt (by rw [Q.valuation_uniformizer]; exact WithZero.exp_pos))
      _ = Q.valuation Q.uniformizer := mul_one _
      _ < 1 := hu_lt_one
  have ha_mem : a ∈ sourceSeedUpperIdeal m index := by
    change sourceSeedIntegralClosureToValuationRing m index a ∈
      IsLocalRing.maximalIdeal Q.valuationRing
    rw [Valuation.mem_maximalIdeal_iff]
    exact ha_lt_one
  intro hbot
  exact ha0 (Ideal.mem_bot.mp (hbot ▸ ha_mem))
noncomputable def sourceSeedUpperHeightOne
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    IsDedekindDomain.HeightOneSpectrum (SourceSeedIntegralClosure m) :=
  ⟨sourceSeedUpperIdeal m index,
    sourceSeedUpperIdeal_isPrime m index,
    sourceSeedUpperIdeal_ne_bot m index⟩
theorem sourceSeedUpperPrimeCompl_maps_to_unit
    (m : ℕ) (index : SourceSelectedPlaceIndex m)
    (s : (sourceSeedUpperHeightOne m index).asIdeal.primeCompl) :
    IsUnit (sourceSeedIntegralClosureToValuationRing m index s) := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hs
  exact s.property hs
noncomputable abbrev sourceSeedUpperCanonicalLocalization
    (m : ℕ) (index : SourceSelectedPlaceIndex m) : ValuationSubring (SourceField m) :=
  (sourceSeedUpperHeightOne m index).valuationSubringAtPrime (SourceField m)
noncomputable def sourceSeedUpperLocalizationToValuationRing
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSeedUpperCanonicalLocalization m index →+*
      (sourceSelectedRationalPlace m index).place.valuationRing :=
  IsLocalization.lift
    (M := (sourceSeedUpperHeightOne m index).asIdeal.primeCompl)
    (g := sourceSeedIntegralClosureToValuationRing m index)
    (sourceSeedUpperPrimeCompl_maps_to_unit m index)
theorem sourceSeedUpperLocalizationToValuationRing_comp
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (sourceSeedUpperLocalizationToValuationRing m index).comp
        (algebraMap (SourceSeedIntegralClosure m)
          (sourceSeedUpperCanonicalLocalization m index)) =
      sourceSeedIntegralClosureToValuationRing m index := by
  simpa [sourceSeedUpperLocalizationToValuationRing] using
    (IsLocalization.lift_comp
      (sourceSeedUpperPrimeCompl_maps_to_unit m index))
theorem sourceSeedUpperLocalization_coe_triangle
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (ValuationSubring.subtype
      (sourceSelectedRationalPlace m index).place.valuationRing).comp
        (sourceSeedUpperLocalizationToValuationRing m index) =
      ValuationSubring.subtype
        (sourceSeedUpperCanonicalLocalization m index) := by
  apply IsLocalization.ringHom_ext
    (sourceSeedUpperHeightOne m index).asIdeal.primeCompl
  ext b
  change (((sourceSeedUpperLocalizationToValuationRing m index
      (algebraMap (SourceSeedIntegralClosure m)
        (sourceSeedUpperCanonicalLocalization m index) b)) :
          (sourceSelectedRationalPlace m index).place.valuationRing) :
      SourceField m) = algebraMap (SourceSeedIntegralClosure m) (SourceField m) b
  rw [← RingHom.comp_apply,
    sourceSeedUpperLocalizationToValuationRing_comp]
  rfl
theorem sourceSeedUpperCanonicalLocalization_le_valuationRing
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSeedUpperCanonicalLocalization m index ≤
      (sourceSelectedRationalPlace m index).place.valuationRing := by
  intro x hx
  let xC : sourceSeedUpperCanonicalLocalization m index := ⟨x, hx⟩
  have htriangle := RingHom.congr_fun
    (sourceSeedUpperLocalization_coe_triangle m index) xC
  have hxField :
      ((sourceSeedUpperLocalizationToValuationRing m index xC :
        (sourceSelectedRationalPlace m index).place.valuationRing) :
          SourceField m) = x := by
    simpa only [RingHom.comp_apply, ValuationSubring.coe_subtype] using
      htriangle
  rw [← hxField]
  exact (sourceSeedUpperLocalizationToValuationRing m index xC).property
theorem sourceSeedPlaceValuation_isNontrivial
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (sourceSelectedRationalPlace m index).place.valuation.IsNontrivial := by
  let Q := (sourceSelectedRationalPlace m index).place
  rw [Valuation.isNontrivial_iff_exists_lt_one]
  refine ⟨Q.uniformizer, ?_, ?_⟩
  · apply Q.valuation.ne_zero_iff.mp
    rw [Q.valuation_uniformizer]
    exact WithZero.exp_ne_zero
  · rw [Q.valuation_uniformizer, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
theorem sourceSeedPlaceValuationRing_ne_top
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (sourceSelectedRationalPlace m index).place.valuationRing ≠ ⊤ := by
  let Q := (sourceSelectedRationalPlace m index).place
  intro htop
  exact ((Valuation.valuationSubring_eq_top_iff (v := Q.valuation)).mp htop)
    (sourceSeedPlaceValuation_isNontrivial m index)
theorem sourceSeedUpperCanonicalLocalization_eq_valuationRing
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    sourceSeedUpperCanonicalLocalization m index =
      (sourceSelectedRationalPlace m index).place.valuationRing :=
  ValuationSubring.eq_of_le_of_ne_top _
    (sourceSeedUpperCanonicalLocalization_le_valuationRing m index)
    (sourceSeedPlaceValuationRing_ne_top m index)
noncomputable def sourceSeedUpperPrime (m : ℕ)
    (index : SourceSelectedPlaceIndex m) :
    (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceSeedIntegralClosure m) := by
  letI : (sourceSeedUpperIdeal m index).IsPrime :=
    sourceSeedUpperIdeal_isPrime m index
  letI : (sourceSeedUpperIdeal m index).LiesOver
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing) :=
    sourceSeedUpperIdeal_liesOver m index
  exact Ideal.primesOver.mk _ (sourceSeedUpperIdeal m index)
theorem globalPlace_eq_of_valuation_eq
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    {P Q : GlobalPlace F256 E} (h : P.valuation = Q.valuation) : P = Q := by
  cases P
  cases Q
  cases h
  rfl
theorem rationalPlace_eq_of_place_eq
    {E : Type*} [_root_.Field E] [Algebra F256 E]
    {P Q : RationalPlace F256 E} (h : P.place = Q.place) : P = Q := by
  cases P with
  | mk pp pe ph =>
      cases Q with
      | mk qp qe qh =>
          dsimp at h
          subst qp
          have he : pe = qe := by
            apply RingEquiv.ext
            intro a
            rw [ph, qh]
          subst qe
          rfl
theorem sourceSeedUpperPrime_injective (m : ℕ) :
    Function.Injective (sourceSeedUpperPrime m) := by
  intro i j hij
  have hideal : sourceSeedUpperIdeal m i =
      sourceSeedUpperIdeal m j := congrArg Subtype.val hij
  have hheight : sourceSeedUpperHeightOne m i =
      sourceSeedUpperHeightOne m j := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact hideal
  have hvaluationRing :
      (sourceSelectedRationalPlace m i).place.valuationRing =
      (sourceSelectedRationalPlace m j).place.valuationRing := by
    rw [← sourceSeedUpperCanonicalLocalization_eq_valuationRing m i,
      ← sourceSeedUpperCanonicalLocalization_eq_valuationRing m j]
    change (sourceSeedUpperHeightOne m i).valuationSubringAtPrime (SourceField m) =
      (sourceSeedUpperHeightOne m j).valuationSubringAtPrime (SourceField m)
    rw [hheight]
  have hisEquiv :
      (sourceSelectedRationalPlace m i).place.valuation.IsEquiv
        (sourceSelectedRationalPlace m j).place.valuation := by
    rw [Valuation.isEquiv_iff_valuationSubring]
    exact hvaluationRing
  have hvaluation :
      (sourceSelectedRationalPlace m i).place.valuation =
        (sourceSelectedRationalPlace m j).place.valuation :=
    normalizedValuation_eq_of_isEquiv
      (sourceSelectedRationalPlace m i).place.valuation
      (sourceSelectedRationalPlace m j).place.valuation
      (sourceSelectedRationalPlace m i).place.normalized
      (sourceSelectedRationalPlace m j).place.normalized hisEquiv
  apply sourceSelectedRationalPlace_injective m
  exact rationalPlace_eq_of_place_eq
    (globalPlace_eq_of_valuation_eq hvaluation)
theorem sourceSeed_primesOver_ncard (m : ℕ) :
    ((IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
      (SourceSeedIntegralClosure m)).ncard = 240 * 16 ^ m := by
  let O := SourceSeedBaseValuationRing
  let C := SourceSeedIntegralClosure m
  let K := GaloisBaseField
  let L := SourceField m
  let p : Ideal O := IsLocalRing.maximalIdeal O
  letI : IsDiscreteValuationRing O :=
    sourceSeedFixedBaseOnePlace.valuationRing_isDiscreteValuationRing
  letI : Module.IsTorsionFree O C := by
    change Module.IsTorsionFree SourceSeedBaseValuationRing
      (SourceSeedIntegralClosure m)
    exact sourceSeedIntegralClosureTorsionFree m
  letI : NoZeroSMulDivisors O C := by
    constructor
    intro c x h
    exact smul_eq_zero.mp h
  have hp0 : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hlower : 240 * 16 ^ m ≤ (p.primesOver C).ncard := by
    calc
      240 * 16 ^ m = Nat.card (SourceSelectedPlaceIndex m) := by
        rw [Nat.card_eq_fintype_card, sourceSelectedPlaceIndex_card]
      _ ≤ Nat.card (p.primesOver C) :=
        Nat.card_le_card_of_injective (sourceSeedUpperPrime m)
          (sourceSeedUpperPrime_injective m)
      _ = (p.primesOver C).ncard := Nat.card_coe_set_eq _
  have hupper : (p.primesOver C).ncard ≤ Module.finrank K L := by
    rw [← IsDedekindDomain.coe_primesOverFinset hp0 C,
      Set.ncard_coe_finset]
    exact Ideal.card_primesOverFinset_le_finrank C K L hp0
  apply le_antisymm
  · exact hupper.trans_eq (sourceSeed_fixedBase_finrank m)
  · exact hlower
noncomputable def sourceSeedUpperPrimeEquiv (m : ℕ) :
    SourceSelectedPlaceIndex m ≃
      (IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
        (SourceSeedIntegralClosure m) := by
  apply Equiv.ofBijective (sourceSeedUpperPrime m)
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨sourceSeedUpperPrime_injective m, ?_⟩
  calc
    Nat.card (SourceSelectedPlaceIndex m) = 240 * 16 ^ m := by
      rw [Nat.card_eq_fintype_card, sourceSelectedPlaceIndex_card]
    _ = ((IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
        (SourceSeedIntegralClosure m)).ncard :=
      (sourceSeed_primesOver_ncard m).symm
    _ = Nat.card
        ((IsLocalRing.maximalIdeal SourceSeedBaseValuationRing).primesOver
          (SourceSeedIntegralClosure m)) :=
      (Nat.card_coe_set_eq _).symm
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


