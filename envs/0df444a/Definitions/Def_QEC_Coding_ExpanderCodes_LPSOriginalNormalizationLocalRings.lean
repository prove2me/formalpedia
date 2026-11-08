-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:51:30.633485+00:00
-- url     : https://prove2.me/theorems/c30ff53d-e0a3-4a95-89f5-7b0ade7ed7a7
-- title:
--   LPSOriginal Normalization Local Rings
-- statement:
--   Definitions and structural lemmas for LPSOriginal Normalization Local Rings, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationLocalRings.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationComplexPoints
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_meromorphicNoPoleEvaluation_eq_zero_iff_order_pos
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ValuationCentres_polynomialIntegralModel_evaluation_kernel_ne_bot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ValuationCentres_valuationRing_eq_actual_heightOneCentre
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGluedChartMap_openImmersion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldLocalOrder_integral_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finiteDimensional
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityConstantChart_value
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityNormalChartEvaluation_constant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityNormalChartEvaluation_surjective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizationChart_order_cover
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizationCurveSpecPoint_infinity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizationCurveSpecPoint_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroConstantChart_value
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroNormalChartEvaluation_constant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroNormalChartEvaluation_surjective

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.ValuationCentres
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
local instance _p2m_local_instance_82cf6a41b6_22 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local instance _p2m_local_instance_82cf6a41b6_27 : Algebra P K := ((algebraMap J K).comp (algebraMap P J)).toAlgebra
local instance _p2m_local_instance_82cf6a41b6_28 : Algebra ℂ K := ((algebraMap J K).comp (algebraMap ℂ J)).toAlgebra
local instance _p2m_local_instance_82cf6a41b6_29 : IsScalarTower ℂ J K := .of_algebraMap_eq' rfl
local instance _p2m_local_instance_82cf6a41b6_30 : IsScalarTower ℂ P K := .of_algebraMap_eq' rfl
local notation "IC0" => lpsOriginalComplexNormalZeroChart N hpos
lemma lpsOriginalZeroEvaluation_ker_isMaximal (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    (RingHom.ker (lpsOriginalZeroNormalChartEvaluation N hpos hN x hj)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (lpsOriginalZeroNormalChartEvaluation_surjective N hpos hN x hj)
lemma lpsOriginalInfinityEvaluation_ker_isMaximal (x : LPSOriginalFilledCurve N)
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    (RingHom.ker (lpsOriginalInfinityNormalChartEvaluation N hpos hN x hi)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (lpsOriginalInfinityNormalChartEvaluation_surjective N hpos hN x hi)
lemma lpsOriginalZeroEvaluation_eq_zero_iff_order_pos (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (a : IC0) :
    lpsOriginalZeroNormalChartEvaluation N hpos hN x hj a = 0 ↔
      0 < lpsOriginalFieldLocalOrder N hN hpos x a.val :=
  meromorphicNoPoleEvaluation_eq_zero_iff_order_pos _ _
lemma lpsOriginalInfinityEvaluation_eq_zero_iff_order_pos (x : LPSOriginalFilledCurve N)
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (a : lpsOriginalComplexNormalInfinityChart N hpos) :
    lpsOriginalInfinityNormalChartEvaluation N hpos hN x hi a = 0 ↔
      0 < lpsOriginalFieldLocalOrder N hN hpos x a.val :=
  meromorphicNoPoleEvaluation_eq_zero_iff_order_pos _ _
local instance _p2m_local_instance_82cf6a41b6_59 : IsScalarTower P J K := .of_algebraMap_eq' rfl
local instance _p2m_local_instance_82cf6a41b6_60 : FiniteDimensional J K :=
  lpsOriginalGeneratedFunctionField_finiteDimensional N hpos
lemma lpsOriginalZeroChart_isDedekindDomain : IsDedekindDomain IC0 :=
  integralClosure.isDedekindDomain P J K
lemma lpsOriginalZeroChart_isFractionRing : IsFractionRing IC0 K :=
  IsIntegralClosure.isFractionRing_of_finite_extension P J K IC0
lemma lpsOriginalZeroEvaluation_ker_ne_bot (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    RingHom.ker (lpsOriginalZeroNormalChartEvaluation N hpos hN x hj) ≠ ⊥ := by
  apply QEC.Coding.AlgebraicGeometry.ValuationCentres.polynomialIntegralModel_evaluation_kernel_ne_bot
    ((algebraMap J K).injective.comp (IsFractionRing.injective P J))
  intro c
  have h := lpsOriginalZeroNormalChartEvaluation_constant N hpos hN x hj c
  convert h using 1
  apply congrArg (lpsOriginalZeroNormalChartEvaluation N hpos hN x hj)
  apply Subtype.ext
  rw [lpsOriginalZeroConstantChart_value]
  exact (IsScalarTower.algebraMap_apply ℂ P K c).symm
lemma lpsOriginalZeroEvaluation_heightOneCentre_and_valuationRing
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    let : IsDedekindDomain IC0 := lpsOriginalZeroChart_isDedekindDomain N hpos
    let : IsFractionRing IC0 K := lpsOriginalZeroChart_isFractionRing N hpos
    ∃ H : IsDedekindDomain.HeightOneSpectrum IC0,
      H.asIdeal = RingHom.ker (lpsOriginalZeroNormalChartEvaluation N hpos hN x hj) ∧
      H.valuationSubringAtPrime K =
        (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring := by
  let : IsDedekindDomain IC0 := lpsOriginalZeroChart_isDedekindDomain N hpos
  let : IsFractionRing IC0 K := lpsOriginalZeroChart_isFractionRing N hpos
  let v := AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)
  have hR (a : IC0) : v (algebraMap IC0 K a) ≤ 1 :=
    lpsOriginalFieldLocalOrder_integral_nonnegative N hN hpos x hj a
  have hn : ∃ a : IC0, a ≠ 0 ∧ v (algebraMap IC0 K a) < 1 := by
    obtain ⟨a,ha,hn⟩ :=
      (RingHom.ker (lpsOriginalZeroNormalChartEvaluation N hpos hN x hj)).ne_bot_iff.mp
        (lpsOriginalZeroEvaluation_ker_ne_bot N hpos hN x hj)
    refine ⟨a,hn,?_⟩
    exact (lpsOriginalZeroEvaluation_eq_zero_iff_order_pos N hpos hN x hj a).mp ha
  obtain ⟨H,hH,hV⟩ := valuationRing_eq_actual_heightOneCentre IC0 v hR hn
  refine ⟨H,?_,hV⟩
  rw [hH]
  ext a
  rw [Ideal.mem_comap, v.mem_maximalIdeal_iff]
  change v (algebraMap IC0 K a) < 1 ↔
    lpsOriginalZeroNormalChartEvaluation N hpos hN x hj a = 0
  exact (lpsOriginalZeroEvaluation_eq_zero_iff_order_pos N hpos hN x hj a).symm
local instance _p2m_local_instance_82cf6a41b6_112 : IsDedekindDomain IC0 := lpsOriginalZeroChart_isDedekindDomain N hpos
local instance _p2m_local_instance_82cf6a41b6_113 : IsFractionRing IC0 K := lpsOriginalZeroChart_isFractionRing N hpos
def lpsOriginalZeroHeightOneCentre (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    IsDedekindDomain.HeightOneSpectrum IC0 :=
  ⟨RingHom.ker (lpsOriginalZeroNormalChartEvaluation N hpos hN x h),
    (lpsOriginalZeroEvaluation_ker_isMaximal N hpos hN x h).isPrime,
    lpsOriginalZeroEvaluation_ker_ne_bot N hpos hN x h⟩
lemma lpsOriginalZeroHeightOneCentre_valuationRing (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    (lpsOriginalZeroHeightOneCentre N hpos hN x h).valuationSubringAtPrime K =
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring := by
  obtain ⟨H,hH,hV⟩ := lpsOriginalZeroEvaluation_heightOneCentre_and_valuationRing N hpos hN x h
  have he : H = lpsOriginalZeroHeightOneCentre N hpos hN x h :=
    IsDedekindDomain.HeightOneSpectrum.ext hH
  rw [he] at hV
  exact hV
def lpsOriginalZeroStalkMeromorphicValuationRingEquiv (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    (_root_.AlgebraicGeometry.Spec.structureSheaf IC0).presheaf.stalk
      (⟨(lpsOriginalZeroHeightOneCentre N hpos hN x h).asIdeal,
        (lpsOriginalZeroHeightOneCentre N hpos hN x h).isPrime⟩ : PrimeSpectrum IC0) ≃+*
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring :=
  (heightOneStalkValuationRingEquiv IC0 (lpsOriginalZeroHeightOneCentre N hpos hN x h)).trans
    (RingEquiv.subringCongr
      (congrArg ValuationSubring.toSubring (lpsOriginalZeroHeightOneCentre_valuationRing N hpos hN x h)))
lemma lpsOriginalZeroNormalizationSpecPoint_heightOneCentre
    (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    (lpsOriginalZeroNormalizationSpecPoint N hpos hN x h).base
      (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ) =
      (⟨(lpsOriginalZeroHeightOneCentre N hpos hN x h).asIdeal,
        (lpsOriginalZeroHeightOneCentre N hpos hN x h).isPrime⟩ : PrimeSpectrum IC0) := by
  apply PrimeSpectrum.ext
  rfl
def lpsOriginalZeroNormalizationPointLocalRingEquiv
    (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    (_root_.AlgebraicGeometry.Spec.structureSheaf IC0).presheaf.stalk
      ((lpsOriginalZeroNormalizationSpecPoint N hpos hN x h).base
        (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)) ≃+*
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring := by
  rw [lpsOriginalZeroNormalizationSpecPoint_heightOneCentre]
  exact lpsOriginalZeroStalkMeromorphicValuationRingEquiv N hpos hN x h
def lpsOriginalNormalizationCurveLocalRingEquiv_zero
    (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    (lpsOriginalComplexNormalGluedScheme N hpos).presheaf.stalk
      ((lpsOriginalNormalizationCurveSpecPoint N hpos hN x).base
        (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)) ≃+*
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring := by
  rw [lpsOriginalNormalizationCurveSpecPoint_zero N hpos hN x h]
  letI : _root_.AlgebraicGeometry.IsOpenImmersion
      (lpsOriginalComplexNormalGluedChartMap N hpos false) :=
    lpsOriginalComplexNormalGluedChartMap_openImmersion N hpos false
  exact (CategoryTheory.asIso
    ((lpsOriginalComplexNormalGluedChartMap N hpos false).stalkMap
      ((lpsOriginalZeroNormalizationSpecPoint N hpos hN x h).base
        (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)))).commRingCatIsoToRingEquiv.trans
      (lpsOriginalZeroNormalizationPointLocalRingEquiv N hpos hN x h)
section InfinityModel
local instance _p2m_local_instance_82cf6a41b6_206 : Algebra P J := lpsOriginalReciprocalBaseCAlgebra
local instance _p2m_local_instance_82cf6a41b6_207 : SMul P J := Algebra.toSMul
local instance _p2m_local_instance_82cf6a41b6_208 : Module P J := Algebra.toModule
local instance _p2m_local_instance_82cf6a41b6_209 : IsFractionRing P J := lpsOriginalReciprocalBaseC_isFractionRing
local instance _p2m_local_instance_82cf6a41b6_210 : Algebra P K := (lpsOriginalReciprocalComplexFieldPolynomialMap N hpos).toAlgebra
local instance _p2m_local_instance_82cf6a41b6_211 : SMul P K := Algebra.toSMul
local instance _p2m_local_instance_82cf6a41b6_212 : Module P K := Algebra.toModule
local instance _p2m_local_instance_82cf6a41b6_213 : IsScalarTower P J K := .of_algebraMap_eq' rfl
local notation "ICI" => lpsOriginalComplexNormalInfinityChart N hpos
lemma lpsOriginalInfinityChart_isDedekindDomain : IsDedekindDomain ICI :=
  integralClosure.isDedekindDomain P J K
lemma lpsOriginalInfinityChart_isFractionRing : IsFractionRing ICI K :=
  IsIntegralClosure.isFractionRing_of_finite_extension P J K ICI
lemma lpsOriginalInfinityEvaluation_ker_ne_bot (x : LPSOriginalFilledCurve N)
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x
      (((algebraMap J K).comp (lpsOriginalCanonicalComplexPolynomialFractionMap))
        Polynomial.X)⁻¹) :
    RingHom.ker (lpsOriginalInfinityNormalChartEvaluation N hpos hN x hi) ≠ ⊥ := by
  apply QEC.Coding.AlgebraicGeometry.ValuationCentres.polynomialIntegralModel_evaluation_kernel_ne_bot
    ((algebraMap J K).injective.comp (IsFractionRing.injective P J))
  intro c
  have h := lpsOriginalInfinityNormalChartEvaluation_constant N hpos hN x hi c
  convert h using 1
  apply congrArg (lpsOriginalInfinityNormalChartEvaluation N hpos hN x hi)
  apply Subtype.ext
  rw [lpsOriginalInfinityConstantChart_value]
  change algebraMap J K
    (lpsOriginalComplexJFractionInversion
      (algebraMap ℂ J c)) = algebraMap ℂ K c
  rw [lpsOriginalComplexJFractionInversion_constant]
  rfl
lemma lpsOriginalInfinityEvaluation_heightOneCentre_and_valuationRing
    (x : LPSOriginalFilledCurve N)
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x
      (((algebraMap J K).comp (lpsOriginalCanonicalComplexPolynomialFractionMap))
        Polynomial.X)⁻¹) :
    let : IsDedekindDomain ICI := lpsOriginalInfinityChart_isDedekindDomain N hpos
    let : IsFractionRing ICI K := lpsOriginalInfinityChart_isFractionRing N hpos
    ∃ H : IsDedekindDomain.HeightOneSpectrum ICI,
      H.asIdeal = RingHom.ker (lpsOriginalInfinityNormalChartEvaluation N hpos hN x hi) ∧
      H.valuationSubringAtPrime K =
        (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring := by
  let : IsDedekindDomain ICI := lpsOriginalInfinityChart_isDedekindDomain N hpos
  let : IsFractionRing ICI K := lpsOriginalInfinityChart_isFractionRing N hpos
  let v := AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)
  have hR (a : ICI) : v (algebraMap ICI K a) ≤ 1 :=
    lpsOriginalInfinityIntegral_order_nonnegative N hpos hN x hi a
  have hn : ∃ a : ICI, a ≠ 0 ∧ v (algebraMap ICI K a) < 1 := by
    obtain ⟨a,ha,hn⟩ :=
      (RingHom.ker (lpsOriginalInfinityNormalChartEvaluation N hpos hN x hi)).ne_bot_iff.mp
        (lpsOriginalInfinityEvaluation_ker_ne_bot N hpos hN x hi)
    refine ⟨a,hn,?_⟩
    exact (lpsOriginalInfinityEvaluation_eq_zero_iff_order_pos N hpos hN x hi a).mp ha
  obtain ⟨H,hH,hV⟩ := valuationRing_eq_actual_heightOneCentre ICI v hR hn
  refine ⟨H,?_,hV⟩
  rw [hH]
  ext a
  rw [Ideal.mem_comap, v.mem_maximalIdeal_iff]
  change v (algebraMap ICI K a) < 1 ↔
    lpsOriginalInfinityNormalChartEvaluation N hpos hN x hi a = 0
  exact (lpsOriginalInfinityEvaluation_eq_zero_iff_order_pos N hpos hN x hi a).symm
local instance _p2m_local_instance_82cf6a41b6_272 : IsDedekindDomain ICI := lpsOriginalInfinityChart_isDedekindDomain N hpos
local instance _p2m_local_instance_82cf6a41b6_273 : IsFractionRing ICI K := lpsOriginalInfinityChart_isFractionRing N hpos
def lpsOriginalInfinityHeightOneCentre (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (((algebraMap J K).comp lpsOriginalCanonicalComplexPolynomialFractionMap) Polynomial.X)⁻¹) :
    IsDedekindDomain.HeightOneSpectrum ICI :=
  ⟨RingHom.ker (lpsOriginalInfinityNormalChartEvaluation N hpos hN x h),
    (lpsOriginalInfinityEvaluation_ker_isMaximal N hpos hN x h).isPrime,
    lpsOriginalInfinityEvaluation_ker_ne_bot N hpos hN x h⟩
lemma lpsOriginalInfinityHeightOneCentre_valuationRing (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (((algebraMap J K).comp lpsOriginalCanonicalComplexPolynomialFractionMap) Polynomial.X)⁻¹) :
    (lpsOriginalInfinityHeightOneCentre N hpos hN x h).valuationSubringAtPrime K =
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring := by
  obtain ⟨H,hH,hV⟩ := lpsOriginalInfinityEvaluation_heightOneCentre_and_valuationRing N hpos hN x h
  have he : H = lpsOriginalInfinityHeightOneCentre N hpos hN x h :=
    IsDedekindDomain.HeightOneSpectrum.ext hH
  rw [he] at hV
  exact hV
def lpsOriginalInfinityStalkMeromorphicValuationRingEquiv (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (((algebraMap J K).comp lpsOriginalCanonicalComplexPolynomialFractionMap) Polynomial.X)⁻¹) :
    (_root_.AlgebraicGeometry.Spec.structureSheaf ICI).presheaf.stalk
      (⟨(lpsOriginalInfinityHeightOneCentre N hpos hN x h).asIdeal,
        (lpsOriginalInfinityHeightOneCentre N hpos hN x h).isPrime⟩ : PrimeSpectrum ICI) ≃+*
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring :=
  (heightOneStalkValuationRingEquiv ICI (lpsOriginalInfinityHeightOneCentre N hpos hN x h)).trans
    (RingEquiv.subringCongr
      (congrArg ValuationSubring.toSubring (lpsOriginalInfinityHeightOneCentre_valuationRing N hpos hN x h)))
lemma lpsOriginalInfinityNormalizationSpecPoint_heightOneCentre
    (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (((algebraMap J K).comp lpsOriginalCanonicalComplexPolynomialFractionMap) Polynomial.X)⁻¹) :
    (lpsOriginalInfinityNormalizationSpecPoint N hpos hN x h).base
      (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ) =
      (⟨(lpsOriginalInfinityHeightOneCentre N hpos hN x h).asIdeal,
        (lpsOriginalInfinityHeightOneCentre N hpos hN x h).isPrime⟩ : PrimeSpectrum ICI) := by
  apply PrimeSpectrum.ext
  rfl
def lpsOriginalInfinityNormalizationPointLocalRingEquiv
    (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (((algebraMap J K).comp lpsOriginalCanonicalComplexPolynomialFractionMap) Polynomial.X)⁻¹) :
    (_root_.AlgebraicGeometry.Spec.structureSheaf ICI).presheaf.stalk
      ((lpsOriginalInfinityNormalizationSpecPoint N hpos hN x h).base
        (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)) ≃+*
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring := by
  rw [lpsOriginalInfinityNormalizationSpecPoint_heightOneCentre]
  exact lpsOriginalInfinityStalkMeromorphicValuationRingEquiv N hpos hN x h
def lpsOriginalNormalizationCurveLocalRingEquiv_infinity
    (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (((algebraMap J K).comp lpsOriginalCanonicalComplexPolynomialFractionMap) Polynomial.X)⁻¹) :
    (lpsOriginalComplexNormalGluedScheme N hpos).presheaf.stalk
      ((lpsOriginalNormalizationCurveSpecPoint N hpos hN x).base
        (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)) ≃+*
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring := by
  rw [lpsOriginalNormalizationCurveSpecPoint_infinity N hpos hN x h]
  letI : _root_.AlgebraicGeometry.IsOpenImmersion
      (lpsOriginalComplexNormalGluedChartMap N hpos true) :=
    lpsOriginalComplexNormalGluedChartMap_openImmersion N hpos true
  exact (CategoryTheory.asIso
    ((lpsOriginalComplexNormalGluedChartMap N hpos true).stalkMap
      ((lpsOriginalInfinityNormalizationSpecPoint N hpos hN x h).base
        (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)))).commRingCatIsoToRingEquiv.trans
      (lpsOriginalInfinityNormalizationPointLocalRingEquiv N hpos hN x h)
end InfinityModel
def lpsOriginalNormalizationCurveLocalRingEquiv
    (x : LPSOriginalFilledCurve N) :
    (lpsOriginalComplexNormalGluedScheme N hpos).presheaf.stalk
      ((lpsOriginalNormalizationCurveSpecPoint N hpos hN x).base
        (⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ)) ≃+*
      (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x)).valuationSubring := by
  classical
  by_cases hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)
  · exact lpsOriginalNormalizationCurveLocalRingEquiv_zero N hpos hN x hj
  · exact lpsOriginalNormalizationCurveLocalRingEquiv_infinity N hpos hN x
      ((lpsOriginalNormalizationChart_order_cover N hpos hN x).resolve_left hj)
end
end QEC.Coding.TannerLiftedProduct


