-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T05:56:17.265013+00:00
-- url     : https://prove2.me/theorems/7cef7ad0-5b4b-4b29-bed0-edf2cb199be1
-- title:
--   LPSOriginal Reciprocal Normalization Comparison
-- statement:
--   Definitions and structural lemmas for LPSOriginal Reciprocal Normalization Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalNormalizationComparison.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
import Theorems.Thm_QEC_Coding_IntegralClosureScalarExtension_BaseRing_fieldTensorIntegralClosureHom_bijective_of_isLocalization
import Theorems.Thm_QEC_Coding_IntegralClosureScalarExtension_BaseRing_fieldTensorIntegralClosureHom_val
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_finiteDimensional
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finiteDimensional
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionInversion_involutive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.OriginalNormalizationComparison.IntegralBasis
noncomputable section
variable {R K E ι : Type*} [CommRing R] [IsDomain R] [Field K] [Field E]
  [Algebra R K] [IsFractionRing R K] [Algebra R E] [Algebra K E] [IsScalarTower R K E]
  [FiniteDimensional K E]
lemma exists_integral_basis (b : Module.Basis ι K E) :
    ∃ b' : Module.Basis ι K E, ∀ i : ι, IsIntegral R (b' i) := by
  classical
  have ha (i : ι) : IsAlgebraic R (b i) :=
    (IsFractionRing.isAlgebraic_iff R K E).mpr (IsIntegral.of_finite K (b i)).isAlgebraic
  choose d hd hi using fun i => (ha i).exists_integral_multiple
  have hw (i : ι) : IsUnit (algebraMap R K (d i)) :=
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff (algebraMap R K)
      (IsFractionRing.injective R K)).mpr (hd i))
  refine ⟨b.isUnitSMul hw, fun i => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, IsScalarTower.algebraMap_smul]
  exact hi i
end
end QEC.Coding.OriginalNormalizationComparison.IntegralBasis
namespace QEC.Coding.OriginalNormalizationComparison.ReciprocalFraction
noncomputable section
variable (k : Type*) [Field k]
local notation "K" => FractionRing (Polynomial k)
def reciprocalPolynomialMap : Polynomial k →+* K :=
  (Polynomial.aeval ((algebraMap (Polynomial k) K Polynomial.X)⁻¹)).toRingHom
lemma reciprocalPolynomialMap_injective : Function.Injective (reciprocalPolynomialMap k) := by
  apply transcendental_iff_injective.mp
  have hx : Transcendental k (algebraMap (Polynomial k) K Polynomial.X) :=
    (transcendental_algebraMap_iff (IsFractionRing.injective (Polynomial k) K)).mpr
      (Polynomial.transcendental_X k)
  exact fun h => hx (IsAlgebraic.inv_iff.mp h)
def fractionInverse : K →+* K := IsFractionRing.lift (reciprocalPolynomialMap_injective k)
lemma fractionInverse_polynomial (p : Polynomial k) :
    fractionInverse k (algebraMap (Polynomial k) K p) = reciprocalPolynomialMap k p :=
  IsFractionRing.lift_algebraMap _ p
lemma fractionInverse_X : fractionInverse k (algebraMap (Polynomial k) K Polynomial.X) =
    (algebraMap (Polynomial k) K Polynomial.X)⁻¹ := by
  rw [fractionInverse_polynomial]
  exact Polynomial.aeval_X _
lemma fractionInverse_constant (c : k) :
    fractionInverse k (algebraMap k K c) = algebraMap k K c := by
  rw [IsScalarTower.algebraMap_apply k (Polynomial k) K]
  change fractionInverse k (algebraMap (Polynomial k) K (Polynomial.C c)) = _
  rw [fractionInverse_polynomial]
  exact (Polynomial.aeval _).commutes c
lemma fractionInverse_involutive : Function.Involutive (fractionInverse k) := by
  have h : (fractionInverse k).comp (fractionInverse k) = RingHom.id K := by
    apply IsFractionRing.ringHom_ext (A := Polynomial k)
    have hp : ((fractionInverse k).comp (fractionInverse k)).comp
        (algebraMap (Polynomial k) K) = algebraMap (Polynomial k) K := by
      apply Polynomial.ringHom_ext
      · intro c
        change fractionInverse k (fractionInverse k (algebraMap (Polynomial k) K (Polynomial.C c))) = _
        rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply k (Polynomial k) K,
          fractionInverse_constant, fractionInverse_constant]
      · change fractionInverse k (fractionInverse k (algebraMap (Polynomial k) K Polynomial.X)) = _
        rw [fractionInverse_X, map_inv₀, fractionInverse_X, inv_inv]
    intro p
    exact RingHom.congr_fun hp p
  intro x
  exact RingHom.congr_fun h x
def fractionInverseAlgEquiv : K ≃ₐ[k] K :=
  AlgEquiv.ofBijective
    { toRingHom := fractionInverse k, commutes' := fractionInverse_constant k }
    ⟨(fractionInverse_involutive k).injective, (fractionInverse_involutive k).surjective⟩
lemma reciprocal_isFractionRing :
    let : Algebra (Polynomial k) K :=
      ((fractionInverseAlgEquiv k).toRingHom.comp (algebraMap (Polynomial k) K)).toAlgebra
    IsFractionRing (Polynomial k) K :=
  (IsLocalization.isLocalization_iff_of_ringEquiv
    (M := nonZeroDivisors (Polynomial k)) (R := Polynomial k) (S := K)
    (fractionInverseAlgEquiv k).toRingEquiv).mp inferInstance
end
end QEC.Coding.OriginalNormalizationComparison.ReciprocalFraction
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
def lpsOriginalComplexJFractionInversion : JC →+* JC :=
  (QEC.Coding.OriginalNormalizationComparison.ReciprocalFraction.fractionInverseAlgEquiv ℂ).toRingHom
lemma lpsOriginalComplexJFractionInversion_X :
    lpsOriginalComplexJFractionInversion (algebraMap (Polynomial ℂ) JC Polynomial.X) =
      (algebraMap (Polynomial ℂ) JC Polynomial.X)⁻¹ :=
  QEC.Coding.OriginalNormalizationComparison.ReciprocalFraction.fractionInverse_X ℂ
lemma lpsOriginalJBaseQToC_reciprocal :
    lpsOriginalJBaseQToC.comp lpsOriginalJFractionInversion =
      lpsOriginalComplexJFractionInversion.comp lpsOriginalJBaseQToC := by
  apply IsFractionRing.ringHom_ext (A := Polynomial ℚ)
  have hp : (lpsOriginalJBaseQToC.comp lpsOriginalJFractionInversion).comp
      (algebraMap (Polynomial ℚ) JQ) =
      (lpsOriginalComplexJFractionInversion.comp lpsOriginalJBaseQToC).comp
        (algebraMap (Polynomial ℚ) JQ) := by
    apply Polynomial.ringHom_ext
    · intro q
      simp only [Polynomial.C_eq_algebraMap, RingHom.map_rat_algebraMap]
    · change lpsOriginalJBaseQToC
        (lpsOriginalJFractionInversion (algebraMap (Polynomial ℚ) JQ Polynomial.X)) =
        lpsOriginalComplexJFractionInversion
          (lpsOriginalJBaseQToC (algebraMap (Polynomial ℚ) JQ Polynomial.X))
      simp only [lpsOriginalJFractionInversion_X, map_inv₀,
        lpsOriginalJBaseQToC_polynomial, Polynomial.map_X,
        lpsOriginalComplexJFractionInversion_X]
  intro p
  exact RingHom.congr_fun hp p
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
abbrev lpsOriginalCanonicalRationalPolynomialFractionMap : Polynomial ℚ →+* JQ :=
  algebraMap (Polynomial ℚ) JQ
abbrev lpsOriginalCanonicalComplexPolynomialFractionMap : Polynomial ℂ →+* JC :=
  algebraMap (Polynomial ℂ) JC
def lpsOriginalRationalJFractionInversionRingEquiv : JQ ≃+* JQ :=
  RingEquiv.ofBijective lpsOriginalJFractionInversion
    ⟨lpsOriginalJFractionInversion_involutive.injective,
      lpsOriginalJFractionInversion_involutive.surjective⟩
abbrev lpsOriginalReciprocalBaseQAlgebra : Algebra (Polynomial ℚ) JQ :=
  (lpsOriginalJFractionInversion.comp lpsOriginalCanonicalRationalPolynomialFractionMap).toAlgebra
abbrev lpsOriginalReciprocalBaseCAlgebra : Algebra (Polynomial ℂ) JC :=
  (lpsOriginalComplexJFractionInversion.comp
    lpsOriginalCanonicalComplexPolynomialFractionMap).toAlgebra
lemma lpsOriginalReciprocalBaseQ_isFractionRing :
    let : Algebra (Polynomial ℚ) JQ := lpsOriginalReciprocalBaseQAlgebra
    IsFractionRing (Polynomial ℚ) JQ :=
  (IsLocalization.isLocalization_iff_of_ringEquiv
    (M := nonZeroDivisors (Polynomial ℚ)) (R := Polynomial ℚ) (S := JQ)
    lpsOriginalRationalJFractionInversionRingEquiv).mp inferInstance
lemma lpsOriginalReciprocalBaseC_isFractionRing :
    let : Algebra (Polynomial ℂ) JC := lpsOriginalReciprocalBaseCAlgebra
    IsFractionRing (Polynomial ℂ) JC :=
  QEC.Coding.OriginalNormalizationComparison.ReciprocalFraction.reciprocal_isFractionRing ℂ
lemma lpsOriginalComplexJFractionInversion_constant (c : ℂ) :
    lpsOriginalComplexJFractionInversion (algebraMap ℂ JC c) = algebraMap ℂ JC c :=
  QEC.Coding.OriginalNormalizationComparison.ReciprocalFraction.fractionInverse_constant ℂ c
local instance reciprocalNormalizationDictionary001 : Algebra (Polynomial ℚ) JQ := lpsOriginalReciprocalBaseQAlgebra
local instance reciprocalNormalizationDictionary002 : Algebra (Polynomial ℂ) JC := lpsOriginalReciprocalBaseCAlgebra
local instance reciprocalNormalizationDictionary003 : SMul (Polynomial ℚ) JQ := Algebra.toSMul
local instance reciprocalNormalizationDictionary004 : SMul (Polynomial ℂ) JC := Algebra.toSMul
local instance reciprocalNormalizationDictionary005 : Module (Polynomial ℚ) JQ := Algebra.toModule
local instance reciprocalNormalizationDictionary006 : Module (Polynomial ℂ) JC := Algebra.toModule
local instance reciprocalNormalizationDictionary007 : IsFractionRing (Polynomial ℚ) JQ := lpsOriginalReciprocalBaseQ_isFractionRing
local instance reciprocalNormalizationDictionary008 : IsFractionRing (Polynomial ℂ) JC := lpsOriginalReciprocalBaseC_isFractionRing
local instance reciprocalNormalizationDictionary009 : Algebra JQ JC := lpsOriginalJBaseQToC.toAlgebra
local instance reciprocalNormalizationDictionary010 : Algebra JC LPSOriginalHolomorphicFractionField := lpsOriginalJFractionEmbedding.toAlgebra
local instance reciprocalNormalizationDictionary011 : Algebra JQ LPSOriginalHolomorphicFractionField := lpsOriginalJFractionEmbeddingQ.toAlgebra
local instance reciprocalNormalizationDictionary012 : IsScalarTower JQ JC LPSOriginalHolomorphicFractionField := lpsOriginalJBaseQToC_actualTower
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
def lpsOriginalReciprocalRationalFieldPolynomialMap : Polynomial ℚ →+* FQ :=
  (algebraMap JQ FQ).comp (algebraMap (Polynomial ℚ) JQ)
def lpsOriginalReciprocalComplexFieldPolynomialMap : Polynomial ℂ →+* FC :=
  (algebraMap JC FC).comp (algebraMap (Polynomial ℂ) JC)
local instance reciprocalNormalizationDictionary013 : Algebra (Polynomial ℚ) FQ := (lpsOriginalReciprocalRationalFieldPolynomialMap N hN).toAlgebra
local instance reciprocalNormalizationDictionary014 : Algebra (Polynomial ℂ) FC := (lpsOriginalReciprocalComplexFieldPolynomialMap N hN).toAlgebra
local instance reciprocalNormalizationDictionary015 : IsScalarTower (Polynomial ℚ) JQ FQ := .of_algebraMap_eq' rfl
local instance reciprocalNormalizationDictionary016 : IsScalarTower (Polynomial ℂ) JC FC := .of_algebraMap_eq' rfl
local instance reciprocalNormalizationDictionary017 : IsScalarTower ℚ (Polynomial ℚ) FQ := by infer_instance
local instance reciprocalNormalizationDictionary018 : Algebra ℂ FC := ((algebraMap JC FC).comp (algebraMap ℂ JC)).toAlgebra
local instance reciprocalNormalizationDictionary019 : IsScalarTower ℂ JC FC := .of_algebraMap_eq' rfl
local instance reciprocalNormalizationDictionary020 : IsScalarTower ℂ (Polynomial ℂ) FC :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := Polynomial ℂ) (A := FC) fun c => by
    change algebraMap JC FC (algebraMap ℂ JC c) =
      algebraMap JC FC (lpsOriginalComplexJFractionInversion (algebraMap ℂ JC c))
    rw [lpsOriginalComplexJFractionInversion_constant]
local instance reciprocalNormalizationDictionary021 : FiniteDimensional JQ FQ := lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hN
local instance reciprocalNormalizationDictionary022 : FiniteDimensional JC FC := lpsOriginalGeneratedFunctionField_finiteDimensional N hN
local instance reciprocalNormalizationDictionary023 : Algebra.IsIntegral JQ FQ := ⟨fun x => IsIntegral.of_finite JQ x⟩
local instance reciprocalNormalizationDictionary024 : Algebra.IsIntegral JC FC := ⟨fun x => IsIntegral.of_finite JC x⟩
local instance reciprocalNormalizationDictionary025 : Algebra.IsSeparable JQ FQ := Algebra.IsSeparable.of_integral JQ FQ
local instance reciprocalNormalizationDictionary026 : Algebra.IsSeparable JC FC := Algebra.IsSeparable.of_integral JC FC
omit [NeZero N] in
lemma lpsOriginalReciprocalPolynomialSquare :
    (lpsOriginalGeneratedQToComplex N hN).toRingHom.comp
      (lpsOriginalReciprocalRationalFieldPolynomialMap N hN) =
      (lpsOriginalReciprocalComplexFieldPolynomialMap N hN).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ)) := by
  apply RingHom.ext
  intro p
  change lpsOriginalGeneratedQToComplex N hN
    (algebraMap JQ FQ (lpsOriginalJFractionInversion
      (lpsOriginalCanonicalRationalPolynomialFractionMap p))) =
    algebraMap JC FC (lpsOriginalComplexJFractionInversion
      (lpsOriginalCanonicalComplexPolynomialFractionMap (p.map (algebraMap ℚ ℂ))))
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply JQ JC FC]
  change algebraMap JC FC (lpsOriginalJBaseQToC
    (lpsOriginalJFractionInversion (lpsOriginalCanonicalRationalPolynomialFractionMap p))) = _
  have h := RingHom.congr_fun lpsOriginalJBaseQToC_reciprocal
    (lpsOriginalCanonicalRationalPolynomialFractionMap p)
  change lpsOriginalJBaseQToC
    (lpsOriginalJFractionInversion (lpsOriginalCanonicalRationalPolynomialFractionMap p)) =
    lpsOriginalComplexJFractionInversion
      (lpsOriginalJBaseQToC (lpsOriginalCanonicalRationalPolynomialFractionMap p)) at h
  rw [h, lpsOriginalJBaseQToC_polynomial]
lemma lpsOriginalRationalReciprocal_integralBasisExists :
    ∃ b : Module.Basis (Fin (lpsOriginalRationalPowerBasis N hN).dim) JQ FQ,
      ∀ i, IsIntegral (Polynomial ℚ) (b i) :=
  QEC.Coding.OriginalNormalizationComparison.IntegralBasis.exists_integral_basis
    (R := Polynomial ℚ) (lpsOriginalRationalPowerBasis N hN).basis
def lpsOriginalRationalReciprocalIntegralBasis :
    Module.Basis (Fin (lpsOriginalRationalPowerBasis N hN).dim) JQ FQ :=
  Classical.choose (lpsOriginalRationalReciprocal_integralBasisExists N hN)
lemma lpsOriginalRationalReciprocalIntegralBasis_integral
    (i : Fin (lpsOriginalRationalPowerBasis N hN).dim) :
    IsIntegral (Polynomial ℚ) (lpsOriginalRationalReciprocalIntegralBasis N hN i) :=
  Classical.choose_spec (lpsOriginalRationalReciprocal_integralBasisExists N hN) i
def lpsOriginalComplexReciprocalIntegralBasis :
    Module.Basis (Fin (lpsOriginalRationalPowerBasis N hN).dim) JC FC :=
  (Algebra.TensorProduct.basis JC (lpsOriginalRationalReciprocalIntegralBasis N hN)).map
    (lpsOriginalRationalComplexTensorEquiv N hN).toLinearEquiv
lemma lpsOriginalComplexReciprocalIntegralBasis_integral
    (i : Fin (lpsOriginalRationalPowerBasis N hN).dim) :
    IsIntegral (Polynomial ℂ) (lpsOriginalComplexReciprocalIntegralBasis N hN i) := by
  rw [lpsOriginalComplexReciprocalIntegralBasis, Module.Basis.map_apply,
    Algebra.TensorProduct.basis_apply]
  change IsIntegral (Polynomial ℂ) (lpsOriginalRationalComplexTensorMap N hN
    ((1 : JC) ⊗ₜ[JQ] lpsOriginalRationalReciprocalIntegralBasis N hN i))
  rw [lpsOriginalRationalComplexTensorMap_tmul, one_smul]
  have hi : (lpsOriginalReciprocalRationalFieldPolynomialMap N hN).IsIntegralElem
      (lpsOriginalRationalReciprocalIntegralBasis N hN i) :=
    lpsOriginalRationalReciprocalIntegralBasis_integral N hN i
  have hm := hi.map (lpsOriginalGeneratedQToComplex N hN).toRingHom
  rw [lpsOriginalReciprocalPolynomialSquare] at hm
  exact hm.of_comp
lemma lpsOriginalComplexReciprocalIntegralTraceCoordinates
    (x : FC) (hx : IsIntegral (Polynomial ℂ) x) :
    ∃ c : Fin (lpsOriginalRationalPowerBasis N hN).dim → Polynomial ℂ,
      x = ∑ i, algebraMap (Polynomial ℂ) FC (c i) *
        lpsOriginalGeneratedQToComplex N hN
          ((lpsOriginalRationalReciprocalIntegralBasis N hN).traceDual i) := by
  obtain ⟨c, hc⟩ := QEC.Coding.OriginalNormalizationComparison.TraceComparison.integral_traceDual_coefficients
    (lpsOriginalComplexReciprocalIntegralBasis N hN)
    (lpsOriginalComplexReciprocalIntegralBasis_integral N hN) x hx
  have hd := QEC.Coding.OriginalNormalizationComparison.TraceComparison.traceDual_tensor_equiv
    (lpsOriginalRationalReciprocalIntegralBasis N hN)
    (lpsOriginalRationalComplexTensorEquiv N hN)
  have hdi (i : Fin (lpsOriginalRationalPowerBasis N hN).dim) :
      (lpsOriginalComplexReciprocalIntegralBasis N hN).traceDual i =
        lpsOriginalGeneratedQToComplex N hN
          ((lpsOriginalRationalReciprocalIntegralBasis N hN).traceDual i) := by
    have h := congrFun hd i
    change (lpsOriginalComplexReciprocalIntegralBasis N hN).traceDual i =
      lpsOriginalRationalComplexTensorMap N hN
        ((1 : JC) ⊗ₜ[JQ] (lpsOriginalRationalReciprocalIntegralBasis N hN).traceDual i) at h
    rw [lpsOriginalRationalComplexTensorMap_tmul, one_smul] at h
    exact h
  refine ⟨c, ?_⟩
  simpa only [hdi] using hc
omit [NeZero N] in
lemma lpsOriginalConstantTensorMap_reciprocalJ :
    lpsOriginalConstantTensorMap N hN
      ((1 : ℂ) ⊗ₜ[ℚ] (lpsOriginalRationalJElement N hN)⁻¹) =
      algebraMap (Polynomial ℂ) FC Polynomial.X := by
  rw [lpsOriginalConstantTensorMap_tmul, map_one, one_mul]
  change lpsOriginalGeneratedQToComplex N hN
      (algebraMap JQ FQ (lpsOriginalCanonicalRationalPolynomialFractionMap Polynomial.X))⁻¹ =
    algebraMap JC FC (lpsOriginalComplexJFractionInversion
      (lpsOriginalCanonicalComplexPolynomialFractionMap Polynomial.X))
  rw [map_inv₀, AlgHom.commutes, IsScalarTower.algebraMap_apply JQ JC FC]
  change (algebraMap JC FC (lpsOriginalJBaseQToC
    (lpsOriginalCanonicalRationalPolynomialFractionMap Polynomial.X)))⁻¹ = _
  rw [lpsOriginalJBaseQToC_polynomial, Polynomial.map_X,
    lpsOriginalComplexJFractionInversion_X, map_inv₀]
omit [NeZero N] in
lemma lpsOriginalConstantTensorMap_reciprocalPolynomial (p : Polynomial ℂ) :
    lpsOriginalConstantTensorMap N hN
      (Polynomial.aeval ((1 : ℂ) ⊗ₜ[ℚ] (lpsOriginalRationalJElement N hN)⁻¹) p) =
      algebraMap (Polynomial ℂ) FC p := by
  let π : Polynomial ℂ →ₐ[ℂ] FC := IsScalarTower.toAlgHom ℂ (Polynomial ℂ) FC
  rw [← Polynomial.aeval_algHom_apply, lpsOriginalConstantTensorMap_reciprocalJ]
  change Polynomial.aeval (π Polynomial.X) p = π p
  rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_X_left_apply]
lemma lpsOriginalComplexReciprocalIntegral_constantTensorImage
    (x : FC) (hx : IsIntegral (Polynomial ℂ) x) :
    ∃ z : ℂ ⊗[ℚ] FQ, lpsOriginalConstantTensorMap N hN z = x := by
  obtain ⟨c, hc⟩ := lpsOriginalComplexReciprocalIntegralTraceCoordinates N hN x hx
  refine ⟨∑ i, Polynomial.aeval ((1 : ℂ) ⊗ₜ[ℚ] (lpsOriginalRationalJElement N hN)⁻¹) (c i) *
    ((1 : ℂ) ⊗ₜ[ℚ] (lpsOriginalRationalReciprocalIntegralBasis N hN).traceDual i), ?_⟩
  rw [map_sum]
  calc
    ∑ i, lpsOriginalConstantTensorMap N hN
      (Polynomial.aeval ((1 : ℂ) ⊗ₜ[ℚ] (lpsOriginalRationalJElement N hN)⁻¹) (c i) *
        ((1 : ℂ) ⊗ₜ[ℚ] (lpsOriginalRationalReciprocalIntegralBasis N hN).traceDual i)) =
      ∑ i, algebraMap (Polynomial ℂ) FC (c i) *
        lpsOriginalGeneratedQToComplex N hN
          ((lpsOriginalRationalReciprocalIntegralBasis N hN).traceDual i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, lpsOriginalConstantTensorMap_reciprocalPolynomial,
        lpsOriginalConstantTensorMap_tmul, map_one, one_mul]
    _ = x := hc.symm
local notation "BP" => ℂ ⊗[ℚ] Polynomial ℚ
local notation "TB" => ℂ ⊗[ℚ] FQ
local instance reciprocalNormalizationDictionary027 : IsScalarTower ℚ ℂ FC := .of_algebraMap_eq fun q =>
  (RingHom.map_rat_algebraMap (algebraMap ℂ FC) q).symm
local instance reciprocalNormalizationDictionary028 : Algebra BP TB :=
  (Algebra.TensorProduct.map (AlgHom.id ℂ ℂ)
    (IsScalarTower.toAlgHom ℚ (Polynomial ℚ) FQ)).toAlgebra
omit [NeZero N] in
lemma lpsOriginalConstantTensorMap_reciprocalPolynomialSquare :
    (lpsOriginalConstantTensorMap N hN).toRingHom.comp (algebraMap BP TB) =
      (algebraMap (Polynomial ℂ) FC).comp
        QEC.Coding.OriginalNormalizationComparison.ConstantAmbient.complexPolynomialTensorEquiv.toRingHom := by
  apply RingHom.ext
  intro z
  change lpsOriginalConstantTensorMap N hN (algebraMap BP TB z) =
    algebraMap (Polynomial ℂ) FC
      (QEC.Coding.OriginalNormalizationComparison.ConstantAmbient.complexPolynomialTensorEquiv z)
  induction z with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c p =>
    change lpsOriginalConstantTensorMap N hN (c ⊗ₜ[ℚ] algebraMap (Polynomial ℚ) FQ p) = _
    rw [lpsOriginalConstantTensorMap_tmul,
      QEC.Coding.OriginalNormalizationComparison.ConstantAmbient.complexPolynomialTensorEquiv_tmul,
      Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) FC]
    have hp : lpsOriginalGeneratedQToComplex N hN (algebraMap (Polynomial ℚ) FQ p) =
        algebraMap (Polynomial ℂ) FC (p.map (algebraMap ℚ ℂ)) :=
      RingHom.congr_fun (lpsOriginalReciprocalPolynomialSquare N hN) p
    rw [hp]
def lpsOriginalComplexReciprocalNormalizationTensorEquiv :
    ℂ ⊗[ℚ] integralClosure (Polynomial ℚ) FQ ≃+* integralClosure (Polynomial ℂ) FC :=
  (QEC.Coding.IntegralClosureScalarExtension.charZeroFieldTensorIntegralClosureEquiv
    (k := ℚ) (L := ℂ) (B := FQ) (Polynomial ℚ)).trans
      (QEC.Coding.OriginalNormalizationComparison.IntegralEmbedding.integralClosureEmbeddingEquiv
        QEC.Coding.OriginalNormalizationComparison.ConstantAmbient.complexPolynomialTensorEquiv.toRingEquiv
        (lpsOriginalConstantTensorMap N hN).toRingHom
        (lpsOriginalConstantTensorMap_injective N hN)
        (lpsOriginalConstantTensorMap_reciprocalPolynomialSquare N hN)
        (lpsOriginalComplexReciprocalIntegral_constantTensorImage N hN))
lemma lpsOriginalComplexReciprocalNormalizationTensorEquiv_value
    (z : ℂ ⊗[ℚ] integralClosure (Polynomial ℚ) FQ) :
    (lpsOriginalComplexReciprocalNormalizationTensorEquiv N hN z).val =
      lpsOriginalConstantTensorMap N hN
        (Algebra.TensorProduct.map (AlgHom.id ℂ ℂ)
          ((integralClosure (Polynomial ℚ) FQ).val.restrictScalars ℚ) z) := by
  change lpsOriginalConstantTensorMap N hN
    ((QEC.Coding.IntegralClosureScalarExtension.fieldTensorIntegralClosureHom
      (k := ℚ) (L := ℂ) (B := FQ) (Polynomial ℚ) z).val) = _
  rw [QEC.Coding.IntegralClosureScalarExtension.fieldTensorIntegralClosureHom_val]
  congr 1
lemma lpsOriginalComplexReciprocalNormalizationTensorEquiv_tmulValue
    (c : ℂ) (x : integralClosure (Polynomial ℚ) FQ) :
    (lpsOriginalComplexReciprocalNormalizationTensorEquiv N hN (c ⊗ₜ[ℚ] x)).val =
      algebraMap ℂ FC c * lpsOriginalGeneratedQToComplex N hN x.val := by
  rw [lpsOriginalComplexReciprocalNormalizationTensorEquiv_value]
  change lpsOriginalConstantTensorMap N hN (c ⊗ₜ[ℚ] x.val) = _
  exact lpsOriginalConstantTensorMap_tmul N hN c x.val
local instance reciprocalNormalizationDictionary029 : Algebra ℂ (integralClosure (Polynomial ℂ) FC) :=
  ((integralClosure (Polynomial ℂ) FC).restrictScalars ℂ).algebra
def lpsOriginalComplexReciprocalNormalizationTensorAlgEquiv :
    ℂ ⊗[ℚ] integralClosure (Polynomial ℚ) FQ ≃ₐ[ℂ] integralClosure (Polynomial ℂ) FC where
  toRingEquiv := lpsOriginalComplexReciprocalNormalizationTensorEquiv N hN
  commutes' c := by
    apply Subtype.ext
    change (lpsOriginalComplexReciprocalNormalizationTensorEquiv N hN
      (c ⊗ₜ[ℚ] (1 : integralClosure (Polynomial ℚ) FQ))).val = algebraMap ℂ FC c
    rw [lpsOriginalComplexReciprocalNormalizationTensorEquiv_tmulValue]
    change algebraMap ℂ FC c * lpsOriginalGeneratedQToComplex N hN (1 : FQ) = algebraMap ℂ FC c
    rw [map_one, mul_one]
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
local instance reciprocalNormalizationDictionary030 : Algebra (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbeddingQ.toAlgebra
variable (N : ℕ) (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "BP" => ℚ ⊗[ℤ] Polynomial ℤ
local notation "TB" => ℚ ⊗[ℤ] FQ
local instance reciprocalNormalizationDictionary031 : Algebra (Polynomial ℤ) FQ := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
local instance reciprocalNormalizationDictionary032 : IsScalarTower ℤ (Polynomial ℤ) FQ := by infer_instance
local instance reciprocalNormalizationDictionary033 : Algebra (Polynomial ℚ) JQ := lpsOriginalReciprocalBaseQAlgebra
local instance reciprocalNormalizationDictionary034 : SMul (Polynomial ℚ) JQ := Algebra.toSMul
local instance reciprocalNormalizationDictionary035 : Module (Polynomial ℚ) JQ := Algebra.toModule
local instance reciprocalNormalizationDictionary036 : Algebra (Polynomial ℚ) FQ :=
  (lpsOriginalReciprocalRationalFieldPolynomialMap N hN).toAlgebra
local instance reciprocalNormalizationDictionary037 : IsScalarTower (Polynomial ℚ) JQ FQ := .of_algebraMap_eq' rfl
local instance reciprocalNormalizationDictionary038 : IsScalarTower ℚ (Polynomial ℚ) FQ := by infer_instance
local instance reciprocalNormalizationDictionary039 : Algebra BP TB :=
  (Algebra.TensorProduct.map (AlgHom.id ℚ ℚ)
    (IsScalarTower.toAlgHom ℤ (Polynomial ℤ) FQ)).toAlgebra
lemma lpsOriginalRationalConstantTensorCollapse_reciprocalPolynomialSquare :
    (lpsOriginalRationalConstantTensorCollapse N hN).toRingHom.comp (algebraMap BP TB) =
      (algebraMap (Polynomial ℚ) FQ).comp
        (QEC.Coding.OriginalNormalizationComparison.ScalarPolynomial.polynomialTensorEquiv ℤ ℚ).toRingHom := by
  apply RingHom.ext
  intro z
  change lpsOriginalRationalConstantTensorCollapse N hN (algebraMap BP TB z) =
    algebraMap (Polynomial ℚ) FQ (QEC.Coding.OriginalNormalizationComparison.ScalarPolynomial.polynomialTensorEquiv ℤ ℚ z)
  induction z with
  | zero => simp only [map_zero]
  | add x y hx hy =>
    have hf := ((lpsOriginalRationalConstantTensorCollapse N hN).toRingHom.comp
      (algebraMap BP TB)).map_add x y
    have hg := ((algebraMap (Polynomial ℚ) FQ).comp
      (QEC.Coding.OriginalNormalizationComparison.ScalarPolynomial.polynomialTensorEquiv ℤ ℚ).toRingHom).map_add x y
    exact hf.trans ((congrArg₂ (· + ·) hx hy).trans hg.symm)
  | tmul q p =>
    change lpsOriginalRationalConstantTensorCollapse N hN
      (q ⊗ₜ[ℤ] algebraMap (Polynomial ℤ) FQ p) = _
    rw [lpsOriginalRationalConstantTensorCollapse_tmul,
      QEC.Coding.OriginalNormalizationComparison.ScalarPolynomial.polynomialTensorEquiv_tmul,
      Algebra.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) FQ]
    rfl
def lpsOriginalIntegerInfinityNormalizationRationalTensorEquiv :
    ℚ ⊗[ℤ] integralClosure (Polynomial ℤ) FQ ≃+* integralClosure (Polynomial ℚ) FQ :=
  (RingEquiv.ofBijective
    (QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldTensorIntegralClosureHom
      (K := ℤ) (F := ℚ) (B0 := FQ) (Polynomial ℤ))
    (QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldTensorIntegralClosureHom_bijective_of_isLocalization
      (K := ℤ) (F := ℚ) (B0 := FQ) (nonZeroDivisors ℤ) (Polynomial ℤ))).trans
      (QEC.Coding.IntegralClosureScalarExtension.BaseRing.integralClosureTransportEquiv
        (QEC.Coding.OriginalNormalizationComparison.ScalarPolynomial.polynomialTensorEquiv ℤ ℚ).toRingEquiv
        (lpsOriginalRationalConstantTensorCollapse N hN).toRingEquiv
        (lpsOriginalRationalConstantTensorCollapse_reciprocalPolynomialSquare N hN))
lemma lpsOriginalIntegerInfinityNormalizationRationalTensorEquiv_value
    (z : ℚ ⊗[ℤ] integralClosure (Polynomial ℤ) FQ) :
    (lpsOriginalIntegerInfinityNormalizationRationalTensorEquiv N hN z).val =
      lpsOriginalRationalConstantTensorCollapse N hN
        (Algebra.TensorProduct.map (AlgHom.id ℚ ℚ)
          ((integralClosure (Polynomial ℤ) FQ).val.restrictScalars ℤ) z) := by
  change lpsOriginalRationalConstantTensorCollapse N hN
    ((QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldTensorIntegralClosureHom
      (K := ℤ) (F := ℚ) (B0 := FQ) (Polynomial ℤ) z).val) = _
  rw [QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldTensorIntegralClosureHom_val]
  congr 1
lemma lpsOriginalIntegerInfinityNormalizationRationalTensorEquiv_tmulValue
    (q : ℚ) (x : integralClosure (Polynomial ℤ) FQ) :
    (lpsOriginalIntegerInfinityNormalizationRationalTensorEquiv N hN (q ⊗ₜ[ℤ] x)).val =
      q • x.val := by
  rw [lpsOriginalIntegerInfinityNormalizationRationalTensorEquiv_value]
  change lpsOriginalRationalConstantTensorCollapse N hN (q ⊗ₜ[ℤ] x.val) = _
  exact lpsOriginalRationalConstantTensorCollapse_tmul N hN q x.val
local instance reciprocalNormalizationDictionary040 : Algebra ℚ (integralClosure (Polynomial ℚ) FQ) :=
  ((integralClosure (Polynomial ℚ) FQ).restrictScalars ℚ).algebra
def lpsOriginalIntegerInfinityNormalizationRationalTensorAlgEquiv :
    ℚ ⊗[ℤ] integralClosure (Polynomial ℤ) FQ ≃ₐ[ℚ] integralClosure (Polynomial ℚ) FQ where
  toRingEquiv := lpsOriginalIntegerInfinityNormalizationRationalTensorEquiv N hN
  commutes' q := by
    apply Subtype.ext
    change (lpsOriginalIntegerInfinityNormalizationRationalTensorEquiv N hN
      (q ⊗ₜ[ℤ] (1 : integralClosure (Polynomial ℤ) FQ))).val = algebraMap ℚ FQ q
    rw [lpsOriginalIntegerInfinityNormalizationRationalTensorEquiv_tmulValue]
    change q • (1 : FQ) = algebraMap ℚ FQ q
    rw [Algebra.smul_def, mul_one]
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
local instance reciprocalNormalizationDictionary041 : Algebra (FractionRing (Polynomial ℚ)) (FractionRing (Polynomial ℂ)) :=
  lpsOriginalJBaseQToC.toAlgebra
local instance reciprocalNormalizationDictionary042 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local instance reciprocalNormalizationDictionary043 : Algebra (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbeddingQ.toAlgebra
local instance reciprocalNormalizationDictionary044 : IsScalarTower (FractionRing (Polynomial ℚ))
    (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJBaseQToC_actualTower
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
local instance reciprocalNormalizationDictionary045 : Algebra (Polynomial ℤ) FQ := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
local instance reciprocalNormalizationDictionary046 : IsScalarTower ℤ (Polynomial ℤ) FQ := by infer_instance
local instance reciprocalNormalizationDictionary047 : Algebra (Polynomial ℚ) JQ := lpsOriginalReciprocalBaseQAlgebra
local instance reciprocalNormalizationDictionary048 : Algebra (Polynomial ℂ) JC := lpsOriginalReciprocalBaseCAlgebra
local instance reciprocalNormalizationDictionary049 : SMul (Polynomial ℚ) JQ := Algebra.toSMul
local instance reciprocalNormalizationDictionary050 : SMul (Polynomial ℂ) JC := Algebra.toSMul
local instance reciprocalNormalizationDictionary051 : Module (Polynomial ℚ) JQ := Algebra.toModule
local instance reciprocalNormalizationDictionary052 : Module (Polynomial ℂ) JC := Algebra.toModule
local instance reciprocalNormalizationDictionary053 : Algebra (Polynomial ℚ) FQ :=
  (lpsOriginalReciprocalRationalFieldPolynomialMap N hN).toAlgebra
local instance reciprocalNormalizationDictionary054 : IsScalarTower ℚ (Polynomial ℚ) FQ := by infer_instance
local instance reciprocalNormalizationDictionary055 : Algebra (Polynomial ℂ) FC :=
  (lpsOriginalReciprocalComplexFieldPolynomialMap N hN).toAlgebra
local instance reciprocalNormalizationDictionary056 : IsScalarTower (Polynomial ℂ) JC FC := .of_algebraMap_eq' rfl
local instance reciprocalNormalizationDictionary057 : Algebra ℂ FC := ((algebraMap JC FC).comp (algebraMap ℂ JC)).toAlgebra
local instance reciprocalNormalizationDictionary058 : IsScalarTower ℂ JC FC := .of_algebraMap_eq' rfl
local instance reciprocalNormalizationDictionary059 : IsScalarTower ℂ (Polynomial ℂ) FC :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := Polynomial ℂ) (A := FC) fun c => by
    change algebraMap JC FC (algebraMap ℂ JC c) =
      algebraMap JC FC (lpsOriginalComplexJFractionInversion (algebraMap ℂ JC c))
    rw [lpsOriginalComplexJFractionInversion_constant]
local notation "IZ" => integralClosure (Polynomial ℤ) FQ
local notation "IQ" => integralClosure (Polynomial ℚ) FQ
local notation "IC" => integralClosure (Polynomial ℂ) FC
local instance reciprocalNormalizationDictionary060 : Algebra ℚ IQ := ((integralClosure (Polynomial ℚ) FQ).restrictScalars ℚ).algebra
local instance reciprocalNormalizationDictionary061 : Algebra ℂ IC := ((integralClosure (Polynomial ℂ) FC).restrictScalars ℂ).algebra
def lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv :
    ℂ ⊗[ℤ] lpsOriginalIntegerNormalInfinityChart N hN ≃ₐ[ℂ] IC := by
  change ℂ ⊗[ℤ] IZ ≃ₐ[ℂ] IC
  exact (Algebra.TensorProduct.cancelBaseChange ℤ ℚ ℂ ℂ IZ).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := ℂ) (A₁ := ℂ))
      (lpsOriginalIntegerInfinityNormalizationRationalTensorAlgEquiv N hN)).trans
        (lpsOriginalComplexReciprocalNormalizationTensorAlgEquiv N hN))
end
end QEC.Coding.TannerLiftedProduct


