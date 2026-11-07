-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalZeroNormalizationComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T05:30:45.096708+00:00
-- url     : https://prove2.me/theorems/9839ad53-9bcc-4c8f-a5fb-d5a34e90782d
-- title:
--   LPSOriginal Zero Normalization Comparison
-- statement:
--   Definitions and structural lemmas for LPSOriginal Zero Normalization Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalZeroNormalizationComparison.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureScalarExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbedding_polynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNHolomorphic_integral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integralQ
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
namespace QEC.Coding.OriginalNormalizationComparison.ScalarPolynomial
open scoped TensorProduct
noncomputable section
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
def polynomialTensorEquiv : S ⊗[R] Polynomial R ≃ₐ[S] Polynomial S :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R := S) (A₁ := S))
    (MvPolynomial.uniqueAlgEquiv R Unit).symm).trans
      ((MvPolynomial.algebraTensorAlgEquiv (σ := Unit) R S).trans
        (MvPolynomial.uniqueAlgEquiv S Unit))
lemma polynomialTensorEquiv_tmul (c : S) (p : Polynomial R) :
    polynomialTensorEquiv R S (c ⊗ₜ[R] p) = c • p.map (algebraMap R S) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, Polynomial.map_add, smul_add, hp, hq]
  | monomial n q =>
    change (MvPolynomial.uniqueAlgEquiv S Unit)
      ((MvPolynomial.algebraTensorAlgEquiv R S)
        (c ⊗ₜ[R] (MvPolynomial.uniqueAlgEquiv R Unit).symm (Polynomial.monomial n q))) = _
    rw [show (MvPolynomial.uniqueAlgEquiv R Unit).symm (Polynomial.monomial n q) =
      MvPolynomial.monomial (Finsupp.single () n) q from
        by simpa using (MvPolynomial.uniqueAlgEquiv_symm_monomial R
          (σ := Unit) (d := Finsupp.single () n) (r := q))]
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, map_smul,
      MvPolynomial.map_monomial, MvPolynomial.uniqueAlgEquiv_monomial,
      Polynomial.map_monomial]
    simp only [Finsupp.single_eq_same]
end
end QEC.Coding.OriginalNormalizationComparison.ScalarPolynomial
namespace QEC.Coding.OriginalNormalizationComparison
open scoped TensorProduct
noncomputable section
namespace TraceComparison
variable {K E A C : Type*} [Field K] [Field E] [Field A] [Field C]
  [Algebra K E] [Algebra K A] [Algebra A C] [FiniteDimensional K E]
lemma trace_tensor (x : E) :
    Algebra.trace A (A ⊗[K] E) ((1 : A) ⊗ₜ[K] x) =
      algebraMap K A (Algebra.trace K E x) := by
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul]
  exact LinearMap.trace_baseChange (Algebra.lmul K E x) A
lemma trace_tensor_equiv (e : A ⊗[K] E ≃ₐ[A] C) (x : E) :
    Algebra.trace A C (e ((1 : A) ⊗ₜ[K] x)) =
      algebraMap K A (Algebra.trace K E x) :=
  (Algebra.trace_eq_of_algEquiv e ((1 : A) ⊗ₜ[K] x)).trans (trace_tensor x)
lemma traceDual_tensor_equiv
    [Algebra.IsSeparable K E] [FiniteDimensional A C] [Algebra.IsSeparable A C]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K E) (e : A ⊗[K] E ≃ₐ[A] C) :
    ((Algebra.TensorProduct.basis A b).map e.toLinearEquiv).traceDual =
      fun i => e ((1 : A) ⊗ₜ[K] b.traceDual i) := by
  rw [Module.Basis.traceDual_eq_iff]
  intro i j
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, Algebra.traceForm_apply]
  change Algebra.trace A C
    ((e ((1 : A) ⊗ₜ[K] b.traceDual i)) * (e ((1 : A) ⊗ₜ[K] b j))) =
      if j = i then 1 else 0
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_tensor_equiv,
    Module.Basis.trace_traceDual_mul]
  split_ifs <;> simp only [map_one, map_zero]
lemma integral_traceDual_coefficients
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra R A] [IsFractionRing R A] [Algebra R C] [IsScalarTower R A C]
    [FiniteDimensional A C] [Algebra.IsSeparable A C]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A C) (hb : ∀ i, IsIntegral R (b i))
    (x : C) (hx : IsIntegral R x) :
    ∃ c : ι → R, x = ∑ i, algebraMap R C (c i) * b.traceDual i := by
  classical
  have hi (i : ι) : IsIntegral R (b.traceDual.repr x i) := by
    rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply]
    exact Algebra.isIntegral_trace (hx.mul (hb i))
  choose c hc using fun i => (IsIntegrallyClosed.isIntegral_iff (R := R) (K := A)).mp (hi i)
  refine ⟨c, ?_⟩
  symm
  calc
    ∑ i, algebraMap R C (c i) * b.traceDual i =
        ∑ i, (b.traceDual.repr x i) • b.traceDual i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hc i, Algebra.smul_def, ← IsScalarTower.algebraMap_apply R A C]
    _ = x := b.traceDual.sum_repr x
end TraceComparison
end
end QEC.Coding.OriginalNormalizationComparison
namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
local instance zeroNormalizationDictionary001 : Algebra (FractionRing (Polynomial ℚ)) (FractionRing (Polynomial ℂ)) :=
  lpsOriginalJBaseQToC.toAlgebra
local instance zeroNormalizationDictionary002 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local instance zeroNormalizationDictionary003 : Algebra (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbeddingQ.toAlgebra
local instance zeroNormalizationDictionary004 : IsScalarTower (FractionRing (Polynomial ℚ))
    (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJBaseQToC_actualTower
section ActualComplexNormalization
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
local instance zeroNormalizationDictionary005 : Algebra (Polynomial ℂ) FC :=
  ((algebraMap JC FC).comp (algebraMap (Polynomial ℂ) JC)).toAlgebra
local instance zeroNormalizationDictionary006 : IsScalarTower (Polynomial ℂ) JC FC := .of_algebraMap_eq' rfl
local instance zeroNormalizationDictionary007 : FiniteDimensional JQ FQ := lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hN
local instance zeroNormalizationDictionary008 : FiniteDimensional JC FC := lpsOriginalGeneratedFunctionField_finiteDimensional N hN
local instance zeroNormalizationDictionary009 : Algebra.IsIntegral JQ FQ := ⟨fun x => IsIntegral.of_finite JQ x⟩
local instance zeroNormalizationDictionary010 : Algebra.IsSeparable JQ FQ := Algebra.IsSeparable.of_integral JQ FQ
local instance zeroNormalizationDictionary011 : Algebra.IsIntegral JC FC := ⟨fun x => IsIntegral.of_finite JC x⟩
local instance zeroNormalizationDictionary012 : Algebra.IsSeparable JC FC := Algebra.IsSeparable.of_integral JC FC
def lpsOriginalComplexGeneratedGenerator : FC :=
  ⟨lpsOriginalJNInFractionField N hN,
    IntermediateField.subset_adjoin JC {lpsOriginalJNInFractionField N hN} (Set.mem_singleton _)⟩
lemma lpsOriginalComplexGeneratedGenerator_integralPolynomial :
    IsIntegral (Polynomial ℂ) (lpsOriginalComplexGeneratedGenerator N hN) := by
  let φ : Polynomial ℂ →+* FC := algebraMap (Polynomial ℂ) FC
  let ψ : FC →+* LPSOriginalHolomorphicFractionField :=
    (lpsOriginalGeneratedFunctionField N hN).val.toRingHom
  have hcomp : ψ.comp φ =
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEval.toRingHom := by
    apply RingHom.ext
    intro p
    exact lpsOriginalJFractionEmbedding_polynomial p
  apply RingHom.IsIntegralElem.of_map (g := ψ) (show Function.Injective ψ from Subtype.val_injective)
  rw [hcomp]
  exact (lpsOriginalJNHolomorphic_integral N hN).map
    (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
def lpsOriginalRationalPowerBasis : PowerBasis JQ FQ :=
  IntermediateField.adjoin.powerBasis (lpsOriginalJNInFractionField_integralQ N hN)
def lpsOriginalComplexTensorBasis :
    Module.Basis (Fin (lpsOriginalRationalPowerBasis N hN).dim) JC FC :=
  (Algebra.TensorProduct.basis JC (lpsOriginalRationalPowerBasis N hN).basis).map
    (lpsOriginalRationalComplexTensorEquiv N hN).toLinearEquiv
lemma lpsOriginalComplexTensorBasis_integralPolynomial
    (i : Fin (lpsOriginalRationalPowerBasis N hN).dim) :
    IsIntegral (Polynomial ℂ) (lpsOriginalComplexTensorBasis N hN i) := by
  have hα : lpsOriginalGeneratedQToComplex N hN (lpsOriginalRationalPowerBasis N hN).gen =
      lpsOriginalComplexGeneratedGenerator N hN := by
    apply Subtype.ext
    rfl
  rw [lpsOriginalComplexTensorBasis, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
  change IsIntegral (Polynomial ℂ)
    (lpsOriginalRationalComplexTensorMap N hN
      ((1 : JC) ⊗ₜ[JQ] (lpsOriginalRationalPowerBasis N hN).basis i))
  rw [lpsOriginalRationalComplexTensorMap_tmul, one_smul,
    (lpsOriginalRationalPowerBasis N hN).basis_eq_pow, map_pow, hα]
  exact (lpsOriginalComplexGeneratedGenerator_integralPolynomial N hN).pow i.val
lemma lpsOriginalComplexIntegralTraceCoordinates
    (x : FC) (hx : IsIntegral (Polynomial ℂ) x) :
    ∃ c : Fin (lpsOriginalRationalPowerBasis N hN).dim → Polynomial ℂ,
      x = ∑ i, algebraMap (Polynomial ℂ) FC (c i) *
        lpsOriginalGeneratedQToComplex N hN
          ((lpsOriginalRationalPowerBasis N hN).basis.traceDual i) := by
  obtain ⟨c, hc⟩ := QEC.Coding.OriginalNormalizationComparison.TraceComparison.integral_traceDual_coefficients
    (lpsOriginalComplexTensorBasis N hN)
    (lpsOriginalComplexTensorBasis_integralPolynomial N hN) x hx
  have hd := QEC.Coding.OriginalNormalizationComparison.TraceComparison.traceDual_tensor_equiv
    (lpsOriginalRationalPowerBasis N hN).basis (lpsOriginalRationalComplexTensorEquiv N hN)
  have hdi (i : Fin (lpsOriginalRationalPowerBasis N hN).dim) :
      (lpsOriginalComplexTensorBasis N hN).traceDual i =
        lpsOriginalGeneratedQToComplex N hN
          ((lpsOriginalRationalPowerBasis N hN).basis.traceDual i) := by
    have h := congrFun hd i
    change (lpsOriginalComplexTensorBasis N hN).traceDual i =
      lpsOriginalRationalComplexTensorMap N hN
        ((1 : JC) ⊗ₜ[JQ] (lpsOriginalRationalPowerBasis N hN).basis.traceDual i) at h
    rw [lpsOriginalRationalComplexTensorMap_tmul, one_smul] at h
    exact h
  refine ⟨c, ?_⟩
  simpa only [hdi] using hc
local instance zeroNormalizationDictionary013 : Algebra ℂ FC := ((algebraMap JC FC).comp (algebraMap ℂ JC)).toAlgebra
local instance zeroNormalizationDictionary014 : IsScalarTower ℂ JC FC := .of_algebraMap_eq' rfl
local instance zeroNormalizationDictionary015 : IsScalarTower ℚ ℂ FC := .of_algebraMap_eq fun q =>
  (RingHom.map_rat_algebraMap (algebraMap ℂ FC) q).symm
def lpsOriginalConstantTensorMap : ℂ ⊗[ℚ] FQ →ₐ[ℂ] FC :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ FC)
    (lpsOriginalGeneratedQToComplex N hN).toRingHom.toRatAlgHom (fun _ _ => Commute.all _ _)
omit [NeZero N] in
lemma lpsOriginalConstantTensorMap_tmul (c : ℂ) (x : FQ) :
    lpsOriginalConstantTensorMap N hN (c ⊗ₜ[ℚ] x) =
      algebraMap ℂ FC c * lpsOriginalGeneratedQToComplex N hN x := rfl
def lpsOriginalRationalJElement : FQ :=
  algebraMap JQ FQ (algebraMap (Polynomial ℚ) JQ Polynomial.X)
omit [NeZero N] in
lemma lpsOriginalConstantTensorMap_j :
    lpsOriginalConstantTensorMap N hN ((1 : ℂ) ⊗ₜ[ℚ] lpsOriginalRationalJElement N hN) =
      algebraMap (Polynomial ℂ) FC Polynomial.X := by
  rw [lpsOriginalConstantTensorMap_tmul, map_one, one_mul]
  change lpsOriginalGeneratedQToComplex N hN
    (algebraMap JQ FQ (algebraMap (Polynomial ℚ) JQ Polynomial.X)) =
      algebraMap JC FC (algebraMap (Polynomial ℂ) JC Polynomial.X)
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply JQ JC FC]
  change algebraMap JC FC
    (lpsOriginalJBaseQToC (algebraMap (Polynomial ℚ) JQ Polynomial.X)) = _
  rw [lpsOriginalJBaseQToC_polynomial, Polynomial.map_X]
local instance zeroNormalizationDictionary016 : IsScalarTower ℂ (Polynomial ℂ) FC := .of_algebraMap_eq fun c => by
  change algebraMap JC FC (algebraMap ℂ JC c) =
    algebraMap JC FC (algebraMap (Polynomial ℂ) JC (algebraMap ℂ (Polynomial ℂ) c))
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) JC]
omit [NeZero N] in
lemma lpsOriginalConstantTensorMap_polynomial (p : Polynomial ℂ) :
    lpsOriginalConstantTensorMap N hN
      (Polynomial.aeval ((1 : ℂ) ⊗ₜ[ℚ] lpsOriginalRationalJElement N hN) p) =
      algebraMap (Polynomial ℂ) FC p := by
  let π : Polynomial ℂ →ₐ[ℂ] FC := IsScalarTower.toAlgHom ℂ (Polynomial ℂ) FC
  rw [← Polynomial.aeval_algHom_apply, lpsOriginalConstantTensorMap_j]
  change Polynomial.aeval (π Polynomial.X) p = π p
  rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_X_left_apply]
lemma lpsOriginalComplexIntegral_constantTensorImage
    (x : FC) (hx : IsIntegral (Polynomial ℂ) x) :
    ∃ z : ℂ ⊗[ℚ] FQ, lpsOriginalConstantTensorMap N hN z = x := by
  obtain ⟨c, hc⟩ := lpsOriginalComplexIntegralTraceCoordinates N hN x hx
  refine ⟨∑ i, Polynomial.aeval ((1 : ℂ) ⊗ₜ[ℚ] lpsOriginalRationalJElement N hN) (c i) *
    ((1 : ℂ) ⊗ₜ[ℚ] (lpsOriginalRationalPowerBasis N hN).basis.traceDual i), ?_⟩
  rw [map_sum]
  calc
    ∑ i, lpsOriginalConstantTensorMap N hN
      (Polynomial.aeval ((1 : ℂ) ⊗ₜ[ℚ] lpsOriginalRationalJElement N hN) (c i) *
        ((1 : ℂ) ⊗ₜ[ℚ] (lpsOriginalRationalPowerBasis N hN).basis.traceDual i)) =
      ∑ i, algebraMap (Polynomial ℂ) FC (c i) *
        lpsOriginalGeneratedQToComplex N hN
          ((lpsOriginalRationalPowerBasis N hN).basis.traceDual i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, lpsOriginalConstantTensorMap_polynomial,
        lpsOriginalConstantTensorMap_tmul, map_one, one_mul]
    _ = x := hc.symm
end ActualComplexNormalization
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.OriginalNormalizationComparison.ConstantAmbient
open scoped TensorProduct
noncomputable section
def complexPolynomialTensorEquiv : ℂ ⊗[ℚ] Polynomial ℚ ≃ₐ[ℂ] Polynomial ℂ :=
  QEC.Coding.OriginalNormalizationComparison.ScalarPolynomial.polynomialTensorEquiv ℚ ℂ
lemma complexPolynomialTensorEquiv_tmul (c : ℂ) (p : Polynomial ℚ) :
    complexPolynomialTensorEquiv (c ⊗ₜ[ℚ] p) = c • p.map (algebraMap ℚ ℂ) :=
  QEC.Coding.OriginalNormalizationComparison.ScalarPolynomial.polynomialTensorEquiv_tmul ℚ ℂ c p
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "BP" => ℂ ⊗[ℚ] Polynomial ℚ
local notation "BQ" => ℂ ⊗[ℚ] JQ
open QEC.Coding.TannerLiftedProduct
local instance zeroNormalizationDictionary017 : Module ℚ JQ := Algebra.toModule
local instance zeroNormalizationDictionary018 : Module ℚ JC := Algebra.toModule
local instance zeroNormalizationDictionary019 : SMul ℚ JQ := (inferInstance : Algebra ℚ JQ).toSMul
local instance zeroNormalizationDictionary020 : SMul ℚ JC := (inferInstance : Algebra ℚ JC).toSMul
local instance zeroNormalizationDictionary021 : Module ℂ JC := Algebra.toModule
local instance zeroNormalizationDictionary022 : SMul ℂ JC := (inferInstance : Algebra ℂ JC).toSMul
local instance zeroNormalizationDictionary023 : IsScalarTower ℚ ℂ JC :=
  IsScalarTower.of_algebraMap_eq (R := ℚ) (S := ℂ) (A := JC) fun q =>
    (RingHom.map_rat_algebraMap (algebraMap ℂ JC) q).symm
local instance zeroNormalizationDictionary024 : Algebra JQ JC := lpsOriginalJBaseQToC.toAlgebra
def complexRationalTensorMap : BQ →ₐ[ℂ] JC :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ JC)
    lpsOriginalJBaseQToC.toRatAlgHom (fun _ _ => Commute.all _ _)
lemma complexRationalTensorMap_tmul (c : ℂ) (r : JQ) :
    complexRationalTensorMap (c ⊗ₜ[ℚ] r) =
      algebraMap ℂ JC c * lpsOriginalJBaseQToC r := rfl
local instance zeroNormalizationDictionary025 : Algebra BP BQ :=
  (Algebra.TensorProduct.map (AlgHom.id ℂ ℂ)
    (IsScalarTower.toAlgHom ℚ (Polynomial ℚ) JQ)).toAlgebra
local instance zeroNormalizationDictionary026 : IsScalarTower ℂ BP BQ :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := BP) (A := BQ) fun c => by
  change c ⊗ₜ[ℚ] (1 : JQ) = c ⊗ₜ[ℚ] algebraMap (Polynomial ℚ) JQ 1
  rw [map_one]
local instance zeroNormalizationDictionary027 : IsLocalization
    ((nonZeroDivisors (Polynomial ℚ)).map
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℂ))) BQ :=
  IsLocalization.tensorProduct_tensorProduct_right ℚ ℂ
    (nonZeroDivisors (Polynomial ℚ)) JQ (by
      apply RingHom.ext
      intro p
      change (1 : ℂ) ⊗ₜ[ℚ] algebraMap (Polynomial ℚ) JQ p =
        (1 : ℂ) ⊗ₜ[ℚ] algebraMap (Polynomial ℚ) JQ p
      rfl)
lemma complexRationalTensorMap_polynomial (z : BP) :
    complexRationalTensorMap (algebraMap BP BQ z) =
      algebraMap (Polynomial ℂ) JC (complexPolynomialTensorEquiv z) := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c p =>
    change complexRationalTensorMap (c ⊗ₜ[ℚ] algebraMap (Polynomial ℚ) JQ p) = _
    rw [complexRationalTensorMap_tmul, lpsOriginalJBaseQToC_polynomial,
      complexPolynomialTensorEquiv_tmul, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) JC]
lemma complexRationalTensorMap_injective : Function.Injective complexRationalTensorMap := by
  change Function.Injective complexRationalTensorMap.toRingHom
  rw [IsLocalization.injective_iff_map_algebraMap_eq
    ((nonZeroDivisors (Polynomial ℚ)).map
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := ℂ)))]
  intro x y
  constructor
  · exact congrArg complexRationalTensorMap
  · intro h
    change complexRationalTensorMap (algebraMap BP BQ x) =
      complexRationalTensorMap (algebraMap BP BQ y) at h
    rw [complexRationalTensorMap_polynomial, complexRationalTensorMap_polynomial] at h
    exact congrArg (algebraMap BP BQ)
      (complexPolynomialTensorEquiv.injective ((IsFractionRing.injective (Polynomial ℂ) JC) h))
local instance zeroNormalizationDictionary028 : Algebra JQ BQ := Algebra.TensorProduct.rightAlgebra
local instance zeroNormalizationDictionary029 : Module JQ BQ := Algebra.toModule
def complexRationalTensorMapOverJ : BQ →ₐ[JQ] JC where
  __ := complexRationalTensorMap.toRingHom
  commutes' r := by
    change complexRationalTensorMap ((1 : ℂ) ⊗ₜ[ℚ] r) = lpsOriginalJBaseQToC r
    rw [complexRationalTensorMap_tmul, map_one, one_mul]
variable (B : Type*) [CommRing B] [Algebra ℚ B] [Algebra JQ B]
local instance zeroNormalizationDictionary030 : IsScalarTower ℚ JQ B :=
  IsScalarTower.of_algebraMap_eq (R := ℚ) (S := JQ) (A := B) fun q =>
    (RingHom.map_rat_algebraMap (algebraMap JQ B) q).symm
def constantTensorReassociate : ℂ ⊗[ℚ] B ≃ₐ[ℚ] BQ ⊗[JQ] B :=
  (Algebra.TensorProduct.comm ℚ ℂ B).trans
    (((Algebra.TensorProduct.cancelBaseChange ℚ JQ JQ B ℂ).symm.restrictScalars ℚ).trans
      (((Algebra.TensorProduct.comm JQ B (JQ ⊗[ℚ] ℂ)).restrictScalars ℚ).trans
        ((Algebra.TensorProduct.congr (Algebra.TensorProduct.commRight ℚ JQ ℂ)
          (AlgEquiv.refl (R := JQ) (A₁ := B))).restrictScalars ℚ)))
lemma constantTensorReassociate_tmul (c : ℂ) (x : B) :
    constantTensorReassociate B (c ⊗ₜ[ℚ] x) =
      (c ⊗ₜ[ℚ] (1 : JQ)) ⊗ₜ[JQ] x := by
  simp only [constantTensorReassociate, AlgEquiv.trans_apply,
    Algebra.TensorProduct.comm_tmul, AlgEquiv.restrictScalars_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  rfl
def constantTensorToRationalExtension : ℂ ⊗[ℚ] B →ₐ[ℚ] JC ⊗[JQ] B :=
  ((Algebra.TensorProduct.map complexRationalTensorMapOverJ (AlgHom.id JQ B)).restrictScalars ℚ).comp
    (constantTensorReassociate B).toAlgHom
lemma constantTensorToRationalExtension_tmul (c : ℂ) (x : B) :
    constantTensorToRationalExtension B (c ⊗ₜ[ℚ] x) =
      algebraMap ℂ JC c ⊗ₜ[JQ] x := by
  change Algebra.TensorProduct.map complexRationalTensorMapOverJ (AlgHom.id JQ B)
    (constantTensorReassociate B (c ⊗ₜ[ℚ] x)) = _
  rw [constantTensorReassociate_tmul, Algebra.TensorProduct.map_tmul]
  change complexRationalTensorMap (c ⊗ₜ[ℚ] (1 : JQ)) ⊗ₜ[JQ] x = _
  rw [complexRationalTensorMap_tmul, map_one, mul_one]
lemma constantTensorToRationalExtension_injective [Module.Flat JQ B] :
    Function.Injective (constantTensorToRationalExtension B) := by
  have hi := Module.Flat.rTensor_preserves_injective_linearMap (M := B)
    complexRationalTensorMapOverJ.toLinearMap complexRationalTensorMap_injective
  exact hi.comp (constantTensorReassociate B).injective
end
end QEC.Coding.OriginalNormalizationComparison.ConstantAmbient
namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
local instance zeroNormalizationDictionary031 : Algebra (FractionRing (Polynomial ℚ)) (FractionRing (Polynomial ℂ)) :=
  lpsOriginalJBaseQToC.toAlgebra
local instance zeroNormalizationDictionary032 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local instance zeroNormalizationDictionary033 : Algebra (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbeddingQ.toAlgebra
local instance zeroNormalizationDictionary034 : IsScalarTower (FractionRing (Polynomial ℚ))
    (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJBaseQToC_actualTower
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
local instance zeroNormalizationDictionary035 : Algebra ℂ FC := ((algebraMap JC FC).comp (algebraMap ℂ JC)).toAlgebra
local instance zeroNormalizationDictionary036 : IsScalarTower ℂ JC FC := .of_algebraMap_eq' rfl
local instance zeroNormalizationDictionary037 : FiniteDimensional JQ FQ := lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hN
local instance zeroNormalizationDictionary038 : Module.Free JQ FQ := Module.Free.of_basis (Module.Basis.ofVectorSpace JQ FQ)
local instance zeroNormalizationDictionary039 : Module.Flat JQ FQ := Module.Flat.of_free
lemma lpsOriginalConstantTensorMap_injective :
    Function.Injective (lpsOriginalConstantTensorMap N hN) := by
  let ρ := QEC.Coding.OriginalNormalizationComparison.ConstantAmbient.constantTensorToRationalExtension FQ
  have hρ := QEC.Coding.OriginalNormalizationComparison.ConstantAmbient.constantTensorToRationalExtension_injective FQ
  let e := lpsOriginalRationalComplexTensorEquiv N hN
  have h (z : ℂ ⊗[ℚ] FQ) : lpsOriginalConstantTensorMap N hN z = e (ρ z) := by
    induction z with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c x =>
      change lpsOriginalConstantTensorMap N hN (c ⊗ₜ[ℚ] x) =
        e (QEC.Coding.OriginalNormalizationComparison.ConstantAmbient.constantTensorToRationalExtension FQ (c ⊗ₜ[ℚ] x))
      rw [lpsOriginalConstantTensorMap_tmul,
        QEC.Coding.OriginalNormalizationComparison.ConstantAmbient.constantTensorToRationalExtension_tmul]
      change algebraMap ℂ FC c * lpsOriginalGeneratedQToComplex N hN x =
        lpsOriginalRationalComplexTensorMap N hN (algebraMap ℂ JC c ⊗ₜ[JQ] x)
      rw [lpsOriginalRationalComplexTensorMap_tmul, Algebra.smul_def]
      rfl
  intro x y hxy
  apply hρ
  apply e.injective
  rw [← h x, ← h y]
  exact hxy
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.OriginalNormalizationComparison.IntegralEmbedding
noncomputable section
variable {R S A C : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing C]
lemma integralElem_iff_of_injective
    (f : R →+* A) (g : S →+* C) (e : R ≃+* S) (u : A →+* C)
    (hu : Function.Injective u) (hcomp : u.comp f = g.comp e.toRingHom) (x : A) :
    f.IsIntegralElem x ↔ g.IsIntegralElem (u x) := by
  have hinv : (u.comp f).comp e.symm.toRingHom = g := by
    rw [hcomp]
    apply RingHom.ext
    intro r
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  constructor
  · intro hx
    have h := hx.map u
    rw [hcomp] at h
    exact h.of_comp
  · intro hx
    have h : ((u.comp f).comp e.symm.toRingHom).IsIntegralElem (u x) := by
      rw [hinv]
      exact hx
    exact RingHom.IsIntegralElem.of_map hu h.of_comp
variable [Algebra R A] [Algebra S C]
def integralClosureEmbeddingHom (e : R ≃+* S) (u : A →+* C)
    (hu : Function.Injective u)
    (hcomp : u.comp (algebraMap R A) = (algebraMap S C).comp e.toRingHom) :
    integralClosure R A →+* integralClosure S C where
  toFun x := ⟨u x.val, (integralElem_iff_of_injective (algebraMap R A)
    (algebraMap S C) e u hu hcomp x.val).mp x.property⟩
  map_one' := Subtype.ext u.map_one
  map_zero' := Subtype.ext u.map_zero
  map_mul' x y := Subtype.ext (u.map_mul x.val y.val)
  map_add' x y := Subtype.ext (u.map_add x.val y.val)
lemma integralClosureEmbeddingHom_bijective (e : R ≃+* S) (u : A →+* C)
    (hu : Function.Injective u)
    (hcomp : u.comp (algebraMap R A) = (algebraMap S C).comp e.toRingHom)
    (himage : ∀ x : C, IsIntegral S x → ∃ z : A, u z = x) :
    Function.Bijective (integralClosureEmbeddingHom e u hu hcomp) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact hu (congrArg Subtype.val h)
  · intro y
    obtain ⟨z, hz⟩ := himage y.val y.property
    have hi : IsIntegral R z :=
      (integralElem_iff_of_injective (algebraMap R A) (algebraMap S C)
        e u hu hcomp z).mpr (by simpa only [hz] using
          (show (algebraMap S C).IsIntegralElem y.val from y.property))
    refine ⟨⟨z, hi⟩, ?_⟩
    exact Subtype.ext hz
def integralClosureEmbeddingEquiv (e : R ≃+* S) (u : A →+* C)
    (hu : Function.Injective u)
    (hcomp : u.comp (algebraMap R A) = (algebraMap S C).comp e.toRingHom)
    (himage : ∀ x : C, IsIntegral S x → ∃ z : A, u z = x) :
    integralClosure R A ≃+* integralClosure S C :=
  RingEquiv.ofBijective (integralClosureEmbeddingHom e u hu hcomp)
    (integralClosureEmbeddingHom_bijective e u hu hcomp himage)
end
end QEC.Coding.OriginalNormalizationComparison.IntegralEmbedding
namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
local instance zeroNormalizationDictionary040 : Algebra (FractionRing (Polynomial ℚ)) (FractionRing (Polynomial ℂ)) :=
  lpsOriginalJBaseQToC.toAlgebra
local instance zeroNormalizationDictionary041 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local instance zeroNormalizationDictionary042 : Algebra (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbeddingQ.toAlgebra
local instance zeroNormalizationDictionary043 : IsScalarTower (FractionRing (Polynomial ℚ))
    (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJBaseQToC_actualTower
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
local notation "BP" => ℂ ⊗[ℚ] Polynomial ℚ
local notation "TB" => ℂ ⊗[ℚ] FQ
local instance zeroNormalizationDictionary044 : Algebra (Polynomial ℚ) FQ :=
  ((algebraMap JQ FQ).comp (algebraMap (Polynomial ℚ) JQ)).toAlgebra
local instance zeroNormalizationDictionary045 : IsScalarTower (Polynomial ℚ) JQ FQ := .of_algebraMap_eq' rfl
local instance zeroNormalizationDictionary046 : IsScalarTower ℚ (Polynomial ℚ) FQ := by infer_instance
local instance zeroNormalizationDictionary047 : Algebra (Polynomial ℂ) FC :=
  ((algebraMap JC FC).comp (algebraMap (Polynomial ℂ) JC)).toAlgebra
local instance zeroNormalizationDictionary048 : IsScalarTower (Polynomial ℂ) JC FC := .of_algebraMap_eq' rfl
local instance zeroNormalizationDictionary049 : Algebra ℂ FC := ((algebraMap JC FC).comp (algebraMap ℂ JC)).toAlgebra
local instance zeroNormalizationDictionary050 : IsScalarTower ℂ JC FC := .of_algebraMap_eq' rfl
local instance zeroNormalizationDictionary051 : IsScalarTower ℂ (Polynomial ℂ) FC := .of_algebraMap_eq fun c => by
  change algebraMap JC FC (algebraMap ℂ JC c) =
    algebraMap JC FC (algebraMap (Polynomial ℂ) JC (algebraMap ℂ (Polynomial ℂ) c))
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) JC]
local instance zeroNormalizationDictionary052 : Algebra BP TB :=
  (Algebra.TensorProduct.map (AlgHom.id ℂ ℂ)
    (IsScalarTower.toAlgHom ℚ (Polynomial ℚ) FQ)).toAlgebra
omit [NeZero N] in
lemma lpsOriginalConstantTensorMap_polynomialSquare :
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
        algebraMap (Polynomial ℂ) FC (p.map (algebraMap ℚ ℂ)) := by
      change lpsOriginalGeneratedQToComplex N hN
        (algebraMap JQ FQ (algebraMap (Polynomial ℚ) JQ p)) =
        algebraMap JC FC (algebraMap (Polynomial ℂ) JC (p.map (algebraMap ℚ ℂ)))
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply JQ JC FC]
      change algebraMap JC FC
        (lpsOriginalJBaseQToC (algebraMap (Polynomial ℚ) JQ p)) = _
      rw [lpsOriginalJBaseQToC_polynomial]
    rw [hp]
def lpsOriginalComplexAffineNormalizationTensorEquiv :
    ℂ ⊗[ℚ] integralClosure (Polynomial ℚ) FQ ≃+* integralClosure (Polynomial ℂ) FC :=
  (QEC.Coding.IntegralClosureScalarExtension.charZeroFieldTensorIntegralClosureEquiv
    (k := ℚ) (L := ℂ) (B := FQ) (Polynomial ℚ)).trans
      (QEC.Coding.OriginalNormalizationComparison.IntegralEmbedding.integralClosureEmbeddingEquiv
        QEC.Coding.OriginalNormalizationComparison.ConstantAmbient.complexPolynomialTensorEquiv.toRingEquiv
        (lpsOriginalConstantTensorMap N hN).toRingHom
        (lpsOriginalConstantTensorMap_injective N hN)
        (lpsOriginalConstantTensorMap_polynomialSquare N hN)
        (lpsOriginalComplexIntegral_constantTensorImage N hN))
lemma lpsOriginalComplexAffineNormalizationTensorEquiv_value
    (z : ℂ ⊗[ℚ] integralClosure (Polynomial ℚ) FQ) :
    (lpsOriginalComplexAffineNormalizationTensorEquiv N hN z).val =
      lpsOriginalConstantTensorMap N hN
        (Algebra.TensorProduct.map (AlgHom.id ℂ ℂ)
          ((integralClosure (Polynomial ℚ) FQ).val.restrictScalars ℚ) z) := by
  change lpsOriginalConstantTensorMap N hN
    ((QEC.Coding.IntegralClosureScalarExtension.fieldTensorIntegralClosureHom
      (k := ℚ) (L := ℂ) (B := FQ) (Polynomial ℚ) z).val) = _
  rw [QEC.Coding.IntegralClosureScalarExtension.fieldTensorIntegralClosureHom_val]
  congr 1
lemma lpsOriginalComplexAffineNormalizationTensorEquiv_tmulValue
    (c : ℂ) (x : integralClosure (Polynomial ℚ) FQ) :
    (lpsOriginalComplexAffineNormalizationTensorEquiv N hN (c ⊗ₜ[ℚ] x)).val =
      algebraMap ℂ FC c * lpsOriginalGeneratedQToComplex N hN x.val := by
  rw [lpsOriginalComplexAffineNormalizationTensorEquiv_value]
  change lpsOriginalConstantTensorMap N hN (c ⊗ₜ[ℚ] x.val) = _
  exact lpsOriginalConstantTensorMap_tmul N hN c x.val
local instance zeroNormalizationDictionary053 : Algebra ℂ (integralClosure (Polynomial ℂ) FC) :=
  ((integralClosure (Polynomial ℂ) FC).restrictScalars ℂ).algebra
def lpsOriginalComplexAffineNormalizationTensorAlgEquiv :
    ℂ ⊗[ℚ] integralClosure (Polynomial ℚ) FQ ≃ₐ[ℂ] integralClosure (Polynomial ℂ) FC where
  toRingEquiv := lpsOriginalComplexAffineNormalizationTensorEquiv N hN
  commutes' c := by
    apply Subtype.ext
    change (lpsOriginalComplexAffineNormalizationTensorEquiv N hN
      (c ⊗ₜ[ℚ] (1 : integralClosure (Polynomial ℚ) FQ))).val = algebraMap ℂ FC c
    rw [lpsOriginalComplexAffineNormalizationTensorEquiv_tmulValue]
    change algebraMap ℂ FC c * lpsOriginalGeneratedQToComplex N hN (1 : FQ) = algebraMap ℂ FC c
    rw [map_one, mul_one]
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
local instance zeroNormalizationDictionary054 : Algebra (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbeddingQ.toAlgebra
variable (N : ℕ) (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "BP" => ℚ ⊗[ℤ] Polynomial ℤ
local notation "TB" => ℚ ⊗[ℤ] FQ
local instance zeroNormalizationDictionary055 : Algebra (Polynomial ℤ) FQ := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
local instance zeroNormalizationDictionary056 : IsScalarTower ℤ (Polynomial ℤ) FQ := by infer_instance
local instance zeroNormalizationDictionary057 : Algebra (Polynomial ℚ) FQ :=
  ((algebraMap JQ FQ).comp (algebraMap (Polynomial ℚ) JQ)).toAlgebra
local instance zeroNormalizationDictionary058 : IsScalarTower (Polynomial ℚ) JQ FQ := .of_algebraMap_eq' rfl
local instance zeroNormalizationDictionary059 : IsScalarTower ℚ (Polynomial ℚ) FQ := by infer_instance
local instance zeroNormalizationDictionary060 : Algebra BP TB :=
  (Algebra.TensorProduct.map (AlgHom.id ℚ ℚ)
    (IsScalarTower.toAlgHom ℤ (Polynomial ℤ) FQ)).toAlgebra
def lpsOriginalRationalConstantTensorCollapse : TB ≃ₐ[ℚ] FQ :=
  IsLocalization.algebraLid (R := ℤ) (A := ℚ) (nonZeroDivisors ℤ) FQ
lemma lpsOriginalRationalConstantTensorCollapse_tmul (q : ℚ) (x : FQ) :
    lpsOriginalRationalConstantTensorCollapse N hN (q ⊗ₜ[ℤ] x) = q • x := rfl
lemma lpsOriginalRationalConstantTensorCollapse_polynomialSquare :
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
def lpsOriginalIntegerZeroNormalizationRationalTensorEquiv :
    ℚ ⊗[ℤ] integralClosure (Polynomial ℤ) FQ ≃+* integralClosure (Polynomial ℚ) FQ :=
  (RingEquiv.ofBijective
    (QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldTensorIntegralClosureHom
      (K := ℤ) (F := ℚ) (B0 := FQ) (Polynomial ℤ))
    (QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldTensorIntegralClosureHom_bijective_of_isLocalization
      (K := ℤ) (F := ℚ) (B0 := FQ) (nonZeroDivisors ℤ) (Polynomial ℤ))).trans
      (QEC.Coding.IntegralClosureScalarExtension.BaseRing.integralClosureTransportEquiv
        (QEC.Coding.OriginalNormalizationComparison.ScalarPolynomial.polynomialTensorEquiv ℤ ℚ).toRingEquiv
        (lpsOriginalRationalConstantTensorCollapse N hN).toRingEquiv
        (lpsOriginalRationalConstantTensorCollapse_polynomialSquare N hN))
lemma lpsOriginalIntegerZeroNormalizationRationalTensorEquiv_value
    (z : ℚ ⊗[ℤ] integralClosure (Polynomial ℤ) FQ) :
    (lpsOriginalIntegerZeroNormalizationRationalTensorEquiv N hN z).val =
      lpsOriginalRationalConstantTensorCollapse N hN
        (Algebra.TensorProduct.map (AlgHom.id ℚ ℚ)
          ((integralClosure (Polynomial ℤ) FQ).val.restrictScalars ℤ) z) := by
  change lpsOriginalRationalConstantTensorCollapse N hN
    ((QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldTensorIntegralClosureHom
      (K := ℤ) (F := ℚ) (B0 := FQ) (Polynomial ℤ) z).val) = _
  rw [QEC.Coding.IntegralClosureScalarExtension.BaseRing.fieldTensorIntegralClosureHom_val]
  congr 1
lemma lpsOriginalIntegerZeroNormalizationRationalTensorEquiv_tmulValue
    (q : ℚ) (x : integralClosure (Polynomial ℤ) FQ) :
    (lpsOriginalIntegerZeroNormalizationRationalTensorEquiv N hN (q ⊗ₜ[ℤ] x)).val =
      q • x.val := by
  rw [lpsOriginalIntegerZeroNormalizationRationalTensorEquiv_value]
  change lpsOriginalRationalConstantTensorCollapse N hN (q ⊗ₜ[ℤ] x.val) = _
  exact lpsOriginalRationalConstantTensorCollapse_tmul N hN q x.val
local instance zeroNormalizationDictionary061 : Algebra ℚ (integralClosure (Polynomial ℚ) FQ) :=
  ((integralClosure (Polynomial ℚ) FQ).restrictScalars ℚ).algebra
def lpsOriginalIntegerZeroNormalizationRationalTensorAlgEquiv :
    ℚ ⊗[ℤ] integralClosure (Polynomial ℤ) FQ ≃ₐ[ℚ] integralClosure (Polynomial ℚ) FQ where
  toRingEquiv := lpsOriginalIntegerZeroNormalizationRationalTensorEquiv N hN
  commutes' q := by
    apply Subtype.ext
    change (lpsOriginalIntegerZeroNormalizationRationalTensorEquiv N hN
      (q ⊗ₜ[ℤ] (1 : integralClosure (Polynomial ℤ) FQ))).val = algebraMap ℚ FQ q
    rw [lpsOriginalIntegerZeroNormalizationRationalTensorEquiv_tmulValue]
    change q • (1 : FQ) = algebraMap ℚ FQ q
    rw [Algebra.smul_def, mul_one]
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
local instance zeroNormalizationDictionary062 : Algebra (FractionRing (Polynomial ℚ)) (FractionRing (Polynomial ℂ)) :=
  lpsOriginalJBaseQToC.toAlgebra
local instance zeroNormalizationDictionary063 : Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local instance zeroNormalizationDictionary064 : Algebra (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbeddingQ.toAlgebra
local instance zeroNormalizationDictionary065 : IsScalarTower (FractionRing (Polynomial ℚ))
    (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJBaseQToC_actualTower
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
local instance zeroNormalizationDictionary066 : Algebra (Polynomial ℤ) FQ := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
local instance zeroNormalizationDictionary067 : IsScalarTower ℤ (Polynomial ℤ) FQ := by infer_instance
local instance zeroNormalizationDictionary068 : Algebra (Polynomial ℚ) FQ :=
  ((algebraMap JQ FQ).comp (algebraMap (Polynomial ℚ) JQ)).toAlgebra
local instance zeroNormalizationDictionary069 : IsScalarTower ℚ (Polynomial ℚ) FQ := by infer_instance
local instance zeroNormalizationDictionary070 : Algebra (Polynomial ℂ) FC :=
  ((algebraMap JC FC).comp (algebraMap (Polynomial ℂ) JC)).toAlgebra
local instance zeroNormalizationDictionary071 : IsScalarTower (Polynomial ℂ) JC FC := .of_algebraMap_eq' rfl
local instance zeroNormalizationDictionary072 : Algebra ℂ FC := ((algebraMap JC FC).comp (algebraMap ℂ JC)).toAlgebra
local instance zeroNormalizationDictionary073 : IsScalarTower ℂ JC FC := .of_algebraMap_eq' rfl
local instance zeroNormalizationDictionary074 : IsScalarTower ℂ (Polynomial ℂ) FC := .of_algebraMap_eq fun c => by
  change algebraMap JC FC (algebraMap ℂ JC c) =
    algebraMap JC FC (algebraMap (Polynomial ℂ) JC (algebraMap ℂ (Polynomial ℂ) c))
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) JC]
local notation "IZ" => integralClosure (Polynomial ℤ) FQ
local notation "IQ" => integralClosure (Polynomial ℚ) FQ
local notation "IC" => integralClosure (Polynomial ℂ) FC
local instance zeroNormalizationDictionary075 : Algebra ℚ IQ := ((integralClosure (Polynomial ℚ) FQ).restrictScalars ℚ).algebra
local instance zeroNormalizationDictionary076 : Algebra ℂ IC := ((integralClosure (Polynomial ℂ) FC).restrictScalars ℂ).algebra
def lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv :
    ℂ ⊗[ℤ] lpsOriginalIntegerNormalZeroChart N hN ≃ₐ[ℂ] IC := by
  change ℂ ⊗[ℤ] IZ ≃ₐ[ℂ] IC
  exact (Algebra.TensorProduct.cancelBaseChange ℤ ℚ ℂ ℂ IZ).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := ℂ) (A₁ := ℂ))
      (lpsOriginalIntegerZeroNormalizationRationalTensorAlgEquiv N hN)).trans
        (lpsOriginalComplexAffineNormalizationTensorAlgEquiv N hN))
end
end QEC.Coding.TannerLiftedProduct


