-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLaurentNormalizationComparison
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalLaurentNormalizationComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T06:09:28.592664+00:00
-- url     : https://prove2.me/theorems/7eda759c-2aff-4336-892b-f5947dc1ae76
-- title:
--   LPSOriginal Laurent Normalization Comparison
-- statement:
--   Definitions and structural lemmas for LPSOriginal Laurent Normalization Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLaurentNormalizationComparison.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNormalizationComparison
import Mathlib.RingTheory.Localization.BaseChange
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalOverlap_localization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv_tmulValue
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
namespace QEC.Coding.OriginalNormalizationComparison.ChartLocalization
open scoped TensorProduct
noncomputable section
variable {R S A D : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing D]
  [Algebra R S] [Algebra R A] [Algebra S D]
variable {P U V : Type*} [CommRing P] [CommRing U] [CommRing V]
  [Algebra U V] [Algebra D P]
def localizationRingEquivAt
    (u : U) (d : D) (f : U ≃+* D) (hf : f u = d)
    [IsLocalization.Away u V] [IsLocalization.Away d P] : V ≃+* P := by
  have H : (Submonoid.powers u).map f.toMonoidHom = Submonoid.powers d := by
    rw [Submonoid.map_powers]
    congr 1
  exact IsLocalization.ringEquivOfRingEquiv V P f H
lemma localizationRingEquivAt_algebraMap
    (u : U) (d : D) (f : U ≃+* D) (hf : f u = d)
    [IsLocalization.Away u V] [IsLocalization.Away d P] (x : U) :
    localizationRingEquivAt u d f hf (algebraMap U V x) = algebraMap D P (f x) := by
  unfold localizationRingEquivAt
  exact IsLocalization.ringEquivOfRingEquiv_eq _ x
variable [Algebra S U] [Algebra S V] [Algebra S P]
  [IsScalarTower S U V] [hDP : IsScalarTower S D P]
def localizationAlgEquivAt
    (u : U) (d : D) (f : U ≃ₐ[S] D) (hf : f u = d)
    [IsLocalization.Away u V] [IsLocalization.Away d P] : V ≃ₐ[S] P :=
  AlgEquiv.ofRingEquiv (f := localizationRingEquivAt u d f.toRingEquiv hf) fun c => by
    rw [IsScalarTower.algebraMap_apply S U V, localizationRingEquivAt_algebraMap]
    change algebraMap D P (f (algebraMap S U c)) = algebraMap S P c
    rw [f.commutes, ← IsScalarTower.algebraMap_apply S D P]
end
end QEC.Coding.OriginalNormalizationComparison.ChartLocalization
namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
local notation "JC" => FractionRing (Polynomial ℂ)
lemma lpsOriginalComplexLaurentBaseFraction_powersUnit
    (s : Submonoid.powers (Polynomial.X : Polynomial ℂ)) :
    IsUnit (lpsOriginalCanonicalComplexPolynomialFractionMap s) := by
  obtain ⟨n, hn⟩ := s.property
  rw [← hn, map_pow]
  exact (IsUnit.mk0 _ ((map_ne_zero_iff _
    (IsFractionRing.injective (Polynomial ℂ) JC)).mpr Polynomial.X_ne_zero)).pow n
def lpsOriginalComplexLaurentBaseFractionMap : LaurentPolynomial ℂ →+* JC :=
  IsLocalization.lift (S := LaurentPolynomial ℂ)
    lpsOriginalComplexLaurentBaseFraction_powersUnit
lemma lpsOriginalComplexLaurentBaseFractionMap_polynomial (p : Polynomial ℂ) :
    lpsOriginalComplexLaurentBaseFractionMap (Polynomial.toLaurent p) =
      lpsOriginalCanonicalComplexPolynomialFractionMap p :=
  IsLocalization.lift_eq _ p
local instance laurentNormalizationDictionary001 : Algebra JC LPSOriginalHolomorphicFractionField := lpsOriginalJFractionEmbedding.toAlgebra
variable (N : ℕ) (hN : 0 < N)
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
local instance laurentNormalizationDictionary002 : Algebra (Polynomial ℂ) FC :=
  ((algebraMap JC FC).comp (algebraMap (Polynomial ℂ) JC)).toAlgebra
local instance laurentNormalizationDictionary003 : IsScalarTower (Polynomial ℂ) JC FC := .of_algebraMap_eq' rfl
local instance laurentNormalizationDictionary004 : Algebra ℂ FC := ((algebraMap JC FC).comp (algebraMap ℂ JC)).toAlgebra
local instance laurentNormalizationDictionary005 : IsScalarTower ℂ JC FC := .of_algebraMap_eq' rfl
local instance laurentNormalizationDictionary006 : IsScalarTower ℂ (Polynomial ℂ) FC := .of_algebraMap_eq fun c => by
  change algebraMap JC FC (algebraMap ℂ JC c) =
    algebraMap JC FC (algebraMap (Polynomial ℂ) JC (algebraMap ℂ (Polynomial ℂ) c))
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) JC]
def lpsOriginalComplexLaurentBaseToGeneratedField : LaurentPolynomial ℂ →+* FC :=
  (algebraMap JC FC).comp lpsOriginalComplexLaurentBaseFractionMap
local instance laurentNormalizationDictionary007 : Algebra (LaurentPolynomial ℂ) FC :=
  (lpsOriginalComplexLaurentBaseToGeneratedField N hN).toAlgebra
lemma lpsOriginalComplexLaurentBase_scalarTower :
    IsScalarTower (Polynomial ℂ) (LaurentPolynomial ℂ) FC :=
  IsScalarTower.of_algebraMap_eq fun p => by
    change algebraMap JC FC (algebraMap (Polynomial ℂ) JC p) =
      algebraMap JC FC (lpsOriginalComplexLaurentBaseFractionMap (Polynomial.toLaurent p))
    rw [lpsOriginalComplexLaurentBaseFractionMap_polynomial]
local instance laurentNormalizationDictionary008 : IsScalarTower (Polynomial ℂ) (LaurentPolynomial ℂ) FC :=
  lpsOriginalComplexLaurentBase_scalarTower N hN
local notation "IC0" => integralClosure (Polynomial ℂ) FC
local notation "ICL" => integralClosure (LaurentPolynomial ℂ) FC
def lpsOriginalComplexNormalZeroToLaurent : IC0 →+* ICL where
  toFun x := ⟨x.val, x.property.tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
local instance laurentNormalizationDictionary009 : Algebra IC0 ICL := (lpsOriginalComplexNormalZeroToLaurent N hN).toAlgebra
local instance laurentNormalizationDictionary010 : SMul IC0 ICL := Algebra.toSMul
local instance laurentNormalizationDictionary011 : IsScalarTower IC0 ICL FC :=
  ⟨fun c d l => by
    change (c.val * d.val) * l = c.val * (d.val * l)
    exact mul_assoc _ _ _⟩
local instance laurentNormalizationDictionary012 : IsScalarTower (Polynomial ℂ) IC0 ICL :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ => Subtype.ext rfl)
lemma lpsOriginalComplexNormalLaurent_localization :
    IsLocalization.Away (algebraMap (Polynomial ℂ) IC0 Polynomial.X) ICL := by
  have hx : algebraMap (Polynomial ℂ) FC Polynomial.X ≠ 0 := by
    change algebraMap JC FC (algebraMap (Polynomial ℂ) JC Polynomial.X) ≠ 0
    exact (map_ne_zero_iff _ (algebraMap JC FC).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial ℂ) JC)).mpr Polynomial.X_ne_zero)
  let : IsLocalization.Away (algebraMap (Polynomial ℂ) FC Polynomial.X) FC :=
    IsLocalization.of_le_isUnit fun y hy => by
      obtain ⟨n, rfl⟩ := hy
      exact (IsUnit.mk0 _ hx).pow n
  exact IsLocalization.Away.integralClosure (R := Polynomial ℂ) (S := FC)
    (Rf := LaurentPolynomial ℂ) (Sf := FC) Polynomial.X
local instance laurentNormalizationDictionary013 : IsScalarTower ℂ (Polynomial ℂ) (LaurentPolynomial ℂ) :=
  IsScalarTower.of_algebraMap_eq fun c => (Polynomial.toLaurentAlg (R := ℂ)).commutes c |>.symm
local instance laurentNormalizationDictionary014 : IsScalarTower ℂ (LaurentPolynomial ℂ) FC :=
  .to₁₃₄ ℂ (Polynomial ℂ) (LaurentPolynomial ℂ) FC
local instance laurentNormalizationDictionary015 : Algebra ℂ IC0 := ((integralClosure (Polynomial ℂ) FC).restrictScalars ℂ).algebra
local instance laurentNormalizationDictionary016 : Algebra ℂ ICL := ((integralClosure (LaurentPolynomial ℂ) FC).restrictScalars ℂ).algebra
local instance laurentNormalizationDictionary017 : IsScalarTower ℂ IC0 ICL :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ => Subtype.ext rfl)
local instance laurentNormalizationDictionary018 : IsLocalization.Away (algebraMap (Polynomial ℂ) IC0 Polynomial.X) ICL :=
  lpsOriginalComplexNormalLaurent_localization N hN
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local instance laurentNormalizationDictionary019 : Algebra JQ JC := lpsOriginalJBaseQToC.toAlgebra
local instance laurentNormalizationDictionary020 : Algebra JQ LPSOriginalHolomorphicFractionField := lpsOriginalJFractionEmbeddingQ.toAlgebra
local instance laurentNormalizationDictionary021 : IsScalarTower JQ JC LPSOriginalHolomorphicFractionField :=
  lpsOriginalJBaseQToC_actualTower
local instance laurentNormalizationDictionary022 : Algebra (Polynomial ℤ) FQ := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
local instance laurentNormalizationDictionary023 : IsScalarTower ℤ (Polynomial ℤ) FQ := by infer_instance
local instance laurentNormalizationDictionary024 : Algebra (LaurentPolynomial ℤ) FQ :=
  (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
local instance laurentNormalizationDictionary025 : IsScalarTower (Polynomial ℤ) (LaurentPolynomial ℤ) FQ :=
  lpsOriginalIntegerLaurentBase_scalarTower N hN
local instance laurentNormalizationDictionary026 : IsScalarTower ℤ (LaurentPolynomial ℤ) FQ := by infer_instance
local notation "IZ" => lpsOriginalIntegerNormalZeroChart N hN
local notation "IL" => lpsOriginalIntegerNormalLaurentChart N hN
local instance laurentNormalizationDictionary027 : Algebra ℤ IZ := Ring.toIntAlgebra IZ
local instance laurentNormalizationDictionary028 : Algebra ℤ IL := Ring.toIntAlgebra IL
local instance laurentNormalizationDictionary029 : Module ℤ IZ := AddCommGroup.toIntModule IZ
local instance laurentNormalizationDictionary030 : Module ℤ IL := AddCommGroup.toIntModule IL
local instance laurentNormalizationDictionary031 : Algebra IZ IZ := Algebra.id IZ
local instance laurentNormalizationDictionary032 : SMul IZ IZ := Algebra.toSMul
local instance laurentNormalizationDictionary033 : Module IZ IZ := Algebra.toModule
local instance laurentNormalizationDictionary034 : Algebra IL IL := Algebra.id IL
local instance laurentNormalizationDictionary035 : SMul IL IL := Algebra.toSMul
local instance laurentNormalizationDictionary036 : Module IL IL := Algebra.toModule
local instance laurentNormalizationDictionary037 : IsScalarTower ℤ IZ IZ :=
  ⟨fun z a b => by
    change (z • a) * b = z • (a * b)
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_assoc]⟩
local instance laurentNormalizationDictionary038 : IsScalarTower ℤ IL IL :=
  ⟨fun z a b => by
    change (z • a) * b = z • (a * b)
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_assoc]⟩
local instance laurentNormalizationDictionary039 : Algebra IZ IL := (lpsOriginalIntegerNormalZeroToLaurent N hN).toAlgebra
local instance laurentNormalizationDictionary040 : SMul IZ IL := Algebra.toSMul
local instance laurentNormalizationDictionary041 : IsScalarTower ℤ IZ IL :=
  IsScalarTower.of_algebraMap_eq fun z => by
    rw [algebraMap_int_eq, algebraMap_int_eq]
    change (z : IL) = algebraMap IZ IL (z : IZ)
    exact (map_intCast (algebraMap IZ IL) z).symm
local instance laurentNormalizationDictionary042 : IsLocalization.Away (algebraMap (Polynomial ℤ) IZ Polynomial.X) IL :=
  lpsOriginalIntegerNormalOverlap_localization N hN
variable [NeZero N]
lemma lpsOriginalIntegerZeroComplexNormalization_j :
    lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hN
      ((1 : ℂ) ⊗ₜ[ℤ] algebraMap (Polynomial ℤ) IZ Polynomial.X) =
      algebraMap (Polynomial ℂ) IC0 Polynomial.X := by
  apply Subtype.ext
  erw [lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv_tmulValue]
  rw [map_one, one_mul]
  change lpsOriginalGeneratedQToComplex N hN
      (algebraMap JQ FQ (lpsOriginalIntegerBaseFractionMap Polynomial.X)) =
    algebraMap JC FC (lpsOriginalCanonicalComplexPolynomialFractionMap Polynomial.X)
  unfold lpsOriginalIntegerBaseFractionMap
  change lpsOriginalGeneratedQToComplex N hN
      (algebraMap JQ FQ (lpsOriginalCanonicalRationalPolynomialFractionMap
        (Polynomial.X.map (algebraMap ℤ ℚ)))) = _
  rw [Polynomial.map_X, AlgHom.commutes, IsScalarTower.algebraMap_apply JQ JC FC]
  change algebraMap JC FC (lpsOriginalJBaseQToC
    (lpsOriginalCanonicalRationalPolynomialFractionMap Polynomial.X)) = _
  rw [lpsOriginalJBaseQToC_polynomial, Polynomial.map_X]
local instance laurentNormalizationDictionary043 : Algebra IC0 IC0 := Algebra.id IC0
local instance laurentNormalizationDictionary044 : SMul IC0 IC0 := Algebra.toSMul
local instance laurentNormalizationDictionary045 : Module IC0 IC0 := Algebra.toModule
local instance laurentNormalizationDictionary046 : IsScalarTower IC0 IC0 IC0 := by infer_instance
local notation "TIZ" => ℂ ⊗[ℤ] IZ
local notation "TIL" => ℂ ⊗[ℤ] IL
local instance laurentNormalizationDictionary047 : Algebra TIZ TIL :=
  (Algebra.TensorProduct.map (AlgHom.id ℂ ℂ)
    (lpsOriginalIntegerNormalZeroToLaurent N hN).toIntAlgHom).toAlgebra
local instance laurentNormalizationDictionary048 : SMul TIZ TIL := Algebra.toSMul
local instance laurentNormalizationDictionary049 : Module TIZ TIL := Algebra.toModule
local instance laurentNormalizationDictionary050 : IsScalarTower ℂ TIZ TIL :=
  ⟨fun c a b => by
    let f : TIZ →ₐ[ℂ] TIL := Algebra.TensorProduct.map (AlgHom.id ℂ ℂ)
      (lpsOriginalIntegerNormalZeroToLaurent N hN).toIntAlgHom
    change f (c • a) * b = c • (f a * b)
    calc
      f (c • a) * b = (c • f a) * b := congrArg (fun x : TIL => x * b)
        (f.toLinearMap.map_smul c a)
      _ = c • (f a * b) := smul_mul_assoc c (f a) b⟩
omit [NeZero N] in
lemma lpsOriginalIntegerLaurentTensor_localization :
    IsLocalization.Away
      ((1 : ℂ) ⊗ₜ[ℤ] algebraMap (Polynomial ℤ) IZ Polynomial.X) TIL := by
  have h := IsLocalization.tensorProduct_tensorProduct_right ℤ ℂ
    (Submonoid.powers (algebraMap (Polynomial ℤ) IZ Polynomial.X)) IL
    (by apply RingHom.ext; intro a; rfl)
  simpa only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply] using h
local instance laurentNormalizationDictionary051 : IsLocalization.Away
    ((1 : ℂ) ⊗ₜ[ℤ] algebraMap (Polynomial ℤ) IZ Polynomial.X) TIL :=
  lpsOriginalIntegerLaurentTensor_localization N hN
def lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv : TIL ≃ₐ[ℂ] ICL :=
  QEC.Coding.OriginalNormalizationComparison.ChartLocalization.localizationAlgEquivAt
    (S := ℂ) (U := TIZ) (D := IC0) (V := TIL) (P := ICL)
    ((1 : ℂ) ⊗ₜ[ℤ] algebraMap (Polynomial ℤ) IZ Polynomial.X)
    (algebraMap (Polynomial ℂ) IC0 Polynomial.X)
    (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hN)
    (lpsOriginalIntegerZeroComplexNormalization_j N hN)
local instance laurentNormalizationDictionary052 : IsScalarTower ℤ ℂ FC := by infer_instance
def lpsOriginalIntegerLaurentConstantTensorMap : TIL →ₐ[ℂ] FC :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ FC)
    ((lpsOriginalGeneratedQToComplex N hN).toRingHom.comp
      (integralClosure (LaurentPolynomial ℤ) FQ).val.toRingHom).toIntAlgHom
    (fun _ _ => Commute.all _ _)
lemma lpsOriginalComplexLaurentBaseFractionMap_T_one :
    lpsOriginalComplexLaurentBaseFractionMap (LaurentPolynomial.T 1) =
      lpsOriginalCanonicalComplexPolynomialFractionMap Polynomial.X := by
  rw [← Polynomial.toLaurent_X, lpsOriginalComplexLaurentBaseFractionMap_polynomial]
lemma lpsOriginalComplexLaurentBaseFractionMap_T_neg_one :
    lpsOriginalComplexLaurentBaseFractionMap (LaurentPolynomial.T (-1)) =
      (lpsOriginalCanonicalComplexPolynomialFractionMap Polynomial.X)⁻¹ := by
  have hx : lpsOriginalCanonicalComplexPolynomialFractionMap Polynomial.X ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial ℂ) JC)).mpr Polynomial.X_ne_zero
  have h : lpsOriginalCanonicalComplexPolynomialFractionMap Polynomial.X *
      lpsOriginalComplexLaurentBaseFractionMap (LaurentPolynomial.T (-1)) = 1 := by
    rw [← lpsOriginalComplexLaurentBaseFractionMap_T_one, ← map_mul,
      ← LaurentPolynomial.T_add]
    simp
  apply mul_left_cancel₀ hx
  rw [h, mul_inv_cancel₀ hx]
lemma lpsOriginalComplexLaurentBaseFractionMap_reciprocalPolynomial (p : Polynomial ℂ) :
    lpsOriginalComplexLaurentBaseFractionMap
      (LaurentPolynomial.invert (Polynomial.toLaurent p)) =
      lpsOriginalComplexJFractionInversion
        (lpsOriginalCanonicalComplexPolynomialFractionMap p) := by
  have h : lpsOriginalComplexLaurentBaseFractionMap.comp
      ((LaurentPolynomial.invert (R := ℂ)).toRingHom.comp Polynomial.toLaurent) =
      lpsOriginalComplexJFractionInversion.comp
        lpsOriginalCanonicalComplexPolynomialFractionMap := by
    apply Polynomial.ringHom_ext
    · intro c
      change lpsOriginalComplexLaurentBaseFractionMap
        (LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C c))) = _
      rw [Polynomial.toLaurent_C, LaurentPolynomial.invert_C,
        ← Polynomial.toLaurent_C, lpsOriginalComplexLaurentBaseFractionMap_polynomial]
      change lpsOriginalCanonicalComplexPolynomialFractionMap (Polynomial.C c) =
        lpsOriginalComplexJFractionInversion
          (lpsOriginalCanonicalComplexPolynomialFractionMap (Polynomial.C c))
      rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) JC,
        lpsOriginalComplexJFractionInversion_constant]
    · change lpsOriginalComplexLaurentBaseFractionMap
        (LaurentPolynomial.invert (Polynomial.toLaurent Polynomial.X)) = _
      rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T,
        lpsOriginalComplexLaurentBaseFractionMap_T_neg_one]
      exact lpsOriginalComplexJFractionInversion_X.symm
  exact RingHom.congr_fun h p
abbrev lpsOriginalComplexNormalInfinityChart : Type :=
  letI := (lpsOriginalReciprocalComplexFieldPolynomialMap N hN).toAlgebra
  integralClosure (Polynomial ℂ) FC
def lpsOriginalComplexNormalInfinityToLaurent :
    lpsOriginalComplexNormalInfinityChart N hN →+* ICL := by
  letI : Algebra (Polynomial ℂ) FC :=
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hN).toAlgebra
  letI : Algebra (Polynomial ℂ) (LaurentPolynomial ℂ) :=
    ((LaurentPolynomial.invert (R := ℂ)).toRingHom.comp Polynomial.toLaurent).toAlgebra
  letI : SMul (Polynomial ℂ) (LaurentPolynomial ℂ) := Algebra.toSMul
  letI : Module (Polynomial ℂ) (LaurentPolynomial ℂ) := Algebra.toModule
  letI : IsScalarTower (Polynomial ℂ) (LaurentPolynomial ℂ) FC :=
    IsScalarTower.of_algebraMap_eq fun p => by
      change lpsOriginalReciprocalComplexFieldPolynomialMap N hN p =
        algebraMap JC FC (lpsOriginalComplexLaurentBaseFractionMap
          (LaurentPolynomial.invert (Polynomial.toLaurent p)))
      rw [lpsOriginalComplexLaurentBaseFractionMap_reciprocalPolynomial]
      rfl
  exact
    { toFun := fun x => ⟨x.val, x.property.tower_top⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
end
end QEC.Coding.TannerLiftedProduct


