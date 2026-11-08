-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T06:56:28.968895+00:00
-- url     : https://prove2.me/theorems/00880caa-f946-4eaa-b8b8-39d499945353
-- title:
--   LPSOriginal Normalization Base Change
-- statement:
--   Definitions and structural lemmas for LPSOriginal Normalization Base Change, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationBaseChange.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedOverlap_agreement
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerSpecZ_hom_unique
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
namespace QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open scoped TensorProduct
noncomputable section
local instance affineBaseChangeDictionary001 :
    Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local instance affineBaseChangeDictionary002 :
    Algebra (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbeddingQ.toAlgebra
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
local instance affineBaseChangeDictionary003 : Algebra (Polynomial ℤ) FQ :=
  (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
local instance affineBaseChangeDictionary004 : Algebra (Polynomial ℂ) FC :=
  ((algebraMap JC FC).comp (algebraMap (Polynomial ℂ) JC)).toAlgebra
local instance affineBaseChangeDictionary005 : IsScalarTower (Polynomial ℂ) JC FC :=
  .of_algebraMap_eq' rfl
local instance affineBaseChangeDictionary006 : Algebra ℂ FC :=
  ((algebraMap JC FC).comp (algebraMap ℂ JC)).toAlgebra
local instance affineBaseChangeDictionary007 : IsScalarTower ℂ JC FC :=
  .of_algebraMap_eq' rfl
local instance affineBaseChangeDictionary008 : IsScalarTower ℂ (Polynomial ℂ) FC :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap JC FC (algebraMap ℂ JC c) =
      algebraMap JC FC (algebraMap (Polynomial ℂ) JC (algebraMap ℂ (Polynomial ℂ) c))
    rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) JC]
local instance affineBaseChangeDictionary009 : Algebra (LaurentPolynomial ℤ) FQ :=
  (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
local instance affineBaseChangeDictionary010 : Algebra (LaurentPolynomial ℂ) FC :=
  (lpsOriginalComplexLaurentBaseToGeneratedField N hN).toAlgebra
local instance affineBaseChangeDictionary011 :
    IsScalarTower (Polynomial ℂ) (LaurentPolynomial ℂ) FC :=
  lpsOriginalComplexLaurentBase_scalarTower N hN
local instance affineBaseChangeDictionary012 :
    IsScalarTower ℂ (Polynomial ℂ) (LaurentPolynomial ℂ) :=
  IsScalarTower.of_algebraMap_eq fun c => (Polynomial.toLaurentAlg (R := ℂ)).commutes c |>.symm
local instance affineBaseChangeDictionary013 : IsScalarTower ℂ (LaurentPolynomial ℂ) FC :=
  .to₁₃₄ ℂ (Polynomial ℂ) (LaurentPolynomial ℂ) FC
local notation "ICL" => integralClosure (LaurentPolynomial ℂ) FC
local instance affineBaseChangeDictionary014 : Algebra ℂ ICL :=
  ((integralClosure (LaurentPolynomial ℂ) FC).restrictScalars ℂ).algebra
local instance affineBaseChangeDictionary015 :
    Algebra ℤ (lpsOriginalIntegerNormalLaurentChart N hN) :=
  Ring.toIntAlgebra (lpsOriginalIntegerNormalLaurentChart N hN)
local instance affineBaseChangeDictionary016 :
    Module ℤ (lpsOriginalIntegerNormalLaurentChart N hN) :=
  AddCommGroup.toIntModule (lpsOriginalIntegerNormalLaurentChart N hN)
local notation "IC0" => integralClosure (Polynomial ℂ) FC
local instance affineBaseChangeZeroComplexAlgebra : Algebra ℂ IC0 :=
  ((integralClosure (Polynomial ℂ) FC).restrictScalars ℂ).algebra
local instance affineBaseChangeZeroIntegerAlgebra :
    Algebra ℤ (lpsOriginalIntegerNormalZeroChart N hN) :=
  Ring.toIntAlgebra (lpsOriginalIntegerNormalZeroChart N hN)
local instance affineBaseChangeZeroIntegerModule :
    Module ℤ (lpsOriginalIntegerNormalZeroChart N hN) :=
  AddCommGroup.toIntModule (lpsOriginalIntegerNormalZeroChart N hN)
local instance affineBaseChangeZeroSelfAlgebra : Algebra (lpsOriginalIntegerNormalZeroChart N hN) (lpsOriginalIntegerNormalZeroChart N hN) := Algebra.id (lpsOriginalIntegerNormalZeroChart N hN)
local instance affineBaseChangeZeroSelfSMul : SMul (lpsOriginalIntegerNormalZeroChart N hN) (lpsOriginalIntegerNormalZeroChart N hN) := Algebra.toSMul
local instance affineBaseChangeZeroSelfModule : Module (lpsOriginalIntegerNormalZeroChart N hN) (lpsOriginalIntegerNormalZeroChart N hN) := Algebra.toModule
local instance affineBaseChangeZeroIntegerSelfTower : IsScalarTower ℤ (lpsOriginalIntegerNormalZeroChart N hN) (lpsOriginalIntegerNormalZeroChart N hN) :=
  ⟨fun z a b => by
    change (z • a) * b = z • (a * b)
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_assoc]⟩
local instance affineBaseChangeLaurentSelfAlgebra : Algebra (lpsOriginalIntegerNormalLaurentChart N hN) (lpsOriginalIntegerNormalLaurentChart N hN) := Algebra.id (lpsOriginalIntegerNormalLaurentChart N hN)
local instance affineBaseChangeLaurentSelfSMul : SMul (lpsOriginalIntegerNormalLaurentChart N hN) (lpsOriginalIntegerNormalLaurentChart N hN) := Algebra.toSMul
local instance affineBaseChangeLaurentSelfModule : Module (lpsOriginalIntegerNormalLaurentChart N hN) (lpsOriginalIntegerNormalLaurentChart N hN) := Algebra.toModule
local instance affineBaseChangeLaurentIntegerSelfTower : IsScalarTower ℤ (lpsOriginalIntegerNormalLaurentChart N hN) (lpsOriginalIntegerNormalLaurentChart N hN) :=
  ⟨fun z a b => by
    change (z • a) * b = z • (a * b)
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_assoc]⟩
def lpsOriginalZeroNormalizationAffineBaseChangeIso :
    Spec (.of IC0) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ)))
        (Spec.map (CommRingCat.ofHom
          (algebraMap ℤ (lpsOriginalIntegerNormalZeroChart N hN)))) :=
  normalizationTensorSpecIso (R := ℤ) (S := ℂ) (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hN)
def lpsOriginalLaurentNormalizationAffineBaseChangeIso :
    Spec (.of ICL) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ)))
        (Spec.map (CommRingCat.ofHom
          (algebraMap ℤ (lpsOriginalIntegerNormalLaurentChart N hN)))) :=
  normalizationTensorSpecIso (R := ℤ) (S := ℂ) (lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv N hN)
attribute [local irreducible] lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv
section InfinityAffineBaseChange
local instance affineBaseChangeInfinityPolynomialAlgebra : Algebra (Polynomial ℂ) FC :=
  (lpsOriginalReciprocalComplexFieldPolynomialMap N hN).toAlgebra
local instance affineBaseChangeInfinityComplexPolynomialTower :
    IsScalarTower ℂ (Polynomial ℂ) FC :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap JC FC (algebraMap ℂ JC c) =
      algebraMap JC FC (lpsOriginalComplexJFractionInversion (algebraMap ℂ JC c))
    rw [lpsOriginalComplexJFractionInversion_constant]
local notation "ICInfinity" => integralClosure (Polynomial ℂ) FC
local instance affineBaseChangeInfinityComplexAlgebra : Algebra ℂ ICInfinity :=
  ((integralClosure (Polynomial ℂ) FC).restrictScalars ℂ).algebra
local instance affineBaseChangeInfinityIntegerAlgebra :
    Algebra ℤ (lpsOriginalIntegerNormalInfinityChart N hN) :=
  Ring.toIntAlgebra (lpsOriginalIntegerNormalInfinityChart N hN)
local instance affineBaseChangeInfinityIntegerModule :
    Module ℤ (lpsOriginalIntegerNormalInfinityChart N hN) :=
  AddCommGroup.toIntModule (lpsOriginalIntegerNormalInfinityChart N hN)
local instance affineBaseChangeInfinitySelfAlgebra : Algebra (lpsOriginalIntegerNormalInfinityChart N hN) (lpsOriginalIntegerNormalInfinityChart N hN) := Algebra.id (lpsOriginalIntegerNormalInfinityChart N hN)
local instance affineBaseChangeInfinitySelfSMul : SMul (lpsOriginalIntegerNormalInfinityChart N hN) (lpsOriginalIntegerNormalInfinityChart N hN) := Algebra.toSMul
local instance affineBaseChangeInfinitySelfModule : Module (lpsOriginalIntegerNormalInfinityChart N hN) (lpsOriginalIntegerNormalInfinityChart N hN) := Algebra.toModule
local instance affineBaseChangeInfinityIntegerSelfTower : IsScalarTower ℤ (lpsOriginalIntegerNormalInfinityChart N hN) (lpsOriginalIntegerNormalInfinityChart N hN) :=
  ⟨fun z a b => by
    change (z • a) * b = z • (a * b)
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_assoc]⟩
def lpsOriginalInfinityNormalizationAffineBaseChangeIso :
    Spec (.of ICInfinity) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ)))
        (Spec.map (CommRingCat.ofHom
          (algebraMap ℤ (lpsOriginalIntegerNormalInfinityChart N hN)))) :=
  normalizationTensorSpecIso (R := ℤ) (S := ℂ) (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hN)
end InfinityAffineBaseChange
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalCharts_pullback (N : ℕ) (hN : 0<N) :
    IsPullback (lpsOriginalIntegerNormalSchemeOverlapMap N hN false)
      (lpsOriginalIntegerNormalSchemeOverlapMap N hN true)
      (lpsOriginalIntegerNormalGluedChartMap N hN false)
      (lpsOriginalIntegerNormalGluedChartMap N hN true) := by
  let D := lpsOriginalIntegerNormalSchemeGlueData N hN
  have e : D.V (false,true)=Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have e' : D.V (true,false)=Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have hf : D.f false true = eqToHom e ≫
      lpsOriginalIntegerNormalSchemeOverlapMap N hN false := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have hf' : D.f true false = eqToHom e' ≫
      lpsOriginalIntegerNormalSchemeOverlapMap N hN true := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have ht : D.t false true = eqToHom e ≫ eqToHom e'.symm := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have h : IsPullback (D.f false true) (D.t false true ≫ D.f true false)
      (D.ι false) (D.ι true) :=
    { w := (D.glue_condition false true).symm
      isLimit' := ⟨D.vPullbackConeIsLimit false true⟩ }
  apply h.of_iso (eqToIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, eqToIso.hom, Category.comp_id] using hf
  · simp only [Iso.refl_hom, eqToIso.hom, Category.comp_id]
    rw [ht,hf']
    simp only [Category.assoc,eqToHom_trans_assoc,eqToHom_refl,Category.id_comp]
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    rfl
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    rfl
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
def lpsOriginalIntegerNormalComplexBaseChangedChart (N : ℕ) (hN : 0 < N) (b : Bool) : Scheme :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ)))
    (lpsOriginalIntegerNormalGluedChartMap N hN b ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN)
def lpsOriginalIntegerNormalComplexBaseChangeOpenCover (N : ℕ) (hN : 0 < N) :
    (lpsOriginalIntegerNormalComplexBaseChange N hN).OpenCover :=
  Scheme.Pullback.openCoverOfRight (lpsOriginalIntegerNormalSchemeGlueData N hN).openCover
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ)))
    (lpsOriginalIntegerNormalGluedToSpecZ N hN)
set_option backward.isDefEq.respectTransparency false in
def lpsOriginalComplexNormalChartBaseChangeIso (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    lpsOriginalComplexNormalSchemeChart N hN b ≅
      lpsOriginalIntegerNormalComplexBaseChangedChart N hN b := by
  cases b with
  | false =>
    exact lpsOriginalZeroNormalizationAffineBaseChangeIso N hN ≪≫
      pullback.congrHom rfl (lpsOriginalIntegerSpecZ_hom_unique
        (lpsOriginalIntegerNormalZeroChart N hN) _ _)
  | true =>
    exact lpsOriginalInfinityNormalizationAffineBaseChangeIso N hN ≪≫
      pullback.congrHom rfl (lpsOriginalIntegerSpecZ_hom_unique
        (lpsOriginalIntegerNormalInfinityChart N hN) _ _)
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false in
def lpsOriginalComplexNormalLaurentBaseChangeIso (N : ℕ) [NeZero N] (hN : 0 < N) :
    Spec (.of (lpsOriginalComplexNormalLaurentChart N hN)) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ)))
        (lpsOriginalIntegerNormalSchemeOverlapMap N hN false ≫
          lpsOriginalIntegerNormalGluedChartMap N hN false ≫
          lpsOriginalIntegerNormalGluedToSpecZ N hN) :=
  lpsOriginalLaurentNormalizationAffineBaseChangeIso N hN ≪≫
    pullback.congrHom rfl (lpsOriginalIntegerSpecZ_hom_unique
      (lpsOriginalIntegerNormalLaurentChart N hN) _ _)
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.ChartBaseChange
noncomputable section
set_option backward.isDefEq.respectTransparency false in
def lpsOriginalIntegerNormalComplexBaseChangedOverlapMap (N : ℕ) (hN : 0 < N) (b : Bool) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ)))
      (lpsOriginalIntegerNormalSchemeOverlapMap N hN false ≫
        lpsOriginalIntegerNormalGluedChartMap N hN false ≫
        lpsOriginalIntegerNormalGluedToSpecZ N hN) ⟶
      lpsOriginalIntegerNormalComplexBaseChangedChart N hN b := by
  cases b with
  | false =>
    exact scalarFirstBaseChangedMap (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ)))
      _ _ (lpsOriginalIntegerNormalSchemeOverlapMap N hN false) rfl
  | true =>
    exact scalarFirstBaseChangedMap (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ)))
      _ _ (lpsOriginalIntegerNormalSchemeOverlapMap N hN true)
      (by simpa only [Category.assoc] using
        (congrArg (fun f => f ≫ lpsOriginalIntegerNormalGluedToSpecZ N hN)
          (lpsOriginalIntegerNormalGluedOverlap_agreement N hN).symm))
end
end QEC.Coding.TannerLiftedProduct


