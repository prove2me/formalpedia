-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T06:47:44.701359+00:00
-- url     : https://prove2.me/theorems/32cc92cd-ba3c-4631-ba01-ac6f1430e528
-- title:
--   LPSOriginal Complex Normal Charts
-- statement:
--   Definitions and structural lemmas for LPSOriginal Complex Normal Charts, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalComplexNormalCharts.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLaurentNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_NormalizationBaseChange_algEquivRingHom_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_NormalizationBaseChange_normalizationBaseRingHom_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_NormalizationBaseChange_normalizationConstantRingHom_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv_tmulValue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerLaurentChartComplexNormalization_tmulValue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedOverlap_agreement
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerSpecZ_hom_unique
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
namespace QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open scoped TensorProduct
noncomputable section
local notation "JC" => FractionRing (Polynomial ℂ)
local instance complexGluingDictionary001 : Algebra JC LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
abbrev lpsOriginalComplexNormalZeroChart (N : ℕ) (hN : 0 < N) : Type :=
  letI : Algebra (Polynomial ℂ) (lpsOriginalGeneratedFunctionField N hN) :=
    ((algebraMap JC (lpsOriginalGeneratedFunctionField N hN)).comp
      (algebraMap (Polynomial ℂ) JC)).toAlgebra
  integralClosure (Polynomial ℂ) (lpsOriginalGeneratedFunctionField N hN)
abbrev lpsOriginalComplexNormalLaurentChart (N : ℕ) (hN : 0 < N) : Type :=
  letI := (lpsOriginalComplexLaurentBaseToGeneratedField N hN).toAlgebra
  integralClosure (LaurentPolynomial ℂ) (lpsOriginalGeneratedFunctionField N hN)
def lpsOriginalComplexReciprocalLaurentPolynomialMap :
    Polynomial ℂ →+* LaurentPolynomial ℂ :=
  (LaurentPolynomial.invert (R := ℂ)).toRingHom.comp Polynomial.toLaurent
lemma lpsOriginalComplexReciprocalLaurentPolynomialMap_injective :
    Function.Injective lpsOriginalComplexReciprocalLaurentPolynomialMap :=
  (LaurentPolynomial.invert (R := ℂ)).injective.comp Polynomial.toLaurent_injective
lemma lpsOriginalComplexReciprocalLaurent_isLocalization :
    letI := lpsOriginalComplexReciprocalLaurentPolynomialMap.toAlgebra
    IsLocalization.Away (Polynomial.X : Polynomial ℂ) (LaurentPolynomial ℂ) := by
  have hu (b : Submonoid.powers (Polynomial.X : Polynomial ℂ)) :
      IsUnit (Polynomial.toLaurent (b : Polynomial ℂ)) :=
    IsLocalization.map_units (S := LaurentPolynomial ℂ) b
  have hs (z : LaurentPolynomial ℂ) : ∃ p : Polynomial ℂ ×
      Submonoid.powers (Polynomial.X : Polynomial ℂ),
        z*Polynomial.toLaurent (p.2 : Polynomial ℂ)=Polynomial.toLaurent p.1 :=
    IsLocalization.surj (Submonoid.powers (Polynomial.X : Polynomial ℂ)) z
  let := lpsOriginalComplexReciprocalLaurentPolynomialMap.toAlgebra
  refine
    { map_units := fun b => ?_
      surj := fun z => ?_
      exists_of_eq := fun {x y} h => ?_ }
  · change IsUnit (LaurentPolynomial.invert (Polynomial.toLaurent (b : Polynomial ℂ)))
    exact (hu b).map (LaurentPolynomial.invert (R := ℂ)).toRingHom
  · obtain ⟨p,hp⟩ := hs (LaurentPolynomial.invert z)
    refine ⟨p,?_⟩
    change z*LaurentPolynomial.invert (Polynomial.toLaurent (p.2 : Polynomial ℂ))=
      LaurentPolynomial.invert (Polynomial.toLaurent p.1)
    have hh := congrArg (fun w : LaurentPolynomial ℂ => LaurentPolynomial.invert w) hp
    rw [map_mul] at hh
    have hz : LaurentPolynomial.invert (LaurentPolynomial.invert z)=z :=
      LaurentPolynomial.involutive_invert z
    rw [hz] at hh
    exact hh
  · have hxy := lpsOriginalComplexReciprocalLaurentPolynomialMap_injective h
    refine ⟨1,?_⟩
    simpa only [Submonoid.coe_one,one_mul] using hxy
section ComplexChartOpenImmersions
variable (N : ℕ) (hN : 0 < N)
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
local instance complexGluingDictionary002 : Algebra (Polynomial ℂ) FC :=
  ((algebraMap JC FC).comp (algebraMap (Polynomial ℂ) JC)).toAlgebra
local instance complexGluingDictionary003 : IsScalarTower (Polynomial ℂ) JC FC :=
  .of_algebraMap_eq' rfl
local instance complexGluingDictionary004 : Algebra (LaurentPolynomial ℂ) FC :=
  (lpsOriginalComplexLaurentBaseToGeneratedField N hN).toAlgebra
local instance complexGluingDictionary005 : IsScalarTower (Polynomial ℂ) (LaurentPolynomial ℂ) FC :=
  lpsOriginalComplexLaurentBase_scalarTower N hN
lemma lpsOriginalComplexNormalZeroToLaurent_openImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (lpsOriginalComplexNormalZeroToLaurent N hN))) := by
  let := (lpsOriginalComplexNormalZeroToLaurent N hN).toAlgebra
  let : IsLocalization.Away
      (algebraMap (Polynomial ℂ) (lpsOriginalComplexNormalZeroChart N hN) Polynomial.X)
      (lpsOriginalComplexNormalLaurentChart N hN) :=
    lpsOriginalComplexNormalLaurent_localization N hN
  exact IsOpenImmersion.of_isLocalization
    (algebraMap (Polynomial ℂ) (lpsOriginalComplexNormalZeroChart N hN) Polynomial.X)
lemma lpsOriginalComplexReciprocalLaurentBase_scalarTower :
    letI := lpsOriginalComplexReciprocalLaurentPolynomialMap.toAlgebra
    letI : Algebra (Polynomial ℂ) FC :=
      (lpsOriginalReciprocalComplexFieldPolynomialMap N hN).toAlgebra
    IsScalarTower (Polynomial ℂ) (LaurentPolynomial ℂ) FC := by
  let := lpsOriginalComplexReciprocalLaurentPolynomialMap.toAlgebra
  let : Algebra (Polynomial ℂ) FC :=
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hN).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro p
  change lpsOriginalReciprocalComplexFieldPolynomialMap N hN p =
    algebraMap JC FC (lpsOriginalComplexLaurentBaseFractionMap
      (LaurentPolynomial.invert (Polynomial.toLaurent p)))
  rw [lpsOriginalComplexLaurentBaseFractionMap_reciprocalPolynomial]
  rfl
lemma lpsOriginalComplexNormalInfinityToLaurent_localization :
    letI := lpsOriginalComplexReciprocalLaurentPolynomialMap.toAlgebra
    letI : Algebra (Polynomial ℂ) FC :=
      (lpsOriginalReciprocalComplexFieldPolynomialMap N hN).toAlgebra
    letI := (lpsOriginalComplexNormalInfinityToLaurent N hN).toAlgebra
    IsLocalization.Away
      (algebraMap (Polynomial ℂ) (lpsOriginalComplexNormalInfinityChart N hN) Polynomial.X)
      (lpsOriginalComplexNormalLaurentChart N hN) := by
  let := lpsOriginalComplexReciprocalLaurentPolynomialMap.toAlgebra
  let : SMul (Polynomial ℂ) (LaurentPolynomial ℂ) := Algebra.toSMul
  let : Module (Polynomial ℂ) (LaurentPolynomial ℂ) := Algebra.toModule
  let : Algebra (Polynomial ℂ) FC :=
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hN).toAlgebra
  let := lpsOriginalComplexReciprocalLaurentBase_scalarTower N hN
  let C := lpsOriginalComplexNormalInfinityChart N hN
  let D := lpsOriginalComplexNormalLaurentChart N hN
  let instCD : Algebra C D := (lpsOriginalComplexNormalInfinityToLaurent N hN).toAlgebra
  let : SMul C D := instCD.toSMul
  let : IsScalarTower C D FC :=
    ⟨fun c d l => by
      change (c.val * d.val) * l = c.val * (d.val * l)
      exact mul_assoc _ _ _⟩
  let : IsScalarTower (Polynomial ℂ) C D :=
    .of_algebraMap_eq' (RingHom.ext fun _ => Subtype.ext rfl)
  have hx : algebraMap (Polynomial ℂ) FC Polynomial.X ≠ 0 := by
    change algebraMap JC FC
      (lpsOriginalComplexJFractionInversion
        (algebraMap (Polynomial ℂ) JC Polynomial.X)) ≠ 0
    rw [lpsOriginalComplexJFractionInversion_X]
    apply (map_ne_zero_iff _ (algebraMap JC FC).injective).mpr
    exact inv_ne_zero ((map_ne_zero_iff _
      (IsFractionRing.injective (Polynomial ℂ) JC)).mpr Polynomial.X_ne_zero)
  let : IsLocalization.Away (algebraMap (Polynomial ℂ) FC Polynomial.X) FC :=
    IsLocalization.of_le_isUnit fun y hy => by
      obtain ⟨n, rfl⟩ := hy
      exact (IsUnit.mk0 _ hx).pow n
  let := lpsOriginalComplexReciprocalLaurent_isLocalization
  exact IsLocalization.Away.integralClosure (R := Polynomial ℂ) (S := FC)
    (Rf := LaurentPolynomial ℂ) (Sf := FC) Polynomial.X
lemma lpsOriginalComplexNormalInfinityToLaurent_openImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (lpsOriginalComplexNormalInfinityToLaurent N hN))) := by
  let := lpsOriginalComplexReciprocalLaurentPolynomialMap.toAlgebra
  let : Algebra (Polynomial ℂ) FC :=
    (lpsOriginalReciprocalComplexFieldPolynomialMap N hN).toAlgebra
  let := (lpsOriginalComplexNormalInfinityToLaurent N hN).toAlgebra
  let := lpsOriginalComplexNormalInfinityToLaurent_localization N hN
  exact IsOpenImmersion.of_isLocalization
    (algebraMap (Polynomial ℂ) (lpsOriginalComplexNormalInfinityChart N hN) Polynomial.X)
end ComplexChartOpenImmersions
section NormalizationTensorDiagrams
local instance complexGluingTensorDiagramDictionary001 :
    Algebra (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbedding.toAlgebra
local instance complexGluingTensorDiagramDictionary002 :
    Algebra (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField :=
  lpsOriginalJFractionEmbeddingQ.toAlgebra
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
local instance complexGluingTensorDiagramDictionary003 : Algebra (Polynomial ℤ) FQ :=
  (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
local instance complexGluingTensorDiagramDictionary004 : Algebra (Polynomial ℂ) FC :=
  ((algebraMap JC FC).comp (algebraMap (Polynomial ℂ) JC)).toAlgebra
local instance complexGluingTensorDiagramDictionary005 : IsScalarTower (Polynomial ℂ) JC FC :=
  .of_algebraMap_eq' rfl
local instance complexGluingTensorDiagramDictionary006 : Algebra ℂ FC :=
  ((algebraMap JC FC).comp (algebraMap ℂ JC)).toAlgebra
local instance complexGluingTensorDiagramDictionary007 : IsScalarTower ℂ JC FC :=
  .of_algebraMap_eq' rfl
local instance complexGluingTensorDiagramDictionary008 : IsScalarTower ℂ (Polynomial ℂ) FC :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap JC FC (algebraMap ℂ JC c) =
      algebraMap JC FC (algebraMap (Polynomial ℂ) JC (algebraMap ℂ (Polynomial ℂ) c))
    rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) JC]
local instance complexGluingTensorDiagramDictionary009 : Algebra (LaurentPolynomial ℤ) FQ :=
  (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
local instance complexGluingTensorDiagramDictionary010 : Algebra (LaurentPolynomial ℂ) FC :=
  (lpsOriginalComplexLaurentBaseToGeneratedField N hN).toAlgebra
local instance complexGluingTensorDiagramDictionary011 :
    IsScalarTower (Polynomial ℂ) (LaurentPolynomial ℂ) FC :=
  lpsOriginalComplexLaurentBase_scalarTower N hN
local instance complexGluingTensorDiagramDictionary012 :
    IsScalarTower ℂ (Polynomial ℂ) (LaurentPolynomial ℂ) :=
  IsScalarTower.of_algebraMap_eq fun c => (Polynomial.toLaurentAlg (R := ℂ)).commutes c |>.symm
local instance complexGluingTensorDiagramDictionary013 : IsScalarTower ℂ (LaurentPolynomial ℂ) FC :=
  .to₁₃₄ ℂ (Polynomial ℂ) (LaurentPolynomial ℂ) FC
local notation "ICL" => integralClosure (LaurentPolynomial ℂ) FC
local instance complexGluingTensorDiagramDictionary014 : Algebra ℂ ICL :=
  ((integralClosure (LaurentPolynomial ℂ) FC).restrictScalars ℂ).algebra
local instance complexGluingTensorDiagramDictionary015 :
    Algebra ℤ (lpsOriginalIntegerNormalLaurentChart N hN) :=
  Ring.toIntAlgebra (lpsOriginalIntegerNormalLaurentChart N hN)
local instance complexGluingTensorDiagramDictionary016 :
    Module ℤ (lpsOriginalIntegerNormalLaurentChart N hN) :=
  AddCommGroup.toIntModule (lpsOriginalIntegerNormalLaurentChart N hN)
local instance complexGluingZeroIntegerAlgebra :
    Algebra ℤ (lpsOriginalIntegerNormalZeroChart N hN) :=
  Ring.toIntAlgebra (lpsOriginalIntegerNormalZeroChart N hN)
local instance complexGluingZeroIntegerModule :
    Module ℤ (lpsOriginalIntegerNormalZeroChart N hN) :=
  AddCommGroup.toIntModule (lpsOriginalIntegerNormalZeroChart N hN)
local instance complexGluingInfinityIntegerAlgebra :
    Algebra ℤ (lpsOriginalIntegerNormalInfinityChart N hN) :=
  Ring.toIntAlgebra (lpsOriginalIntegerNormalInfinityChart N hN)
local instance complexGluingInfinityIntegerModule :
    Module ℤ (lpsOriginalIntegerNormalInfinityChart N hN) :=
  AddCommGroup.toIntModule (lpsOriginalIntegerNormalInfinityChart N hN)
local instance complexGluingZeroSelfAlgebra : Algebra (lpsOriginalIntegerNormalZeroChart N hN) (lpsOriginalIntegerNormalZeroChart N hN) := Algebra.id (lpsOriginalIntegerNormalZeroChart N hN)
local instance complexGluingZeroSelfSMul : SMul (lpsOriginalIntegerNormalZeroChart N hN) (lpsOriginalIntegerNormalZeroChart N hN) := Algebra.toSMul
local instance complexGluingZeroSelfModule : Module (lpsOriginalIntegerNormalZeroChart N hN) (lpsOriginalIntegerNormalZeroChart N hN) := Algebra.toModule
local instance complexGluingZeroIntegerSelfTower : IsScalarTower ℤ (lpsOriginalIntegerNormalZeroChart N hN) (lpsOriginalIntegerNormalZeroChart N hN) :=
  ⟨fun z a b => by
    change (z • a) * b = z • (a * b)
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_assoc]⟩
local instance complexGluingInfinitySelfAlgebra : Algebra (lpsOriginalIntegerNormalInfinityChart N hN) (lpsOriginalIntegerNormalInfinityChart N hN) := Algebra.id (lpsOriginalIntegerNormalInfinityChart N hN)
local instance complexGluingInfinitySelfSMul : SMul (lpsOriginalIntegerNormalInfinityChart N hN) (lpsOriginalIntegerNormalInfinityChart N hN) := Algebra.toSMul
local instance complexGluingInfinitySelfModule : Module (lpsOriginalIntegerNormalInfinityChart N hN) (lpsOriginalIntegerNormalInfinityChart N hN) := Algebra.toModule
local instance complexGluingInfinityIntegerSelfTower : IsScalarTower ℤ (lpsOriginalIntegerNormalInfinityChart N hN) (lpsOriginalIntegerNormalInfinityChart N hN) :=
  ⟨fun z a b => by
    change (z • a) * b = z • (a * b)
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_assoc]⟩
local instance complexGluingLaurentSelfAlgebra : Algebra (lpsOriginalIntegerNormalLaurentChart N hN) (lpsOriginalIntegerNormalLaurentChart N hN) := Algebra.id (lpsOriginalIntegerNormalLaurentChart N hN)
local instance complexGluingLaurentSelfSMul : SMul (lpsOriginalIntegerNormalLaurentChart N hN) (lpsOriginalIntegerNormalLaurentChart N hN) := Algebra.toSMul
local instance complexGluingLaurentSelfModule : Module (lpsOriginalIntegerNormalLaurentChart N hN) (lpsOriginalIntegerNormalLaurentChart N hN) := Algebra.toModule
local instance complexGluingLaurentIntegerSelfTower : IsScalarTower ℤ (lpsOriginalIntegerNormalLaurentChart N hN) (lpsOriginalIntegerNormalLaurentChart N hN) :=
  ⟨fun z a b => by
    change (z • a) * b = z • (a * b)
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_assoc]⟩
attribute [local irreducible] lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv
def lpsOriginalComplexZeroIntegerChartRingHom :
    lpsOriginalIntegerNormalZeroChart N hN →+* lpsOriginalComplexNormalZeroChart N hN :=
  normalizationBaseRingHom (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hN).toRingHom
def lpsOriginalComplexInfinityIntegerChartRingHom :
    lpsOriginalIntegerNormalInfinityChart N hN →+*
      lpsOriginalComplexNormalInfinityChart N hN :=
  normalizationBaseRingHom (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hN).toRingHom
def lpsOriginalComplexLaurentIntegerChartRingHom :
    lpsOriginalIntegerNormalLaurentChart N hN →+* lpsOriginalComplexNormalLaurentChart N hN :=
  normalizationBaseRingHom (lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv N hN).toRingHom
lemma lpsOriginalComplexZeroIntegerChartRingHom_apply (x : lpsOriginalIntegerNormalZeroChart N hN) :
    lpsOriginalComplexZeroIntegerChartRingHom N hN x =
      (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hN).toRingHom (1 ⊗ₜ[ℤ] x) :=
  normalizationBaseRingHom_apply (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hN).toRingHom x
lemma lpsOriginalComplexInfinityIntegerChartRingHom_apply (x : lpsOriginalIntegerNormalInfinityChart N hN) :
    lpsOriginalComplexInfinityIntegerChartRingHom N hN x =
      (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hN).toRingHom (1 ⊗ₜ[ℤ] x) :=
  normalizationBaseRingHom_apply (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hN).toRingHom x
lemma lpsOriginalComplexLaurentIntegerChartRingHom_apply (x : lpsOriginalIntegerNormalLaurentChart N hN) :
    lpsOriginalComplexLaurentIntegerChartRingHom N hN x =
      (lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv N hN).toRingHom (1 ⊗ₜ[ℤ] x) := by
  rfl
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexZeroIntegerOverlapRingHomDiagram :
    (lpsOriginalComplexLaurentIntegerChartRingHom N hN).comp
      (lpsOriginalIntegerNormalZeroToLaurent N hN) =
    (lpsOriginalComplexNormalZeroToLaurent N hN).comp
      (lpsOriginalComplexZeroIntegerChartRingHom N hN) := by
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply, RingHom.comp_apply, lpsOriginalComplexLaurentIntegerChartRingHom_apply,
    lpsOriginalComplexZeroIntegerChartRingHom_apply]
  rw [algEquivRingHom_apply, algEquivRingHom_apply]
  apply Subtype.ext
  change (lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv N hN
    ((1 : ℂ) ⊗ₜ[ℤ] lpsOriginalIntegerNormalZeroToLaurent N hN x)).val =
    (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hN
      ((1 : ℂ) ⊗ₜ[ℤ] x)).val
  exact (lpsOriginalIntegerLaurentChartComplexNormalization_tmulValue N hN 1
    (lpsOriginalIntegerNormalZeroToLaurent N hN x)).trans
    (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv_tmulValue N hN 1 x).symm
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexInfinityIntegerOverlapRingHomDiagram :
    (lpsOriginalComplexLaurentIntegerChartRingHom N hN).comp
      (lpsOriginalIntegerNormalInfinityToLaurent N hN) =
    (lpsOriginalComplexNormalInfinityToLaurent N hN).comp
      (lpsOriginalComplexInfinityIntegerChartRingHom N hN) := by
  let : Algebra (Polynomial ℂ) FC := (lpsOriginalReciprocalComplexFieldPolynomialMap N hN).toAlgebra
  let : IsScalarTower ℂ (Polynomial ℂ) FC :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap JC FC (algebraMap ℂ JC c) =
        algebraMap JC FC (lpsOriginalComplexJFractionInversion (algebraMap ℂ JC c))
      rw [lpsOriginalComplexJFractionInversion_constant]
  let : Algebra ℂ (integralClosure (Polynomial ℂ) FC) :=
    ((integralClosure (Polynomial ℂ) FC).restrictScalars ℂ).algebra

  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply, RingHom.comp_apply, lpsOriginalComplexLaurentIntegerChartRingHom_apply,
    lpsOriginalComplexInfinityIntegerChartRingHom_apply]
  rw [algEquivRingHom_apply, algEquivRingHom_apply]
  apply Subtype.ext
  change (lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv N hN
    ((1 : ℂ) ⊗ₜ[ℤ] lpsOriginalIntegerNormalInfinityToLaurent N hN x)).val =
    (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hN
      ((1 : ℂ) ⊗ₜ[ℤ] x)).val
  exact (lpsOriginalIntegerLaurentChartComplexNormalization_tmulValue N hN 1
    (lpsOriginalIntegerNormalInfinityToLaurent N hN x)).trans
    (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv_tmulValue N hN 1 x).symm
def lpsOriginalComplexZeroConstantRingHom :
    ℂ →+* lpsOriginalComplexNormalZeroChart N hN :=
  normalizationConstantRingHom (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hN).toRingHom
def lpsOriginalComplexInfinityConstantRingHom :
    ℂ →+* lpsOriginalComplexNormalInfinityChart N hN :=
  normalizationConstantRingHom (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hN).toRingHom
def lpsOriginalComplexLaurentConstantRingHom :
    ℂ →+* lpsOriginalComplexNormalLaurentChart N hN :=
  normalizationConstantRingHom (lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv N hN).toRingHom
lemma lpsOriginalComplexZeroConstantChartRingHom_apply (x : ℂ) :
    lpsOriginalComplexZeroConstantRingHom N hN x =
      (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hN).toRingHom (x ⊗ₜ[ℤ] 1) :=
  normalizationConstantRingHom_apply (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hN).toRingHom x
lemma lpsOriginalComplexInfinityConstantChartRingHom_apply (x : ℂ) :
    lpsOriginalComplexInfinityConstantRingHom N hN x =
      (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hN).toRingHom (x ⊗ₜ[ℤ] 1) :=
  normalizationConstantRingHom_apply (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hN).toRingHom x
lemma lpsOriginalComplexLaurentConstantChartRingHom_apply (x : ℂ) :
    lpsOriginalComplexLaurentConstantRingHom N hN x =
      (lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv N hN).toRingHom (x ⊗ₜ[ℤ] 1) := by
  rfl
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexZeroConstantOverlapRingHomDiagram :
    (lpsOriginalComplexNormalZeroToLaurent N hN).comp
      (lpsOriginalComplexZeroConstantRingHom N hN) =
    lpsOriginalComplexLaurentConstantRingHom N hN := by
  apply RingHom.ext
  intro c
  rw [RingHom.comp_apply, lpsOriginalComplexLaurentConstantChartRingHom_apply,
    lpsOriginalComplexZeroConstantChartRingHom_apply]
  rw [algEquivRingHom_apply, algEquivRingHom_apply]
  apply Subtype.ext
  change (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv N hN
    (c ⊗ₜ[ℤ] (1 : lpsOriginalIntegerNormalZeroChart N hN))).val =
    (lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv N hN
      (c ⊗ₜ[ℤ] (1 : lpsOriginalIntegerNormalLaurentChart N hN))).val
  exact (lpsOriginalIntegerZeroChartComplexNormalizationAlgEquiv_tmulValue N hN c 1).trans
    (lpsOriginalIntegerLaurentChartComplexNormalization_tmulValue N hN c 1).symm
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexInfinityConstantOverlapRingHomDiagram :
    (lpsOriginalComplexNormalInfinityToLaurent N hN).comp
      (lpsOriginalComplexInfinityConstantRingHom N hN) =
    lpsOriginalComplexLaurentConstantRingHom N hN := by
  let : Algebra (Polynomial ℂ) FC := (lpsOriginalReciprocalComplexFieldPolynomialMap N hN).toAlgebra
  let : IsScalarTower ℂ (Polynomial ℂ) FC :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap JC FC (algebraMap ℂ JC c) =
        algebraMap JC FC (lpsOriginalComplexJFractionInversion (algebraMap ℂ JC c))
      rw [lpsOriginalComplexJFractionInversion_constant]
  let : Algebra ℂ (integralClosure (Polynomial ℂ) FC) :=
    ((integralClosure (Polynomial ℂ) FC).restrictScalars ℂ).algebra

  apply RingHom.ext
  intro c
  rw [RingHom.comp_apply, lpsOriginalComplexLaurentConstantChartRingHom_apply,
    lpsOriginalComplexInfinityConstantChartRingHom_apply]
  rw [algEquivRingHom_apply, algEquivRingHom_apply]
  apply Subtype.ext
  change (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hN
    (c ⊗ₜ[ℤ] (1 : lpsOriginalIntegerNormalInfinityChart N hN))).val =
    (lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv N hN
      (c ⊗ₜ[ℤ] (1 : lpsOriginalIntegerNormalLaurentChart N hN))).val
  exact (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv_tmulValue N hN c 1).trans
    (lpsOriginalIntegerLaurentChartComplexNormalization_tmulValue N hN c 1).symm
end NormalizationTensorDiagrams
def lpsOriginalComplexNormalSchemeChart (N : ℕ) (hN : 0<N) : Bool → Scheme
  | false => Spec (.of (lpsOriginalComplexNormalZeroChart N hN))
  | true => Spec (.of (lpsOriginalComplexNormalInfinityChart N hN))
def lpsOriginalComplexNormalSchemeOverlapMap (N : ℕ) (hN : 0<N) (b : Bool) :
    Spec (.of (lpsOriginalComplexNormalLaurentChart N hN)) ⟶
      lpsOriginalComplexNormalSchemeChart N hN b := by
  cases b with
  | false => exact Spec.map (CommRingCat.ofHom (lpsOriginalComplexNormalZeroToLaurent N hN))
  | true => exact Spec.map (CommRingCat.ofHom (lpsOriginalComplexNormalInfinityToLaurent N hN))
lemma lpsOriginalComplexNormalSchemeOverlapMap_openImmersion
    (N : ℕ) (hN : 0<N) (b : Bool) :
    IsOpenImmersion (lpsOriginalComplexNormalSchemeOverlapMap N hN b) := by
  cases b with
  | false => exact lpsOriginalComplexNormalZeroToLaurent_openImmersion N hN
  | true => exact lpsOriginalComplexNormalInfinityToLaurent_openImmersion N hN
def lpsOriginalComplexNormalSchemeGlueDataPrime (N : ℕ) (hN : 0<N) :
    CategoryTheory.GlueData' Scheme where
  J := Bool
  U := lpsOriginalComplexNormalSchemeChart N hN
  V _ _ _ := Spec (.of (lpsOriginalComplexNormalLaurentChart N hN))
  f i _ _ := lpsOriginalComplexNormalSchemeOverlapMap N hN i
  f_mono i _ _ := by
    let := lpsOriginalComplexNormalSchemeOverlapMap_openImmersion N hN i
    infer_instance
  f_hasPullback i _ _ _ _ := by
    let := lpsOriginalComplexNormalSchemeOverlapMap_openImmersion N hN i
    infer_instance
  t _ _ _ := 𝟙 _
  t' i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)
  t_fac i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)
  t_inv _ _ _ := by simp
  cocycle i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)
def lpsOriginalComplexNormalSchemeGlueData (N : ℕ) (hN : 0<N) :
    Scheme.GlueData := by
  let D := lpsOriginalComplexNormalSchemeGlueDataPrime N hN
  exact
    { toGlueData := CategoryTheory.GlueData.ofGlueData' D
      f_open := fun i j => by
        change IsOpenImmersion (D.f' i j)
        dsimp [CategoryTheory.GlueData'.f']
        split_ifs with h
        · infer_instance
        · let : IsOpenImmersion (D.f i j h) :=
            lpsOriginalComplexNormalSchemeOverlapMap_openImmersion N hN i
          infer_instance }
def lpsOriginalComplexNormalGluedScheme (N : ℕ) (hN : 0<N) : Scheme :=
  (lpsOriginalComplexNormalSchemeGlueData N hN).glued
def lpsOriginalComplexNormalGluedChartMap (N : ℕ) (hN : 0<N) (b : Bool) :
    lpsOriginalComplexNormalSchemeChart N hN b ⟶
      lpsOriginalComplexNormalGluedScheme N hN :=
  (lpsOriginalComplexNormalSchemeGlueData N hN).ι b
def lpsOriginalComplexToIntegerChartMap (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool) :
    lpsOriginalComplexNormalSchemeChart N hN b ⟶
      lpsOriginalIntegerNormalSchemeChart N hN b := by
  cases b with
  | false => exact Spec.map (CommRingCat.ofHom
      (lpsOriginalComplexZeroIntegerChartRingHom N hN))
  | true => exact Spec.map (CommRingCat.ofHom
      (lpsOriginalComplexInfinityIntegerChartRingHom N hN))
lemma lpsOriginalComplexToIntegerChartMap_overlap
    (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool) :
    lpsOriginalComplexNormalSchemeOverlapMap N hN b ≫
      lpsOriginalComplexToIntegerChartMap N hN b =
    Spec.map (CommRingCat.ofHom (lpsOriginalComplexLaurentIntegerChartRingHom N hN)) ≫
      lpsOriginalIntegerNormalSchemeOverlapMap N hN b := by
  cases b <;> change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  · rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (lpsOriginalComplexZeroIntegerOverlapRingHomDiagram N hN).symm
  · rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (lpsOriginalComplexInfinityIntegerOverlapRingHomDiagram N hN).symm
def lpsOriginalComplexChartToIntegerNormal (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool) :
    lpsOriginalComplexNormalSchemeChart N hN b ⟶
      lpsOriginalIntegerNormalGluedScheme N hN :=
  lpsOriginalComplexToIntegerChartMap N hN b ≫ lpsOriginalIntegerNormalGluedChartMap N hN b
lemma lpsOriginalComplexChartToIntegerNormal_overlap (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalComplexNormalSchemeOverlapMap N hN false ≫
      lpsOriginalComplexChartToIntegerNormal N hN false =
    lpsOriginalComplexNormalSchemeOverlapMap N hN true ≫
      lpsOriginalComplexChartToIntegerNormal N hN true := by
  unfold lpsOriginalComplexChartToIntegerNormal
  rw [← Category.assoc, lpsOriginalComplexToIntegerChartMap_overlap,
    Category.assoc, lpsOriginalIntegerNormalGluedOverlap_agreement,
    ← Category.assoc, ← lpsOriginalComplexToIntegerChartMap_overlap, Category.assoc]
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexNormalChartGlueCondition
    (N : ℕ) (hN : 0<N) (T : Scheme)
    (f : (b : Bool) → lpsOriginalComplexNormalSchemeChart N hN b ⟶ T)
    (compatible : lpsOriginalComplexNormalSchemeOverlapMap N hN false ≫ f false =
      lpsOriginalComplexNormalSchemeOverlapMap N hN true ≫ f true) :
    let D := (lpsOriginalComplexNormalSchemeGlueData N hN).toGlueData
    ∀ a : Bool × Bool,
      D.diagram.fst a ≫ f a.1 =
      D.diagram.snd a ≫ f a.2 := by
  let D := (lpsOriginalComplexNormalSchemeGlueData N hN).toGlueData
  change ∀ a : Bool × Bool,
    D.diagram.fst a ≫ f a.1 =
      D.diagram.snd a ≫ f a.2
  rintro ⟨i,j⟩
  change D.f i j ≫ f i =
    (D.t i j ≫ D.f j i) ≫ f j
  cases i <;> cases j
  · simp [D,lpsOriginalComplexNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalComplexNormalSchemeGlueDataPrime]
  · have e : D.V (false,true)=Spec (.of (lpsOriginalComplexNormalLaurentChart N hN)) := by
      simp [D,lpsOriginalComplexNormalSchemeGlueData,
        CategoryTheory.GlueData.ofGlueData',lpsOriginalComplexNormalSchemeGlueDataPrime]
    have h := congrArg (fun f : Spec (.of (lpsOriginalComplexNormalLaurentChart N hN)) ⟶
      T => eqToHom e ≫ f)
      compatible
    simpa [Category.assoc,eqToHom_trans_assoc,D,lpsOriginalComplexNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalComplexNormalSchemeGlueDataPrime] using h
  · have e : D.V (true,false)=Spec (.of (lpsOriginalComplexNormalLaurentChart N hN)) := by
      simp [D,lpsOriginalComplexNormalSchemeGlueData,
        CategoryTheory.GlueData.ofGlueData',lpsOriginalComplexNormalSchemeGlueDataPrime]
    have h := congrArg (fun f : Spec (.of (lpsOriginalComplexNormalLaurentChart N hN)) ⟶
      T => eqToHom e ≫ f)
      compatible.symm
    simpa [Category.assoc,eqToHom_trans_assoc,D,lpsOriginalComplexNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalComplexNormalSchemeGlueDataPrime] using h
  · simp [D,lpsOriginalComplexNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalComplexNormalSchemeGlueDataPrime]
lemma lpsOriginalComplexChartToIntegerNormal_glueCondition
    (N : ℕ) [NeZero N] (hN : 0<N) :
    let D := (lpsOriginalComplexNormalSchemeGlueData N hN).toGlueData
    ∀ a : Bool × Bool,
      D.diagram.fst a ≫ lpsOriginalComplexChartToIntegerNormal N hN a.1 =
      D.diagram.snd a ≫ lpsOriginalComplexChartToIntegerNormal N hN a.2 :=
  lpsOriginalComplexNormalChartGlueCondition N hN
    (lpsOriginalIntegerNormalGluedScheme N hN)
    (lpsOriginalComplexChartToIntegerNormal N hN)
    (lpsOriginalComplexChartToIntegerNormal_overlap N hN)
def lpsOriginalComplexNormalGluedToIntegerNormal (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalComplexNormalGluedScheme N hN ⟶ lpsOriginalIntegerNormalGluedScheme N hN :=
  Multicoequalizer.desc _ _ (lpsOriginalComplexChartToIntegerNormal N hN)
    (lpsOriginalComplexChartToIntegerNormal_glueCondition N hN)
lemma lpsOriginalComplexNormalGluedToIntegerNormal_chart
    (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool) :
    lpsOriginalComplexNormalGluedChartMap N hN b ≫
      lpsOriginalComplexNormalGluedToIntegerNormal N hN =
    lpsOriginalComplexChartToIntegerNormal N hN b :=
  Multicoequalizer.π_desc _ _ _ _ _
def lpsOriginalComplexChartToSpecC (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool) :
    lpsOriginalComplexNormalSchemeChart N hN b ⟶ Spec (.of ℂ) := by
  cases b with
  | false => exact Spec.map (CommRingCat.ofHom (lpsOriginalComplexZeroConstantRingHom N hN))
  | true => exact Spec.map (CommRingCat.ofHom (lpsOriginalComplexInfinityConstantRingHom N hN))
lemma lpsOriginalComplexChartToSpecC_overlap
    (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool) :
    lpsOriginalComplexNormalSchemeOverlapMap N hN b ≫ lpsOriginalComplexChartToSpecC N hN b =
      Spec.map (CommRingCat.ofHom (lpsOriginalComplexLaurentConstantRingHom N hN)) := by
  cases b <;> change Spec.map _ ≫ Spec.map _ = Spec.map _
  · rw [← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (lpsOriginalComplexZeroConstantOverlapRingHomDiagram N hN)
  · rw [← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
      (lpsOriginalComplexInfinityConstantOverlapRingHomDiagram N hN)
def lpsOriginalComplexNormalGluedToSpecC (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalComplexNormalGluedScheme N hN ⟶ Spec (.of ℂ) :=
  Multicoequalizer.desc _ _ (lpsOriginalComplexChartToSpecC N hN)
    (lpsOriginalComplexNormalChartGlueCondition N hN (Spec (.of ℂ))
      (lpsOriginalComplexChartToSpecC N hN)
      ((lpsOriginalComplexChartToSpecC_overlap N hN false).trans
        (lpsOriginalComplexChartToSpecC_overlap N hN true).symm))
lemma lpsOriginalComplexNormalGluedToSpecC_chart
    (N : ℕ) [NeZero N] (hN : 0<N) (b : Bool) :
    lpsOriginalComplexNormalGluedChartMap N hN b ≫ lpsOriginalComplexNormalGluedToSpecC N hN =
      lpsOriginalComplexChartToSpecC N hN b :=
  Multicoequalizer.π_desc _ _ _ _ _
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexNormalGlued_baseSquare
    (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalComplexNormalGluedToSpecC N hN ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ)) =
    lpsOriginalComplexNormalGluedToIntegerNormal N hN ≫
      lpsOriginalIntegerNormalGluedToSpecZ N hN := by
  apply (lpsOriginalComplexNormalSchemeGlueData N hN).openCover.hom_ext
  intro b
  change lpsOriginalComplexNormalGluedChartMap N hN b ≫
      (lpsOriginalComplexNormalGluedToSpecC N hN ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ))) =
    lpsOriginalComplexNormalGluedChartMap N hN b ≫
      (lpsOriginalComplexNormalGluedToIntegerNormal N hN ≫
        lpsOriginalIntegerNormalGluedToSpecZ N hN)
  rw [← Category.assoc, lpsOriginalComplexNormalGluedToSpecC_chart,
    ← Category.assoc, lpsOriginalComplexNormalGluedToIntegerNormal_chart]
  cases b
  · exact lpsOriginalIntegerSpecZ_hom_unique
      (lpsOriginalComplexNormalZeroChart N hN) _ _
  · exact lpsOriginalIntegerSpecZ_hom_unique
      (lpsOriginalComplexNormalInfinityChart N hN) _ _
def lpsOriginalIntegerNormalComplexBaseChange (N : ℕ) (hN : 0<N) : Scheme :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℂ)))
    (lpsOriginalIntegerNormalGluedToSpecZ N hN)
def lpsOriginalComplexNormalToIntegerBaseChange (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalComplexNormalGluedScheme N hN ⟶
      lpsOriginalIntegerNormalComplexBaseChange N hN :=
  pullback.lift (lpsOriginalComplexNormalGluedToSpecC N hN)
    (lpsOriginalComplexNormalGluedToIntegerNormal N hN)
    (lpsOriginalComplexNormalGlued_baseSquare N hN)
end
end QEC.Coding.TannerLiftedProduct


