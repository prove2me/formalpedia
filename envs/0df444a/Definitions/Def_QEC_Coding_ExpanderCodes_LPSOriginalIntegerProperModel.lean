-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:50:46.227212+00:00
-- url     : https://prove2.me/theorems/fc0a4ce7-32de-484c-8482-c1321dde8ff7
-- title:
--   LPSOriginal Integer Proper Model
-- statement:
--   Definitions and structural lemmas for LPSOriginal Integer Proper Model, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerProperModel.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalOverlap_localization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalLaurent_isLocalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalNormalOverlap_localization
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
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
abbrev lpsOriginalIntegerNormalZeroChart (N : ℕ) (hN : 0<N) : Type :=
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)
abbrev lpsOriginalIntegerNormalInfinityChart (N : ℕ) (hN : 0<N) : Type :=
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)
abbrev lpsOriginalIntegerNormalLaurentChart (N : ℕ) (hN : 0<N) : Type :=
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)
def lpsOriginalIntegerNormalZeroToLaurent (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalZeroChart N hN →+*
      lpsOriginalIntegerNormalLaurentChart N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  exact lpsOriginalIntegerNormalChartToOverlap N hN
def lpsOriginalIntegerNormalInfinityToLaurent (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalInfinityChart N hN →+*
      lpsOriginalIntegerNormalLaurentChart N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  exact lpsOriginalIntegerReciprocalNormalChartToOverlap N hN
lemma lpsOriginalIntegerNormalZeroToLaurent_openImmersion
    (N : ℕ) (hN : 0<N) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalZeroToLaurent N hN))) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerNormalZeroToLaurent N hN).toAlgebra
  let := lpsOriginalIntegerLaurentBase_scalarTower N hN
  let : IsLocalization.Away
      (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalZeroChart N hN) Polynomial.X)
      (lpsOriginalIntegerNormalLaurentChart N hN) :=
    lpsOriginalIntegerNormalOverlap_localization N hN
  exact IsOpenImmersion.of_isLocalization
    (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalZeroChart N hN) Polynomial.X)
lemma lpsOriginalIntegerNormalInfinityToLaurent_openImmersion
    (N : ℕ) (hN : 0<N) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalInfinityToLaurent N hN))) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerNormalInfinityToLaurent N hN).toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentBase_scalarTower N hN
  let : IsLocalization.Away
      (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN) Polynomial.X)
      (lpsOriginalIntegerNormalLaurentChart N hN) :=
    lpsOriginalIntegerReciprocalNormalOverlap_localization N hN
  exact IsOpenImmersion.of_isLocalization
    (algebraMap (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN) Polynomial.X)
def lpsOriginalIntegerNormalSchemeChart (N : ℕ) (hN : 0<N) : Bool → Scheme
  | false => Spec (.of (lpsOriginalIntegerNormalZeroChart N hN))
  | true => Spec (.of (lpsOriginalIntegerNormalInfinityChart N hN))
def lpsOriginalIntegerNormalSchemeOverlapMap (N : ℕ) (hN : 0<N) (b : Bool) :
    Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
      lpsOriginalIntegerNormalSchemeChart N hN b := by
  cases b with
  | false => exact Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroToLaurent N hN))
  | true => exact Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToLaurent N hN))
lemma lpsOriginalIntegerNormalSchemeOverlapMap_openImmersion
    (N : ℕ) (hN : 0<N) (b : Bool) :
    IsOpenImmersion (lpsOriginalIntegerNormalSchemeOverlapMap N hN b) := by
  cases b with
  | false => exact lpsOriginalIntegerNormalZeroToLaurent_openImmersion N hN
  | true => exact lpsOriginalIntegerNormalInfinityToLaurent_openImmersion N hN
lemma lpsOriginalTwoChartDistinctTripleFalse
    (i j k : Bool) (hij : i≠j) (hik : i≠k) (hjk : j≠k) : False := by
  cases i <;> cases j <;> cases k
  all_goals first | exact hij rfl | exact hik rfl | exact hjk rfl
def lpsOriginalIntegerNormalSchemeGlueDataPrime (N : ℕ) (hN : 0<N) :
    CategoryTheory.GlueData' Scheme where
  J := Bool
  U := lpsOriginalIntegerNormalSchemeChart N hN
  V _ _ _ := Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN))
  f i _ _ := lpsOriginalIntegerNormalSchemeOverlapMap N hN i
  f_mono i _ _ := by
    let := lpsOriginalIntegerNormalSchemeOverlapMap_openImmersion N hN i
    infer_instance
  f_hasPullback i _ _ _ _ := by
    let := lpsOriginalIntegerNormalSchemeOverlapMap_openImmersion N hN i
    infer_instance
  t _ _ _ := 𝟙 _
  t' i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)
  t_fac i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)
  t_inv _ _ _ := by simp
  cocycle i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)
def lpsOriginalIntegerNormalSchemeGlueData (N : ℕ) (hN : 0<N) :
    Scheme.GlueData := by
  let D := lpsOriginalIntegerNormalSchemeGlueDataPrime N hN
  exact
    { toGlueData := CategoryTheory.GlueData.ofGlueData' D
      f_open := fun i j => by
        change IsOpenImmersion (D.f' i j)
        dsimp [CategoryTheory.GlueData'.f']
        split_ifs with h
        · infer_instance
        · let : IsOpenImmersion (D.f i j h) :=
            lpsOriginalIntegerNormalSchemeOverlapMap_openImmersion N hN i
          infer_instance }
def lpsOriginalIntegerNormalGluedScheme (N : ℕ) (hN : 0<N) : Scheme :=
  (lpsOriginalIntegerNormalSchemeGlueData N hN).glued
def lpsOriginalIntegerNormalGluedChartMap (N : ℕ) (hN : 0<N) (b : Bool) :
    lpsOriginalIntegerNormalSchemeChart N hN b ⟶
      lpsOriginalIntegerNormalGluedScheme N hN :=
  (lpsOriginalIntegerNormalSchemeGlueData N hN).ι b
def lpsOriginalIntegerNormalZeroChartToJLine (N : ℕ) (hN : 0<N) :
    Spec (.of (lpsOriginalIntegerNormalZeroChart N hN)) ⟶
      Spec (.of (Polynomial ℤ)) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ)
    (lpsOriginalIntegerNormalZeroChart N hN)))
def lpsOriginalIntegerNormalInfinityChartToJLine (N : ℕ) (hN : 0<N) :
    Spec (.of (lpsOriginalIntegerNormalInfinityChart N hN)) ⟶
      Spec (.of (Polynomial ℤ)) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  exact Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ)
    (lpsOriginalIntegerNormalInfinityChart N hN)))
def lpsOriginalIntegerNormalLaurentChartToJOverlap (N : ℕ) (hN : 0<N) :
    Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
      Spec (.of (LaurentPolynomial ℤ)) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  exact Spec.map (CommRingCat.ofHom (algebraMap (LaurentPolynomial ℤ)
    (lpsOriginalIntegerNormalLaurentChart N hN)))
lemma lpsOriginalIntegerNormalZeroChartToJLine_overlap
    (N : ℕ) (hN : 0<N) :
    Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroToLaurent N hN)) ≫
      lpsOriginalIntegerNormalZeroChartToJLine N hN =
    lpsOriginalIntegerNormalLaurentChartToJOverlap N hN ≫
      Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial ℤ →+* LaurentPolynomial ℤ)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  unfold lpsOriginalIntegerNormalZeroChartToJLine
    lpsOriginalIntegerNormalLaurentChartToJOverlap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro P
  apply Subtype.ext
  exact (lpsOriginalIntegerLaurentBaseToGeneratedField_polynomial N hN P).symm
lemma lpsOriginalIntegerNormalInfinityChartToJLine_overlap
    (N : ℕ) (hN : 0<N) :
    Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToLaurent N hN)) ≫
      lpsOriginalIntegerNormalInfinityChartToJLine N hN =
    lpsOriginalIntegerNormalLaurentChartToJOverlap N hN ≫
      Spec.map (CommRingCat.ofHom lpsOriginalIntegerReciprocalLaurentPolynomialMap) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  unfold lpsOriginalIntegerNormalInfinityChartToJLine
    lpsOriginalIntegerNormalLaurentChartToJOverlap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro P
  apply Subtype.ext
  exact (lpsOriginalIntegerReciprocalLaurentBaseToGeneratedField_polynomial N hN P).symm
def lpsOriginalIntegerProjectiveJOverlapMap (b : Bool) :
    Spec (.of (LaurentPolynomial ℤ)) ⟶ Spec (.of (Polynomial ℤ)) := by
  cases b with
  | false => exact Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial ℤ →+* LaurentPolynomial ℤ))
  | true => exact Spec.map (CommRingCat.ofHom lpsOriginalIntegerReciprocalLaurentPolynomialMap)
lemma lpsOriginalIntegerProjectiveJOverlapMap_openImmersion (b : Bool) :
    IsOpenImmersion (lpsOriginalIntegerProjectiveJOverlapMap b) := by
  cases b with
  | false =>
      exact IsOpenImmersion.of_isLocalization (R:=Polynomial ℤ) (S:=LaurentPolynomial ℤ) Polynomial.X
  | true =>
      let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
      let := lpsOriginalIntegerReciprocalLaurent_isLocalization
      exact IsOpenImmersion.of_isLocalization (R:=Polynomial ℤ) (S:=LaurentPolynomial ℤ) Polynomial.X
def lpsOriginalIntegerProjectiveJGlueDataPrime : CategoryTheory.GlueData' Scheme where
  J := Bool
  U _ := Spec (.of (Polynomial ℤ))
  V _ _ _ := Spec (.of (LaurentPolynomial ℤ))
  f i _ _ := lpsOriginalIntegerProjectiveJOverlapMap i
  f_mono i _ _ := by
    let := lpsOriginalIntegerProjectiveJOverlapMap_openImmersion i
    infer_instance
  f_hasPullback i _ _ _ _ := by
    let := lpsOriginalIntegerProjectiveJOverlapMap_openImmersion i
    infer_instance
  t _ _ _ := 𝟙 _
  t' i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)
  t_fac i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)
  t_inv _ _ _ := by simp
  cocycle i j k hij hik hjk := False.elim (lpsOriginalTwoChartDistinctTripleFalse i j k hij hik hjk)
def lpsOriginalIntegerProjectiveJGlueData : Scheme.GlueData := by
  let D := lpsOriginalIntegerProjectiveJGlueDataPrime
  exact
    { toGlueData := CategoryTheory.GlueData.ofGlueData' D
      f_open := fun i j => by
        change IsOpenImmersion (D.f' i j)
        dsimp [CategoryTheory.GlueData'.f']
        split_ifs with h
        · infer_instance
        · let : IsOpenImmersion (D.f i j h) :=
            lpsOriginalIntegerProjectiveJOverlapMap_openImmersion i
          infer_instance }
def lpsOriginalIntegerProjectiveJLine : Scheme :=
  lpsOriginalIntegerProjectiveJGlueData.glued
def lpsOriginalIntegerProjectiveJChartMap (b : Bool) :
    Spec (.of (Polynomial ℤ)) ⟶ lpsOriginalIntegerProjectiveJLine :=
  lpsOriginalIntegerProjectiveJGlueData.ι b
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerProjectiveJOverlap_agreement :
    lpsOriginalIntegerProjectiveJOverlapMap false ≫
      lpsOriginalIntegerProjectiveJChartMap false=
    lpsOriginalIntegerProjectiveJOverlapMap true ≫
      lpsOriginalIntegerProjectiveJChartMap true := by
  let D := lpsOriginalIntegerProjectiveJGlueData
  change lpsOriginalIntegerProjectiveJOverlapMap false ≫ D.ι false =
    lpsOriginalIntegerProjectiveJOverlapMap true ≫ D.ι true
  have e : D.V (false,true)=Spec (.of (LaurentPolynomial ℤ)) := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerProjectiveJGlueDataPrime]
  have e' : D.V (true,false)=Spec (.of (LaurentPolynomial ℤ)) := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerProjectiveJGlueDataPrime]
  have hf : D.f false true = eqToHom e ≫
      lpsOriginalIntegerProjectiveJOverlapMap false := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerProjectiveJGlueDataPrime]
  have hf' : D.f true false = eqToHom e' ≫
      lpsOriginalIntegerProjectiveJOverlapMap true := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerProjectiveJGlueDataPrime]
  have ht : D.t false true = eqToHom e ≫ eqToHom e'.symm := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerProjectiveJGlueDataPrime]
  have h := D.glue_condition false true
  rw [hf,hf',ht] at h
  have hh := congrArg (fun f : D.V (false,true) ⟶ D.glued => eqToHom e.symm ≫ f) h.symm
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using hh
def lpsOriginalIntegerNormalChartToProjectiveJ (N : ℕ) (hN : 0<N) :
    ∀ b, lpsOriginalIntegerNormalSchemeChart N hN b ⟶
      lpsOriginalIntegerProjectiveJLine := by
  intro b
  cases b with
  | false => exact lpsOriginalIntegerNormalZeroChartToJLine N hN ≫
      lpsOriginalIntegerProjectiveJChartMap false
  | true => exact lpsOriginalIntegerNormalInfinityChartToJLine N hN ≫
      lpsOriginalIntegerProjectiveJChartMap true
lemma lpsOriginalIntegerNormalChartToProjectiveJ_overlap
    (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalSchemeOverlapMap N hN false ≫
      lpsOriginalIntegerNormalChartToProjectiveJ N hN false =
    lpsOriginalIntegerNormalSchemeOverlapMap N hN true ≫
      lpsOriginalIntegerNormalChartToProjectiveJ N hN true := by
  have hb : Spec.map (CommRingCat.ofHom
      (Polynomial.toLaurent : Polynomial ℤ →+* LaurentPolynomial ℤ)) ≫
      lpsOriginalIntegerProjectiveJChartMap false =
    Spec.map (CommRingCat.ofHom lpsOriginalIntegerReciprocalLaurentPolynomialMap) ≫
      lpsOriginalIntegerProjectiveJChartMap true :=
    lpsOriginalIntegerProjectiveJOverlap_agreement
  change Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroToLaurent N hN)) ≫
      (lpsOriginalIntegerNormalZeroChartToJLine N hN ≫
        lpsOriginalIntegerProjectiveJChartMap false) =
    Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToLaurent N hN)) ≫
      (lpsOriginalIntegerNormalInfinityChartToJLine N hN ≫
        lpsOriginalIntegerProjectiveJChartMap true)
  rw [← Category.assoc, lpsOriginalIntegerNormalZeroChartToJLine_overlap,
    Category.assoc, hb, ← Category.assoc,
    ← lpsOriginalIntegerNormalInfinityChartToJLine_overlap, Category.assoc]
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalChartToProjectiveJ_glueCondition
    (N : ℕ) (hN : 0<N) :
    let D := (lpsOriginalIntegerNormalSchemeGlueData N hN).toGlueData
    ∀ a : Bool × Bool,
      D.diagram.fst a ≫ lpsOriginalIntegerNormalChartToProjectiveJ N hN a.1 =
      D.diagram.snd a ≫ lpsOriginalIntegerNormalChartToProjectiveJ N hN a.2 := by
  let D := (lpsOriginalIntegerNormalSchemeGlueData N hN).toGlueData
  change ∀ a : Bool × Bool,
    D.diagram.fst a ≫ lpsOriginalIntegerNormalChartToProjectiveJ N hN a.1 =
      D.diagram.snd a ≫ lpsOriginalIntegerNormalChartToProjectiveJ N hN a.2
  rintro ⟨i,j⟩
  change D.f i j ≫ lpsOriginalIntegerNormalChartToProjectiveJ N hN i =
    (D.t i j ≫ D.f j i) ≫ lpsOriginalIntegerNormalChartToProjectiveJ N hN j
  cases i <;> cases j
  · simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime]
  · have e : D.V (false,true)=Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) := by
      simp [D,lpsOriginalIntegerNormalSchemeGlueData,
        CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
    have h := congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
      lpsOriginalIntegerProjectiveJLine => eqToHom e ≫ f)
      (lpsOriginalIntegerNormalChartToProjectiveJ_overlap N hN)
    simpa [Category.assoc,eqToHom_trans_assoc,D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime] using h
  · have e : D.V (true,false)=Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) := by
      simp [D,lpsOriginalIntegerNormalSchemeGlueData,
        CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
    have h := congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) ⟶
      lpsOriginalIntegerProjectiveJLine => eqToHom e ≫ f)
      (lpsOriginalIntegerNormalChartToProjectiveJ_overlap N hN).symm
    simpa [Category.assoc,eqToHom_trans_assoc,D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime] using h
  · simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime]
def lpsOriginalIntegerNormalGluedToProjectiveJ (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalGluedScheme N hN ⟶ lpsOriginalIntegerProjectiveJLine :=
  Multicoequalizer.desc _ _ (lpsOriginalIntegerNormalChartToProjectiveJ N hN)
    (lpsOriginalIntegerNormalChartToProjectiveJ_glueCondition N hN)
def lpsOriginalIntegerNormalChartProjection (N : ℕ) (hN : 0<N) :
    ∀ b, lpsOriginalIntegerNormalSchemeChart N hN b ⟶ Spec (.of (Polynomial ℤ)) := by
  intro b
  cases b with
  | false => exact lpsOriginalIntegerNormalZeroChartToJLine N hN
  | true => exact lpsOriginalIntegerNormalInfinityChartToJLine N hN
def lpsOriginalIntegerProjectiveJChartToSpecZ :
    Spec (.of (Polynomial ℤ)) ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom Polynomial.C)
lemma lpsOriginalIntegerProjectiveJOverlap_compSpecZ (b : Bool) :
    lpsOriginalIntegerProjectiveJOverlapMap b ≫
      lpsOriginalIntegerProjectiveJChartToSpecZ =
    Spec.map (CommRingCat.ofHom (algebraMap ℤ (LaurentPolynomial ℤ))) := by
  cases b with
  | false =>
      unfold lpsOriginalIntegerProjectiveJOverlapMap
        lpsOriginalIntegerProjectiveJChartToSpecZ
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      exact (Polynomial.toLaurent_C z).trans (LaurentPolynomial.C_eq_algebraMap z)
  | true =>
      unfold lpsOriginalIntegerProjectiveJOverlapMap
        lpsOriginalIntegerProjectiveJChartToSpecZ
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      change LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C z)) = _
      rw [Polynomial.toLaurent_C,LaurentPolynomial.invert_C,LaurentPolynomial.C_eq_algebraMap]
      rfl
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerProjectiveJChartToSpecZ_glueCondition :
    let D := lpsOriginalIntegerProjectiveJGlueData.toGlueData
    ∀ a : Bool × Bool, D.diagram.fst a ≫ lpsOriginalIntegerProjectiveJChartToSpecZ =
      D.diagram.snd a ≫ lpsOriginalIntegerProjectiveJChartToSpecZ := by
  let D := lpsOriginalIntegerProjectiveJGlueData.toGlueData
  change ∀ a : Bool × Bool, D.diagram.fst a ≫ lpsOriginalIntegerProjectiveJChartToSpecZ =
    D.diagram.snd a ≫ lpsOriginalIntegerProjectiveJChartToSpecZ
  rintro ⟨i,j⟩
  change D.f i j ≫ lpsOriginalIntegerProjectiveJChartToSpecZ =
    (D.t i j ≫ D.f j i) ≫ lpsOriginalIntegerProjectiveJChartToSpecZ
  have h : lpsOriginalIntegerProjectiveJOverlapMap false ≫
      lpsOriginalIntegerProjectiveJChartToSpecZ =
    lpsOriginalIntegerProjectiveJOverlapMap true ≫
      lpsOriginalIntegerProjectiveJChartToSpecZ :=
    (lpsOriginalIntegerProjectiveJOverlap_compSpecZ false).trans
      (lpsOriginalIntegerProjectiveJOverlap_compSpecZ true).symm
  cases i <;> cases j
  · simp [D,lpsOriginalIntegerProjectiveJGlueData,CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f',lpsOriginalIntegerProjectiveJGlueDataPrime]
  · have e : D.V (false,true)=Spec (.of (LaurentPolynomial ℤ)) := by
      simp [D,lpsOriginalIntegerProjectiveJGlueData,CategoryTheory.GlueData.ofGlueData',
        lpsOriginalIntegerProjectiveJGlueDataPrime]
    have he := congrArg (fun f : Spec (.of (LaurentPolynomial ℤ)) ⟶ Spec (.of ℤ) => eqToHom e ≫ f) h
    simpa [Category.assoc,eqToHom_trans_assoc,D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerProjectiveJGlueDataPrime] using he
  · have e : D.V (true,false)=Spec (.of (LaurentPolynomial ℤ)) := by
      simp [D,lpsOriginalIntegerProjectiveJGlueData,CategoryTheory.GlueData.ofGlueData',
        lpsOriginalIntegerProjectiveJGlueDataPrime]
    have he := congrArg (fun f : Spec (.of (LaurentPolynomial ℤ)) ⟶ Spec (.of ℤ) => eqToHom e ≫ f) h.symm
    simpa [Category.assoc,eqToHom_trans_assoc,D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerProjectiveJGlueDataPrime] using he
  · simp [D,lpsOriginalIntegerProjectiveJGlueData,CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f',lpsOriginalIntegerProjectiveJGlueDataPrime]
def lpsOriginalIntegerProjectiveJLineToSpecZ :
    lpsOriginalIntegerProjectiveJLine ⟶ Spec (.of ℤ) :=
  Multicoequalizer.desc _ _ (fun _ => lpsOriginalIntegerProjectiveJChartToSpecZ)
    lpsOriginalIntegerProjectiveJChartToSpecZ_glueCondition
def lpsOriginalIntegerProjectiveJAffinePoint
    (R : Type) [CommRing R] (b : Bool) (x : R) :
    Spec (.of R) ⟶ lpsOriginalIntegerProjectiveJLine :=
  Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom R) x)) ≫
    lpsOriginalIntegerProjectiveJChartMap b
def lpsOriginalIntegerNormalGluedToSpecZ (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalGluedScheme N hN ⟶ Spec (.of ℤ) :=
  lpsOriginalIntegerNormalGluedToProjectiveJ N hN ≫
    lpsOriginalIntegerProjectiveJLineToSpecZ
end
end QEC.Coding.TannerLiftedProduct


