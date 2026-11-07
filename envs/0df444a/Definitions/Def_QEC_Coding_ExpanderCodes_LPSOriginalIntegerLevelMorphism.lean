-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T03:09:24.520266+00:00
-- url     : https://prove2.me/theorems/5f86343d-334a-4b51-8df2-d6185f831ad7
-- title:
--   LPSOriginal Integer Level Morphism
-- statement:
--   Definitions and structural lemmas for LPSOriginal Integer Level Morphism, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelMorphism.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_level_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedOverlap_agreement
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
def lpsOriginalRationalLevelInclusion
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hN →ₐ[FractionRing (Polynomial ℚ)]
      lpsOriginalGeneratedFunctionFieldQ M hM := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact IntermediateField.inclusion
    (lpsOriginalGeneratedFunctionFieldQ_level_le N M hNM h4N hN hM)
def lpsOriginalIntegerNormalZeroLevelPullback
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalZeroChart N hN →+*
      lpsOriginalIntegerNormalZeroChart M hM := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField M hM).toAlgebra
  let f : lpsOriginalGeneratedFunctionFieldQ N hN →ₐ[Polynomial ℤ]
      lpsOriginalGeneratedFunctionFieldQ M hM :=
    { (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom with
      commutes' := fun P => by apply Subtype.ext; rfl }
  exact f.mapIntegralClosure.toRingHom
def lpsOriginalIntegerNormalInfinityLevelPullback
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalInfinityChart N hN →+*
      lpsOriginalIntegerNormalInfinityChart M hM := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField M hM).toAlgebra
  let f : lpsOriginalGeneratedFunctionFieldQ N hN →ₐ[Polynomial ℤ]
      lpsOriginalGeneratedFunctionFieldQ M hM :=
    { (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom with
      commutes' := fun P => by apply Subtype.ext; rfl }
  exact f.mapIntegralClosure.toRingHom
def lpsOriginalIntegerNormalLaurentLevelPullback
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalLaurentChart N hN →+*
      lpsOriginalIntegerNormalLaurentChart M hM := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  letI := (lpsOriginalIntegerLaurentBaseToGeneratedField M hM).toAlgebra
  let f : lpsOriginalGeneratedFunctionFieldQ N hN →ₐ[LaurentPolynomial ℤ]
      lpsOriginalGeneratedFunctionFieldQ M hM :=
    { (lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom with
      commutes' := fun P => by apply Subtype.ext; rfl }
  exact f.mapIntegralClosure.toRingHom
lemma lpsOriginalIntegerNormalZeroLevelPullback_overlap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    (lpsOriginalIntegerNormalZeroToLaurent M hM).comp
      (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM) =
    (lpsOriginalIntegerNormalLaurentLevelPullback N M hNM h4N hN hM).comp
      (lpsOriginalIntegerNormalZeroToLaurent N hN) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rfl
lemma lpsOriginalIntegerNormalInfinityLevelPullback_overlap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    (lpsOriginalIntegerNormalInfinityToLaurent M hM).comp
      (lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM) =
    (lpsOriginalIntegerNormalLaurentLevelPullback N M hNM h4N hN hM).comp
      (lpsOriginalIntegerNormalInfinityToLaurent N hN) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rfl
def lpsOriginalIntegerNormalSchemeLevelChartMap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (b : Bool) :
    lpsOriginalIntegerNormalSchemeChart M hM b ⟶
      lpsOriginalIntegerNormalSchemeChart N hN b := by
  cases b with
  | false => exact Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM))
  | true => exact Spec.map (CommRingCat.ofHom
      (lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM))
def lpsOriginalIntegerNormalSchemeLevelOverlapMap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    Spec (.of (lpsOriginalIntegerNormalLaurentChart M hM)) ⟶
      Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) :=
  Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalLaurentLevelPullback N M hNM h4N hN hM))
lemma lpsOriginalIntegerNormalSchemeLevelChartMap_overlap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (b : Bool) :
    lpsOriginalIntegerNormalSchemeOverlapMap M hM b ≫
      lpsOriginalIntegerNormalSchemeLevelChartMap N M hNM h4N hN hM b =
    lpsOriginalIntegerNormalSchemeLevelOverlapMap N M hNM h4N hN hM ≫
      lpsOriginalIntegerNormalSchemeOverlapMap N hN b := by
  cases b
  · change Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroToLaurent M hM)) ≫
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM)) =
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalLaurentLevelPullback N M hNM h4N hN hM)) ≫
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroToLaurent N hN))
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : lpsOriginalIntegerNormalZeroChart N hN →+*
      lpsOriginalIntegerNormalLaurentChart M hM => Spec.map (CommRingCat.ofHom f))
      (lpsOriginalIntegerNormalZeroLevelPullback_overlap N M hNM h4N hN hM)
  · change Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToLaurent M hM)) ≫
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM)) =
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalLaurentLevelPullback N M hNM h4N hN hM)) ≫
      Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityToLaurent N hN))
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : lpsOriginalIntegerNormalInfinityChart N hN →+*
      lpsOriginalIntegerNormalLaurentChart M hM => Spec.map (CommRingCat.ofHom f))
      (lpsOriginalIntegerNormalInfinityLevelPullback_overlap N M hNM h4N hN hM)
def lpsOriginalIntegerNormalLevelToLower
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (b : Bool) :
    lpsOriginalIntegerNormalSchemeChart M hM b ⟶
      lpsOriginalIntegerNormalGluedScheme N hN :=
  lpsOriginalIntegerNormalSchemeLevelChartMap N M hNM h4N hN hM b ≫
    lpsOriginalIntegerNormalGluedChartMap N hN b
lemma lpsOriginalIntegerNormalLevelToLower_overlap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalSchemeOverlapMap M hM false ≫
      lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM false =
    lpsOriginalIntegerNormalSchemeOverlapMap M hM true ≫
      lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM true := by
  unfold lpsOriginalIntegerNormalLevelToLower
  rw [← Category.assoc, lpsOriginalIntegerNormalSchemeLevelChartMap_overlap,
    Category.assoc, lpsOriginalIntegerNormalGluedOverlap_agreement,
    ← Category.assoc, ← lpsOriginalIntegerNormalSchemeLevelChartMap_overlap,
    Category.assoc]
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalLevelToLower_glueCondition
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    let D := (lpsOriginalIntegerNormalSchemeGlueData M hM).toGlueData
    ∀ a : Bool × Bool,
      D.diagram.fst a ≫ lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM a.1 =
      D.diagram.snd a ≫ lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM a.2 := by
  let D := (lpsOriginalIntegerNormalSchemeGlueData M hM).toGlueData
  change ∀ a : Bool × Bool,
    D.diagram.fst a ≫ lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM a.1 =
      D.diagram.snd a ≫ lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM a.2
  rintro ⟨i,j⟩
  change D.f i j ≫ lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM i =
    (D.t i j ≫ D.f j i) ≫ lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM j
  cases i <;> cases j
  · simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime]
  · have e : D.V (false,true)=Spec (.of (lpsOriginalIntegerNormalLaurentChart M hM)) := by
      simp [D,lpsOriginalIntegerNormalSchemeGlueData,
        CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
    have h := congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart M hM)) ⟶
      lpsOriginalIntegerNormalGluedScheme N hN => eqToHom e ≫ f)
      (lpsOriginalIntegerNormalLevelToLower_overlap N M hNM h4N hN hM)
    simpa [Category.assoc,eqToHom_trans_assoc,D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime] using h
  · have e : D.V (true,false)=Spec (.of (lpsOriginalIntegerNormalLaurentChart M hM)) := by
      simp [D,lpsOriginalIntegerNormalSchemeGlueData,
        CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
    have h := congrArg (fun f : Spec (.of (lpsOriginalIntegerNormalLaurentChart M hM)) ⟶
      lpsOriginalIntegerNormalGluedScheme N hN => eqToHom e ≫ f)
      (lpsOriginalIntegerNormalLevelToLower_overlap N M hNM h4N hN hM).symm
    simpa [Category.assoc,eqToHom_trans_assoc,D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime] using h
  · simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime]
def lpsOriginalIntegerNormalGluedForgetLevel
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalGluedScheme M hM ⟶
      lpsOriginalIntegerNormalGluedScheme N hN :=
  Multicoequalizer.desc _ _ (lpsOriginalIntegerNormalLevelToLower N M hNM h4N hN hM)
    (lpsOriginalIntegerNormalLevelToLower_glueCondition N M hNM h4N hN hM)
end
end QEC.Coding.TannerLiftedProduct


