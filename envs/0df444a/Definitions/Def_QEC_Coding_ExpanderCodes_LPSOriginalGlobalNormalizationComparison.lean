-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T07:17:54.120708+00:00
-- url     : https://prove2.me/theorems/94e4afb2-595e-4532-bbf3-7bb9b785e17b
-- title:
--   LPSOriginal Global Normalization Comparison
-- statement:
--   Definitions and structural lemmas for LPSOriginal Global Normalization Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGlobalNormalizationComparison.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_scalarFirstBaseChangedMap_chartProjection
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ChartBaseChange_scalarFirstBaseChangedMap_scalarProjection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalChartBaseChangeIso_complexProjection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalChartBaseChangeIso_integerProjection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGluedOverlap_agreement
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalLaurentBaseChangeIso_complexProjection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalLaurentBaseChangeIso_integerProjection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalToIntegerBaseChange_chart
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalComplexBaseChangedCharts_pullback
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
open QEC.Coding.AlgebraicGeometry.ChartBaseChange
noncomputable section
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalComplexBaseChangedOverlapMap_complexProjection
    (N : ℕ) (hN : 0 < N) (b : Bool) :
    lpsOriginalIntegerNormalComplexBaseChangedOverlapMap N hN b ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  cases b <;> exact scalarFirstBaseChangedMap_scalarProjection _ _ _ _ _
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerNormalComplexBaseChangedOverlapMap_integerProjection
    (N : ℕ) (hN : 0 < N) (b : Bool) :
    lpsOriginalIntegerNormalComplexBaseChangedOverlapMap N hN b ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ lpsOriginalIntegerNormalSchemeOverlapMap N hN b := by
  cases b <;> exact scalarFirstBaseChangedMap_chartProjection _ _ _ _ _
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexNormalLaurentBaseChangeIso_overlap
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    (lpsOriginalComplexNormalLaurentBaseChangeIso N hN).hom ≫
      lpsOriginalIntegerNormalComplexBaseChangedOverlapMap N hN b =
    lpsOriginalComplexNormalSchemeOverlapMap N hN b ≫
      (lpsOriginalComplexNormalChartBaseChangeIso N hN b).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, lpsOriginalIntegerNormalComplexBaseChangedOverlapMap_complexProjection,
      lpsOriginalComplexNormalChartBaseChangeIso_complexProjection]
    rw [lpsOriginalComplexNormalLaurentBaseChangeIso_complexProjection]
    exact (lpsOriginalComplexChartToSpecC_overlap N hN b).symm
  · simp only [Category.assoc, lpsOriginalIntegerNormalComplexBaseChangedOverlapMap_integerProjection,
      lpsOriginalComplexNormalChartBaseChangeIso_integerProjection]
    rw [← Category.assoc, lpsOriginalComplexNormalLaurentBaseChangeIso_integerProjection]
    exact (lpsOriginalComplexToIntegerChartMap_overlap N hN b).symm
set_option backward.isDefEq.respectTransparency false in
def lpsOriginalComplexNormalBaseChangeOverlapIso (N : ℕ) [NeZero N] (hN : 0 < N) :
    Spec (.of (lpsOriginalComplexNormalLaurentChart N hN)) ≅
      pullback ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f false)
        ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f true) :=
  lpsOriginalComplexNormalLaurentBaseChangeIso N hN ≪≫
    (lpsOriginalIntegerNormalComplexBaseChangedCharts_pullback N hN).isoPullback
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexNormalBaseChangeOverlapIso_zeroProjection
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalComplexNormalBaseChangeOverlapIso N hN).hom ≫ pullback.fst _ _ =
      lpsOriginalComplexNormalSchemeOverlapMap N hN false ≫
        (lpsOriginalComplexNormalChartBaseChangeIso N hN false).hom := by
  rw [lpsOriginalComplexNormalBaseChangeOverlapIso, Iso.trans_hom, Category.assoc,
    IsPullback.isoPullback_hom_fst]
  exact lpsOriginalComplexNormalLaurentBaseChangeIso_overlap N hN false
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexNormalBaseChangeOverlapIso_infinityProjection
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    (lpsOriginalComplexNormalBaseChangeOverlapIso N hN).hom ≫ pullback.snd _ _ =
      lpsOriginalComplexNormalSchemeOverlapMap N hN true ≫
        (lpsOriginalComplexNormalChartBaseChangeIso N hN true).hom := by
  rw [lpsOriginalComplexNormalBaseChangeOverlapIso, Iso.trans_hom, Category.assoc,
    IsPullback.isoPullback_hom_snd]
  exact lpsOriginalComplexNormalLaurentBaseChangeIso_overlap N hN true
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false in
def lpsOriginalIntegerBaseChangeToComplexNormalChart (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    (lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).X b ⟶
      lpsOriginalComplexNormalGluedScheme N hN :=
  (lpsOriginalComplexNormalChartBaseChangeIso N hN b).inv ≫
    lpsOriginalComplexNormalGluedChartMap N hN b
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerBaseChangeToComplexNormalChart_zeroInfinity
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    pullback.fst ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f false)
        ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f true) ≫
      lpsOriginalIntegerBaseChangeToComplexNormalChart N hN false =
    pullback.snd _ _ ≫ lpsOriginalIntegerBaseChangeToComplexNormalChart N hN true := by
  apply (cancel_epi (lpsOriginalComplexNormalBaseChangeOverlapIso N hN).hom).mp
  simp only [lpsOriginalIntegerBaseChangeToComplexNormalChart, ← Category.assoc]
  rw [lpsOriginalComplexNormalBaseChangeOverlapIso_zeroProjection,
    lpsOriginalComplexNormalBaseChangeOverlapIso_infinityProjection]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact lpsOriginalComplexNormalGluedOverlap_agreement N hN
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerBaseChangeToComplexNormalChart_compatible
    (N : ℕ) [NeZero N] (hN : 0 < N) (b c : Bool) :
    pullback.fst ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f b)
        ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f c) ≫
      lpsOriginalIntegerBaseChangeToComplexNormalChart N hN b =
    pullback.snd _ _ ≫ lpsOriginalIntegerBaseChangeToComplexNormalChart N hN c := by
  cases b <;> cases c
  · rw [fst_eq_snd_of_mono_eq]
  · exact lpsOriginalIntegerBaseChangeToComplexNormalChart_zeroInfinity N hN
  · apply (cancel_epi (pullbackSymmetry
        ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f false)
        ((lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f true)).hom).mp
    simpa only [← Category.assoc, pullbackSymmetry_hom_comp_fst,
      pullbackSymmetry_hom_comp_snd] using
        (lpsOriginalIntegerBaseChangeToComplexNormalChart_zeroInfinity N hN).symm
  · rw [fst_eq_snd_of_mono_eq]
set_option backward.isDefEq.respectTransparency false in
def lpsOriginalIntegerBaseChangeToComplexNormal (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerNormalComplexBaseChange N hN ⟶
      lpsOriginalComplexNormalGluedScheme N hN :=
  (lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).glueMorphisms
    (lpsOriginalIntegerBaseChangeToComplexNormalChart N hN)
    (lpsOriginalIntegerBaseChangeToComplexNormalChart_compatible N hN)
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalIntegerBaseChangeToComplexNormal_chart
    (N : ℕ) [NeZero N] (hN : 0 < N) (b : Bool) :
    (lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).f b ≫
      lpsOriginalIntegerBaseChangeToComplexNormal N hN =
      lpsOriginalIntegerBaseChangeToComplexNormalChart N hN b :=
  Scheme.Cover.ι_glueMorphisms (lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN)
    (lpsOriginalIntegerBaseChangeToComplexNormalChart N hN)
    (lpsOriginalIntegerBaseChangeToComplexNormalChart_compatible N hN) b
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexNormalToIntegerBaseChange_hom_inv
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalComplexNormalToIntegerBaseChange N hN ≫
      lpsOriginalIntegerBaseChangeToComplexNormal N hN =
      𝟙 (lpsOriginalComplexNormalGluedScheme N hN) := by
  apply (lpsOriginalComplexNormalSchemeGlueData N hN).openCover.hom_ext
  intro b
  change lpsOriginalComplexNormalGluedChartMap N hN b ≫
    (lpsOriginalComplexNormalToIntegerBaseChange N hN ≫
      lpsOriginalIntegerBaseChangeToComplexNormal N hN) =
    lpsOriginalComplexNormalGluedChartMap N hN b ≫ 𝟙 _
  rw [← Category.assoc, lpsOriginalComplexNormalToIntegerBaseChange_chart,
    Category.assoc, lpsOriginalIntegerBaseChangeToComplexNormal_chart]
  simp only [lpsOriginalIntegerBaseChangeToComplexNormalChart, Iso.hom_inv_id_assoc,
    Category.comp_id]
set_option backward.isDefEq.respectTransparency false in
lemma lpsOriginalComplexNormalToIntegerBaseChange_inv_hom
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalIntegerBaseChangeToComplexNormal N hN ≫
      lpsOriginalComplexNormalToIntegerBaseChange N hN =
      𝟙 (lpsOriginalIntegerNormalComplexBaseChange N hN) := by
  apply (lpsOriginalIntegerNormalComplexBaseChangeOpenCover N hN).hom_ext
  intro b
  rw [← Category.assoc, lpsOriginalIntegerBaseChangeToComplexNormal_chart]
  simp only [lpsOriginalIntegerBaseChangeToComplexNormalChart, Category.assoc,
    lpsOriginalComplexNormalToIntegerBaseChange_chart, Iso.inv_hom_id_assoc, Category.comp_id]
def lpsOriginalComplexNormalGluedIntegerBaseChangeIso
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    lpsOriginalComplexNormalGluedScheme N hN ≅ lpsOriginalIntegerNormalComplexBaseChange N hN where
  hom := lpsOriginalComplexNormalToIntegerBaseChange N hN
  inv := lpsOriginalIntegerBaseChangeToComplexNormal N hN
  hom_inv_id := lpsOriginalComplexNormalToIntegerBaseChange_hom_inv N hN
  inv_hom_id := lpsOriginalComplexNormalToIntegerBaseChange_inv_hom N hN
end
end QEC.Coding.TannerLiftedProduct


