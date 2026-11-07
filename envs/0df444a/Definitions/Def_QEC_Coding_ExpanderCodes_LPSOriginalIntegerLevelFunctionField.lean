-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T04:08:44.763628+00:00
-- url     : https://prove2.me/theorems/84390f55-b1ae-41a2-ba2e-3a9d64592a71
-- title:
--   LPSOriginal Integer Level Function Field
-- statement:
--   Definitions and structural lemmas for LPSOriginal Integer Level Function Field, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerLevelFunctionField.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedChartMap_openImmersion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGluedForgetLevel_chart
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalInfinityLevelPullback_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalZeroLevelPullback_injective
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
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
lemma lpsOriginalInjectiveSpecMap_generic
    (R S : CommRingCat) [IsDomain R] [IsDomain S]
    (f : R ⟶ S) (hf : Function.Injective f) :
    Spec.map f (genericPoint (Spec S)) = genericPoint (Spec R) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  change PrimeSpectrum.comap f.hom ⊥ = ⊥
  apply PrimeSpectrum.ext
  ext r
  change f.hom r = 0 ↔ r = 0
  exact ⟨fun h => hf (by simpa only [map_zero] using h), fun h => by rw [h, map_zero]⟩
lemma lpsOriginalIntegerNormalSchemeLevelChartMap_generic
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (b : Bool) :
    letI := lpsOriginalIntegerNormalSchemeChart_integral N hN b
    letI := lpsOriginalIntegerNormalSchemeChart_integral M hM b
    lpsOriginalIntegerNormalSchemeLevelChartMap N M hNM h4N hN hM b
      (genericPoint (lpsOriginalIntegerNormalSchemeChart M hM b)) =
        genericPoint (lpsOriginalIntegerNormalSchemeChart N hN b) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  cases b
  · let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalIntegerBaseToGeneratedField M hM).toAlgebra
    exact lpsOriginalInjectiveSpecMap_generic _ _
      (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroLevelPullback N M hNM h4N hN hM))
      (lpsOriginalIntegerNormalZeroLevelPullback_injective N M hNM h4N hN hM)
  · let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField M hM).toAlgebra
    exact lpsOriginalInjectiveSpecMap_generic _ _
      (CommRingCat.ofHom (lpsOriginalIntegerNormalInfinityLevelPullback N M hNM h4N hN hM))
      (lpsOriginalIntegerNormalInfinityLevelPullback_injective N M hNM h4N hN hM)
lemma lpsOriginalIntegerNormalGluedForgetLevel_generic
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM
      (genericPoint (lpsOriginalIntegerNormalGluedScheme M hM)) =
        genericPoint (lpsOriginalIntegerNormalGluedScheme N hN) := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  let := lpsOriginalIntegerNormalSchemeChart_integral N hN false
  let := lpsOriginalIntegerNormalSchemeChart_integral M hM false
  let := lpsOriginalIntegerNormalGluedChartMap_openImmersion N hN false
  let := lpsOriginalIntegerNormalGluedChartMap_openImmersion M hM false
  have hm := genericPoint_eq_of_isOpenImmersion
    (lpsOriginalIntegerNormalGluedChartMap M hM false)
  have hn := genericPoint_eq_of_isOpenImmersion
    (lpsOriginalIntegerNormalGluedChartMap N hN false)
  have e := congrArg (fun f : lpsOriginalIntegerNormalSchemeChart M hM false ⟶
    lpsOriginalIntegerNormalGluedScheme N hN =>
      f (genericPoint (lpsOriginalIntegerNormalSchemeChart M hM false)))
      (lpsOriginalIntegerNormalGluedForgetLevel_chart N M hNM h4N hN hM false)
  simpa only [Scheme.Hom.comp_apply, hm, hn,
    lpsOriginalIntegerNormalSchemeLevelChartMap_generic] using e
def lpsOriginalIntegerNormalLevelFunctionFieldPullback
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    (lpsOriginalIntegerNormalGluedScheme N hN).functionField →+*
      (lpsOriginalIntegerNormalGluedScheme M hM).functionField := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  let f := lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM
  let X := lpsOriginalIntegerNormalGluedScheme N hN
  let Y := lpsOriginalIntegerNormalGluedScheme M hM
  have hη : f (genericPoint Y) = genericPoint X :=
    lpsOriginalIntegerNormalGluedForgetLevel_generic N M hNM h4N hN hM
  exact (eqToHom (congrArg X.presheaf.stalk hη.symm) ≫
    f.stalkMap (genericPoint Y)).hom
def lpsOriginalIntegerNormalGeneratedFieldPoint
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Spec (.of (lpsOriginalGeneratedFunctionFieldQ N hN)) ⟶
      lpsOriginalIntegerNormalGluedScheme N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact Spec.map (CommRingCat.ofHom (algebraMap
    (lpsOriginalIntegerNormalZeroChart N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN))) ≫
        lpsOriginalIntegerNormalGluedChartMap N hN false
universe u
end
end QEC.Coding.TannerLiftedProduct


