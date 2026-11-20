-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:50:29.125235+00:00
-- url     : https://prove2.me/theorems/67108ba8-6366-49a7-80e1-29356809c086
-- title:
--   LPSOriginal Second Integer Hecke
-- statement:
--   Definitions and structural lemmas for LPSOriginal Second Integer Hecke, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSecondIntegerHecke.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
def lpsOriginalRationalFrickeLevelPullback
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hN →+* lpsOriginalGeneratedFunctionFieldQ M hM := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (lpsOriginalRationalFrickePullback M hM).comp
    ((lpsOriginalRationalLevelInclusion N M hNM h4N hN hM).toRingHom.comp
      (lpsOriginalRationalFrickePullback N hN))
def lpsOriginalIntegerNormalGluedSecondLevelMap
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    lpsOriginalIntegerNormalGluedScheme M hM ⟶ lpsOriginalIntegerNormalGluedScheme N hN :=
  (lpsOriginalIntegerNormalGluedFrickeIso M hM).hom ≫
    lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM ≫
      (lpsOriginalIntegerNormalGluedFrickeIso N hN).hom
lemma lpsOriginalIntegerNormalGluedFricke_generic
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    lpsOriginalIntegerNormalGluedFricke N hN
      (genericPoint (lpsOriginalIntegerNormalGluedScheme N hN)) =
        genericPoint (lpsOriginalIntegerNormalGluedScheme N hN) := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let : IsIso (lpsOriginalIntegerNormalGluedFricke N hN) :=
    inferInstanceAs (IsIso (lpsOriginalIntegerNormalGluedFrickeIso N hN).hom)
  exact genericPoint_eq_of_isOpenImmersion _
lemma lpsOriginalIntegerNormalGluedSecondLevelMap_generic
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM
      (genericPoint (lpsOriginalIntegerNormalGluedScheme M hM)) =
        genericPoint (lpsOriginalIntegerNormalGluedScheme N hN) := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  simp only [lpsOriginalIntegerNormalGluedSecondLevelMap,
    lpsOriginalIntegerNormalGluedFrickeIso, Scheme.Hom.comp_apply,
    lpsOriginalIntegerNormalGluedFricke_generic, lpsOriginalIntegerNormalGluedForgetLevel_generic]
def lpsOriginalIntegerNormalSecondLevelFunctionFieldPullback
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hN
    letI := lpsOriginalIntegerNormalGluedScheme_integral M hM
    (lpsOriginalIntegerNormalGluedScheme N hN).functionField →+*
      (lpsOriginalIntegerNormalGluedScheme M hM).functionField := by
  let := lpsOriginalIntegerNormalGluedScheme_integral N hN
  let := lpsOriginalIntegerNormalGluedScheme_integral M hM
  let f := lpsOriginalIntegerNormalGluedSecondLevelMap N M hNM h4N hN hM
  let X := lpsOriginalIntegerNormalGluedScheme N hN
  let Y := lpsOriginalIntegerNormalGluedScheme M hM
  have hη : f (genericPoint Y) = genericPoint X :=
    lpsOriginalIntegerNormalGluedSecondLevelMap_generic N M hNM h4N hN hM
  exact (eqToHom (congrArg X.presheaf.stalk hη.symm) ≫ f.stalkMap (genericPoint Y)).hom
end
end QEC.Coding.TannerLiftedProduct


