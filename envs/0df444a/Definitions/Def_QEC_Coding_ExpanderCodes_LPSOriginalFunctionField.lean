-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:55:19.67111+00:00
-- url     : https://prove2.me/theorems/b4836ffa-c736-44e5-afbf-de2b7442075f
-- title:
--   LPSOriginal Function Field
-- statement:
--   Definitions and structural lemmas for LPSOriginal Function Field, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFunctionField.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilated_holomorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_holomorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJPolynomialEvalHom_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJPolynomialEvalHom_injective
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
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
def lpsOriginalHolomorphicSubalgebra : Subalgebra ℂ (ℍ→ℂ) where
  carrier := {f | MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f}
  add_mem' hf hg := hf.add hg
  mul_mem' hf hg := hf.mul hg
  algebraMap_mem' c := (show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun _ : ℍ => c) from mdifferentiable_const)
abbrev LPSOriginalHolomorphicRing := ↥lpsOriginalHolomorphicSubalgebra
instance lpsOriginalHolomorphicRing_noZeroDivisors :
    NoZeroDivisors LPSOriginalHolomorphicRing where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} h := by
    have he : f.val*g.val=0 := congrArg Subtype.val h
    exact ((UpperHalfPlane.mul_eq_zero_iff f.property g.property).mp he).imp
      (fun hf => Subtype.ext hf) (fun hg => Subtype.ext hg)
instance lpsOriginalHolomorphicRing_isDomain :
    IsDomain LPSOriginalHolomorphicRing := NoZeroDivisors.to_isDomain _
def lpsOriginalJHolomorphic : LPSOriginalHolomorphicRing :=
  ⟨lpsOriginalJInvariant,lpsOriginalJInvariant_holomorphic⟩
def lpsOriginalJNHolomorphic (N : ℕ) (hN : 0<N) :
    LPSOriginalHolomorphicRing :=
  ⟨lpsOriginalJDilated N hN,lpsOriginalJDilated_holomorphic N hN⟩
def lpsOriginalJHolomorphicEval : Polynomial ℂ →ₐ[ℂ] LPSOriginalHolomorphicRing :=
  Polynomial.aeval lpsOriginalJHolomorphic
lemma lpsOriginalJHolomorphicEval_apply (P : Polynomial ℂ) (τ : ℍ) :
    (lpsOriginalJHolomorphicEval P).val τ=P.eval (lpsOriginalJInvariant τ) := by
  simp only [lpsOriginalJHolomorphicEval,Polynomial.aeval_subalgebra_coe,
    Polynomial.aeval_fn_apply,Polynomial.coe_aeval_eq_eval]
  rfl
lemma lpsOriginalJHolomorphicEval_injective :
    Function.Injective lpsOriginalJHolomorphicEval := by
  intro P Q h
  apply lpsOriginalJPolynomialEvalHom_injective
  funext τ
  have he := congrArg (fun f : LPSOriginalHolomorphicRing => f.val τ) h
  simpa only [lpsOriginalJHolomorphicEval_apply,lpsOriginalJPolynomialEvalHom_apply] using he
abbrev LPSOriginalHolomorphicFractionField := FractionRing LPSOriginalHolomorphicRing
def lpsOriginalJFractionEmbedding :
    FractionRing (Polynomial ℂ) →+* LPSOriginalHolomorphicFractionField :=
  IsFractionRing.lift (g:=(algebraMap LPSOriginalHolomorphicRing
    LPSOriginalHolomorphicFractionField).comp lpsOriginalJHolomorphicEval.toRingHom)
    ((IsFractionRing.injective LPSOriginalHolomorphicRing
      LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEval_injective)
def lpsOriginalJNInFractionField (N : ℕ) (hN : 0<N) :
    LPSOriginalHolomorphicFractionField :=
  algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
    (lpsOriginalJNHolomorphic N hN)
def lpsOriginalGeneratedFunctionField (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    IntermediateField (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField := by
  letI := lpsOriginalJFractionEmbedding.toAlgebra
  exact IntermediateField.adjoin (FractionRing (Polynomial ℂ))
    {lpsOriginalJNInFractionField N hN}
end
end QEC.Coding.TannerLiftedProduct


