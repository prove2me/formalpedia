-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:57:46.583193+00:00
-- url     : https://prove2.me/theorems/20eb3f52-7772-43a0-ba01-45e2348ad429
-- title:
--   LPSOriginal Meromorphic Differentiation
-- statement:
--   Definitions and structural lemmas for LPSOriginal Meromorphic Differentiation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalMeromorphicDifferentiation.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicGerms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue
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
open Filter Topology
noncomputable section
def lpsOriginalMeromorphicGermComplexConstants (U : Set ℂ) :
    ℂ →+* LPSOriginalMeromorphicGermRing U where
  toFun c := ⟨((fun _ : ℂ => c) : Filter.Germ (Filter.codiscreteWithin U) ℂ),
    (fun _ : ℂ => c), MeromorphicOn.const c, rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
def lpsOriginalMeromorphicGermCoefficientDerivative (U : Set ℂ)
    (A : LPSOriginalMeromorphicGermRing U) : LPSOriginalMeromorphicGermRing U :=
  ⟨(deriv A.property.choose : Filter.Germ (Filter.codiscreteWithin U) ℂ),
    deriv A.property.choose, A.property.choose_spec.1.deriv, rfl⟩
lemma lpsOriginalMeromorphicGermCoefficientDerivative_value
    (U : Set ℂ) (A : LPSOriginalMeromorphicGermRing U)
    (f : ℂ → ℂ) (hf : MeromorphicOn f U)
    (he : A.val = (f : Filter.Germ (Filter.codiscreteWithin U) ℂ)) :
    (lpsOriginalMeromorphicGermCoefficientDerivative U A).val =
      (deriv f : Filter.Germ (Filter.codiscreteWithin U) ℂ) := by
  apply Filter.Germ.coe_eq.mpr
  exact A.property.choose_spec.1.deriv_eventuallyEq_codiscreteWithin hf
    (Filter.Germ.coe_eq.mp (A.property.choose_spec.2.symm.trans he))
lemma lpsOriginalMeromorphicGermCoefficientDerivative_add
    (U : Set ℂ) (A B : LPSOriginalMeromorphicGermRing U) :
    lpsOriginalMeromorphicGermCoefficientDerivative U (A+B) =
      lpsOriginalMeromorphicGermCoefficientDerivative U A +
        lpsOriginalMeromorphicGermCoefficientDerivative U B := by
  obtain ⟨f,hf,he⟩ := A.property
  obtain ⟨g,hg,he'⟩ := B.property
  have hab : (A+B).val = (f+g : Filter.Germ (Filter.codiscreteWithin U) ℂ) := by
    change A.val+B.val = _
    rw [he,he']
  apply Subtype.ext
  change (lpsOriginalMeromorphicGermCoefficientDerivative U (A+B)).val =
    (lpsOriginalMeromorphicGermCoefficientDerivative U A).val +
      (lpsOriginalMeromorphicGermCoefficientDerivative U B).val
  rw [lpsOriginalMeromorphicGermCoefficientDerivative_value U (A+B) (f+g) (hf.add hg) hab,
    lpsOriginalMeromorphicGermCoefficientDerivative_value U A f hf he,
    lpsOriginalMeromorphicGermCoefficientDerivative_value U B g hg he']
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hf.analyticAt_mem_codiscreteWithin,
    hg.analyticAt_mem_codiscreteWithin] with z hz hz'
  exact deriv_add hz.differentiableAt hz'.differentiableAt
lemma lpsOriginalMeromorphicGermCoefficientDerivative_mul
    (U : Set ℂ) (A B : LPSOriginalMeromorphicGermRing U) :
    lpsOriginalMeromorphicGermCoefficientDerivative U (A*B) =
      A*lpsOriginalMeromorphicGermCoefficientDerivative U B +
        B*lpsOriginalMeromorphicGermCoefficientDerivative U A := by
  obtain ⟨f,hf,he⟩ := A.property
  obtain ⟨g,hg,he'⟩ := B.property
  have hab : (A*B).val = (f*g : Filter.Germ (Filter.codiscreteWithin U) ℂ) := by
    change A.val*B.val = _
    rw [he,he']
  apply Subtype.ext
  change (lpsOriginalMeromorphicGermCoefficientDerivative U (A*B)).val =
    A.val*(lpsOriginalMeromorphicGermCoefficientDerivative U B).val +
      B.val*(lpsOriginalMeromorphicGermCoefficientDerivative U A).val
  rw [lpsOriginalMeromorphicGermCoefficientDerivative_value U (A*B) (f*g) (hf.mul hg) hab,
    lpsOriginalMeromorphicGermCoefficientDerivative_value U A f hf he,
    lpsOriginalMeromorphicGermCoefficientDerivative_value U B g hg he',he,he']
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hf.analyticAt_mem_codiscreteWithin,
    hg.analyticAt_mem_codiscreteWithin] with z hz hz'
  simpa only [Pi.mul_apply,Pi.add_apply,mul_comm,add_comm] using
    deriv_mul hz.differentiableAt hz'.differentiableAt
lemma lpsOriginalMeromorphicGermCoefficientDerivative_constant
    (U : Set ℂ) (c : ℂ) :
    lpsOriginalMeromorphicGermCoefficientDerivative U
      (lpsOriginalMeromorphicGermComplexConstants U c) = 0 := by
  apply Subtype.ext
  rw [lpsOriginalMeromorphicGermCoefficientDerivative_value U _
    (fun _ : ℂ => c) (MeromorphicOn.const c) rfl]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards with z
  simp only [deriv_const]
section ComplexDerivation
variable (U : Set ℂ)
local instance _p2m_local_instance_fa94dd1928_116 : Algebra ℂ (LPSOriginalMeromorphicGermRing U) :=
  (lpsOriginalMeromorphicGermComplexConstants U).toAlgebra
def lpsOriginalMeromorphicGermCoefficientDerivation :
    Derivation ℂ (LPSOriginalMeromorphicGermRing U)
      (LPSOriginalMeromorphicGermRing U) := by
  let D : LPSOriginalMeromorphicGermRing U →ₗ[ℂ] LPSOriginalMeromorphicGermRing U :=
    { toFun := lpsOriginalMeromorphicGermCoefficientDerivative U
      map_add' := lpsOriginalMeromorphicGermCoefficientDerivative_add U
      map_smul' := by
        intro c A
        change lpsOriginalMeromorphicGermCoefficientDerivative U
          (lpsOriginalMeromorphicGermComplexConstants U c * A) =
            lpsOriginalMeromorphicGermComplexConstants U c *
              lpsOriginalMeromorphicGermCoefficientDerivative U A
        rw [lpsOriginalMeromorphicGermCoefficientDerivative_mul,
          lpsOriginalMeromorphicGermCoefficientDerivative_constant,mul_zero,add_zero] }
  exact Derivation.mk' D (fun A B =>
    lpsOriginalMeromorphicGermCoefficientDerivative_mul U A B)
end ComplexDerivation
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold
noncomputable section
def lpsOriginalHolomorphicCoefficientDerivative (f : LPSOriginalHolomorphicRing) :
    LPSOriginalHolomorphicRing :=
  ⟨fun τ : ℍ => deriv (f.val ∘ UpperHalfPlane.ofComplex) (τ : ℂ), by
    intro τ
    apply UpperHalfPlane.mdifferentiableAt_iff.mpr
    have ha := (UpperHalfPlane.mdifferentiable_iff.mp f.property).analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet
    exact (ha.deriv (τ : ℂ) τ.im_pos).differentiableAt.congr_of_eventuallyEq
      ((UpperHalfPlane.eventuallyEq_coe_comp_ofComplex τ.im_pos).fun_comp
        (deriv (f.val ∘ UpperHalfPlane.ofComplex)))⟩
end
end QEC.Coding.TannerLiftedProduct


