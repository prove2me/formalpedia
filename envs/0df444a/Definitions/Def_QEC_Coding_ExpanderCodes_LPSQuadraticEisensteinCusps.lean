-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
-- name    : QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:59:15.132017+00:00
-- url     : https://prove2.me/theorems/03285f2d-2dff-46c6-980b-855760162df4
-- title:
--   LPSQuadratic Eisenstein Cusps
-- statement:
--   Definitions and structural lemmas for LPSQuadratic Eisenstein Cusps, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCusps.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
lemma lpsE2PrimitiveColumn_det (a c : ℕ) (h : Nat.Coprime a c) :
    Matrix.det !![(a:ℤ),-Nat.gcdB a c;(c:ℤ),Nat.gcdA a c]=1 := by
  have hg := Nat.gcd_eq_gcd_ab a c
  rw [h.gcd_eq_one] at hg
  rw [Matrix.det_fin_two]
  change (a:ℤ)*Nat.gcdA a c-(-Nat.gcdB a c)*(c:ℤ)=1
  linear_combination -hg
def lpsE2PrimitiveColumn (a c : ℕ) (h : Nat.Coprime a c) : SL(2,ℤ) :=
  ⟨!![(a:ℤ),-Nat.gcdB a c;(c:ℤ),Nat.gcdA a c],lpsE2PrimitiveColumn_det a c h⟩
noncomputable def lpsE2DiagonalTranslation (g b : ℝ) (hg : g≠0) : SL(2,ℝ) :=
  ⟨!![g,b;0,g⁻¹],by simp [Matrix.det_fin_two,Matrix.of_apply,hg]⟩
def lpsE2PrimeCuspMatrix (q : ℕ) : SL(2,ℤ) :=
  ⟨!![1,0;(q:ℤ),1],by simp [Matrix.det_fin_two,Matrix.of_apply]⟩
end QEC.Coding.TannerLiftedProduct


