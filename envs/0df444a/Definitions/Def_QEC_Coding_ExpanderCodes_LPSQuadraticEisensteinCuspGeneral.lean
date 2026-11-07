-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
-- name    : QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:59:47.573197+00:00
-- url     : https://prove2.me/theorems/97262d11-eae2-48ad-8ac2-0db1b1e9dfa2
-- title:
--   LPSQuadratic Eisenstein Cusp General
-- statement:
--   Definitions and structural lemmas for LPSQuadratic Eisenstein Cusp General, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinCuspGeneral.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
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
lemma lpsE2IntegerPrimitiveColumn_det (a c : ℤ) (h : Int.gcd a c=1) :
    Matrix.det !![a,-Int.gcdB a c;c,Int.gcdA a c]=1 := by
  have hg := Int.gcd_eq_gcd_ab a c
  rw [h] at hg
  rw [Matrix.det_fin_two]
  change a*Int.gcdA a c-(-Int.gcdB a c)*c=1
  linear_combination -hg
def lpsE2IntegerPrimitiveColumn (a c : ℤ) (h : Int.gcd a c=1) : SL(2,ℤ) :=
  ⟨!![a,-Int.gcdB a c;c,Int.gcdA a c],lpsE2IntegerPrimitiveColumn_det a c h⟩
noncomputable def lpsE2AffineMatrix (m : ℕ) (hm : 0<m) (r : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(m:ℝ),r;0,1]
    (by simpa [Matrix.det_fin_two,Matrix.of_apply] using
      (show (m:ℝ)≠0 by exact_mod_cast hm.ne'))
noncomputable def lpsQuadraticE2Dilate (q m : ℕ) [Fact q.Prime] (hm : 0<m) (z : ℍ) : ℂ :=
  lpsQuadraticE2Twist q (lpsE2AffineMatrix m hm 0 • z)
end QEC.Coding.TannerLiftedProduct


