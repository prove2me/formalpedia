-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:03:42.815988+00:00
-- url     : https://prove2.me/theorems/2c0a095b-da58-46f3-b1e1-d19623b4eae3
-- title:
--   LPSOriginal Exact Stabilizer
-- statement:
--   Definitions and structural lemmas for LPSOriginal Exact Stabilizer, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_det
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2IntegerColumn_gcd_pos
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
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
lemma lpsOriginalDilationColumnGcdPos (N : ℕ) (hN : 0<N) (γ : SL(2,ℤ)) :
    0<Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0) := by
  let M : GL (Fin 2) ℝ := lpsE2AffineMatrix N hN 0*Matrix.SpecialLinearGroup.mapGL ℝ γ
  have hd : M.det.val=(N:ℝ) := by
    calc M.det.val=(lpsE2AffineMatrix N hN 0).det.val := by simp [M]
         _=(N:ℝ) := lpsE2AffineMatrix_det N hN 0
  have hp : 0<M.det.val := by rw [hd];exact_mod_cast hN
  apply lpsE2IntegerColumn_gcd_pos M hp ((N:ℤ)*γ 0 0) (γ 1 0) 1
  · simp [M,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply]
  · simp [M,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply]
end
end QEC.Coding.TannerLiftedProduct


