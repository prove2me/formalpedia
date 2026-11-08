-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHeckeRealSpectrum
-- name    : QEC_Coding_ExpanderCodes_LPSCuspHeckeRealSpectrum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T13:01:48.512209+00:00
-- url     : https://prove2.me/theorems/6048e96f-e167-4aa4-a0b5-32fa635055c3
-- title:
--   LPSCusp Hecke Real Spectrum
-- statement:
--   Definitions and structural lemmas for LPSCusp Hecke Real Spectrum, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHeckeRealSpectrum.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonAdjunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
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
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped UpperHalfPlane ModularForm MatrixGroups
noncomputable section
def lpsCuspFirstCoefficient (N : ℕ) :
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 →ₗ[ℂ] ℂ where
  toFun f := PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 f)
  map_add' f g := by
    simp only [FunLike.coe_add, ModularForm.qExpansion_add (by norm_num : (0:ℝ)<1)
      (by simp) f g,map_add]
  map_smul' c f := by
    simp only [FunLike.coe_smul, ModularForm.qExpansion_smul (by norm_num : (0:ℝ)<1)
      (by simp) c f,PowerSeries.coeff_smul,smul_eq_mul,RingHom.id_apply]
end
end QEC.Coding.TannerLiftedProduct


