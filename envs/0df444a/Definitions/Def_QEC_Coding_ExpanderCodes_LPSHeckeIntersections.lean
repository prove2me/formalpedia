-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeIntersections
-- name    : QEC_Coding_ExpanderCodes_LPSHeckeIntersections
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:12:15.786001+00:00
-- url     : https://prove2.me/theorems/40dd5cc8-99eb-430c-a29a-ab1e4fde7aa3
-- title:
--   LPSHecke Intersections
-- statement:
--   Definitions and structural lemmas for LPSHecke Intersections, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeIntersections.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
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
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
def lpsUpperCongruence (p : ℕ) : Subgroup SL(2,ℤ) where
  carrier := {γ | (γ 0 1 : ZMod p)=0}
  one_mem' := by simp
  mul_mem' {γ} {δ} hγ hδ := by
    change (γ 0 1:ZMod p)=0 at hγ
    change (δ 0 1:ZMod p)=0 at hδ
    change (((γ*δ:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p)=0
    simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,hγ,hδ]
  inv_mem' {γ} hγ := by
    change (γ 0 1:ZMod p)=0 at hγ
    change (γ⁻¹ 0 1:ZMod p)=0
    simpa [Matrix.SpecialLinearGroup.SL2_inv_expl] using hγ
def lpsHeckeConjugateIntersection (N p : ℕ) : Subgroup SL(2,ℤ) :=
  CongruenceSubgroup.Gamma0 N ⊓ lpsUpperCongruence p
end
end QEC.Coding.TannerLiftedProduct


