-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
-- name    : QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:16:12.48201+00:00
-- url     : https://prove2.me/theorems/db12ef22-65b0-48c7-8733-889b08f8b3d0
-- title:
--   LPSHecke Coefficients
-- statement:
--   Definitions and structural lemmas for LPSHecke Coefficients, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckeCoefficients.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_det
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
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
lemma lpsHeckeUpperGL_infty (p : ℕ) [Fact p.Prime] :
    lpsHeckeUpperGL ℝ p none=lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 := by
  apply Units.ext
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [lpsHeckeUpperGL,lpsHeckeUpperMatrix,lpsE2AffineMatrix,Matrix.map_apply,Matrix.of_apply]
lemma lpsHeckeUpperGL_finite_slash (p : ℕ) [Fact p.Prime] (j : Fin p) (f : ℍ→ℂ) :
    (f ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p (some j))=
      (fun z : ℍ => (p:ℂ)⁻¹*f (lpsHeckeUpperGL ℝ p (some j) • z)) := by
  have hp : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpC : (p:ℂ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  funext z
  simp only [ModularForm.slash_apply,UpperHalfPlane.σ,lpsHeckeUpperGL_det,if_pos hp,abs_of_pos hp]
  simp [UpperHalfPlane.denom,lpsHeckeUpperGL,lpsHeckeUpperMatrix,Matrix.map_apply,Matrix.of_apply]
  field_simp
lemma lpsCuspHecke_apply (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    lpsCuspHecke N p hNp f z =
      (p:ℂ)*f (lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 • z)+
        (p:ℂ)⁻¹*∑ j : Fin p,f (lpsHeckeUpperGL ℝ p (some j) • z) := by
  classical
  change lpsHeckeSlashSum p (f:ℍ→ℂ) z=_
  unfold lpsHeckeSlashSum
  rw [Finset.sum_apply]
  rw [Fintype.sum_option,lpsHeckeUpperGL_infty,lpsFunction_affine_slash]
  simp_rw [lpsHeckeUpperGL_finite_slash]
  simp only [←Finset.mul_sum]
lemma lpsCuspHecke_add (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspHecke N p hNp (f+g)=lpsCuspHecke N p hNp f+lpsCuspHecke N p hNp g := by
  classical
  ext z
  simp only [lpsCuspHecke_apply,FunLike.coe_add,Pi.add_apply,Finset.sum_add_distrib]
  ring
lemma lpsCuspHecke_smul (N p : ℕ) [NeZero N] [Fact p.Prime] (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (c : ℂ) :
    lpsCuspHecke N p hNp (c • f)=c • lpsCuspHecke N p hNp f := by
  classical
  ext z
  simp only [lpsCuspHecke_apply,FunLike.coe_smul,Pi.smul_apply,smul_eq_mul,←Finset.mul_sum]
  ring
noncomputable def lpsCuspHeckeLinearMap (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) :
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 →ₗ[ℂ]
      CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2 where
  toFun := lpsCuspHecke N p hNp
  map_add' := lpsCuspHecke_add N p hNp
  map_smul' c f := lpsCuspHecke_smul N p hNp f c
noncomputable def lpsHeckePrimePowerLinearMap (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) : ℕ →
    Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
  | 0 => LinearMap.id
  | 1 => lpsCuspHeckeLinearMap N p hNp
  | r+2 => (lpsHeckePrimePowerLinearMap N p hNp (r+1)).comp
      (lpsCuspHeckeLinearMap N p hNp)-(p:ℂ) • lpsHeckePrimePowerLinearMap N p hNp r
end QEC.Coding.TannerLiftedProduct


