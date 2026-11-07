-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalCuspOrbits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:35:39.469613+00:00
-- url     : https://prove2.me/theorems/e9dba835-a4af-4335-a701-341aa4e44b99
-- title:
--   LPSOriginal Cusp Orbits
-- statement:
--   Definitions and structural lemmas for LPSOriginal Cusp Orbits, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspOrbits.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNeighborhoods
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
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
def lpsOriginalCuspOrbit (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
  cosetToCuspOrbit (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ⟦ρ⁻¹⟧
lemma lpsOriginalCuspOrbit_surjective (N : ℕ) [NeZero N] :
    Function.Surjective (lpsOriginalCuspOrbit N) := by
  intro c
  obtain ⟨x,hx⟩ := surjective_cosetToCuspOrbit
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) c
  obtain ⟨γ,rfl⟩ := Quotient.exists_rep x
  refine ⟨γ⁻¹,?_⟩
  simpa [lpsOriginalCuspOrbit] using hx
def lpsOriginalCuspRepresentative (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) : SL(2,ℤ) :=
  Classical.choose (lpsOriginalCuspOrbit_surjective N c)
end
end QEC.Coding.TannerLiftedProduct


