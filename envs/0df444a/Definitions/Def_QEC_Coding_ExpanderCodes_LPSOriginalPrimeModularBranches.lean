-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:14:47.792914+00:00
-- url     : https://prove2.me/theorems/56553ea3-8c22-4ec7-b2d7-02925deaa08f
-- title:
--   LPSOriginal Prime Modular Branches
-- statement:
--   Definitions and structural lemmas for LPSOriginal Prime Modular Branches, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeModularBranches.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
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
open scoped UpperHalfPlane MatrixGroups
noncomputable section
def lpsOriginalPrimeBranch (p : ℕ) [Fact p.Prime]
    (m : Option (Fin p)) (τ : ℍ) : ℂ :=
  lpsOriginalJInvariant (lpsHeckeUpperGL ℝ p m • τ)
def lpsOriginalPrimeBranchSL (p : ℕ) (i : Option (Fin p)) : SL(2,ℤ) :=
  match i with
  | none => 1
  | some m => ⟨!![0,-1;1,(m.val:ℤ)],by simp [Matrix.det_fin_two]⟩
def lpsOriginalPrimeBranchInverseRealSL (p : ℕ) (i : Option (Fin p)) : 𝒮ℒ :=
  ⟨Matrix.SpecialLinearGroup.mapGL ℝ (lpsOriginalPrimeBranchSL p i)⁻¹,⟨_,rfl⟩⟩
def lpsOriginalPrimeBranchHolomorphic (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) : LPSOriginalHolomorphicRing :=
  lpsOriginalHolomorphicPullback (lpsOriginalPrimeBranchInverseRealSL p i)
    (lpsOriginalJNHolomorphic p (Fact.out : p.Prime).pos)
def lpsOriginalPrimeFractionBranch (p : ℕ) [Fact p.Prime]
    (i : Option (Fin p)) : LPSOriginalHolomorphicFractionField :=
  algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
    (lpsOriginalPrimeBranchHolomorphic p i)
end
end QEC.Coding.TannerLiftedProduct


