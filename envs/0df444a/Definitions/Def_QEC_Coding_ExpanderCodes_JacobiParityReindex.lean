-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
-- name    : QEC_Coding_ExpanderCodes_JacobiParityReindex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:08:54.439603+00:00
-- url     : https://prove2.me/theorems/402f0be9-5566-4336-8b82-416bc40915f3
-- title:
--   Jacobi Parity Reindex
-- statement:
--   Definitions and structural lemmas for Jacobi Parity Reindex, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiParityReindex.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedSquareSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerTriangularRoots_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedSquareSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSixProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSquareProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiThetaProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiTriangularProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.integerTriangularRoots_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
def jacobiSameParityToFun
    (p : ℤ × ℤ) : {q : ℤ × ℤ // Even (q.1 + q.2)} :=
  ⟨(p.1 + p.2, p.1 - p.2), ⟨p.1, by ring⟩⟩
noncomputable def jacobiSameParityInvFun
    (p : {q : ℤ × ℤ // Even (q.1 + q.2)}) : ℤ × ℤ :=
  ((p.1.1 + p.1.2) / 2, (p.1.1 - p.1.2) / 2)
theorem jacobiSameParity_left_inv :
    Function.LeftInverse jacobiSameParityInvFun jacobiSameParityToFun := by
  intro p
  change (((p.1 + p.2) + (p.1 - p.2)) / 2,
    ((p.1 + p.2) - (p.1 - p.2)) / 2) = p
  apply Prod.ext <;> dsimp only
  all_goals omega
theorem jacobiSameParity_right_inv :
    Function.RightInverse jacobiSameParityInvFun jacobiSameParityToFun := by
  intro p
  obtain ⟨s, hs⟩ := p.property
  apply Subtype.ext
  change ((p.1.1 + p.1.2) / 2 + (p.1.1 - p.1.2) / 2,
    (p.1.1 + p.1.2) / 2 - (p.1.1 - p.1.2) / 2) = p.1
  apply Prod.ext <;> dsimp only
  all_goals omega
noncomputable def jacobiSameParityEquiv :
    (ℤ × ℤ) ≃ {p : ℤ × ℤ // Even (p.1 + p.2)} where
  toFun := jacobiSameParityToFun
  invFun := jacobiSameParityInvFun
  left_inv := jacobiSameParity_left_inv
  right_inv := jacobiSameParity_right_inv
def jacobiOppositeParityToFun
    (p : ℤ × ℤ) : {q : ℤ × ℤ // ¬ Even (q.1 + q.2)} :=
  ⟨(p.1 + p.2, p.2 - p.1 - 1), by
    intro h
    obtain ⟨r, hr⟩ := h
    dsimp only at hr
    omega⟩
noncomputable def jacobiOppositeParityInvFun
    (p : {q : ℤ × ℤ // ¬ Even (q.1 + q.2)}) : ℤ × ℤ :=
  ((p.1.1 - p.1.2 - 1) / 2, (p.1.1 + p.1.2 + 1) / 2)
theorem jacobiOppositeParity_left_inv :
    Function.LeftInverse jacobiOppositeParityInvFun
      jacobiOppositeParityToFun := by
  intro p
  change (((p.1 + p.2) - (p.2 - p.1 - 1) - 1) / 2,
    ((p.1 + p.2) + (p.2 - p.1 - 1) + 1) / 2) = p
  apply Prod.ext <;> dsimp only
  all_goals omega
theorem jacobiOppositeParity_right_inv :
    Function.RightInverse jacobiOppositeParityInvFun
      jacobiOppositeParityToFun := by
  intro p
  obtain ⟨r, hr⟩ := Int.not_even_iff_odd.mp p.property
  apply Subtype.ext
  change ((p.1.1 - p.1.2 - 1) / 2 +
      (p.1.1 + p.1.2 + 1) / 2,
    (p.1.1 + p.1.2 + 1) / 2 -
      (p.1.1 - p.1.2 - 1) / 2 - 1) = p.1
  apply Prod.ext <;> dsimp only
  all_goals omega
noncomputable def jacobiOppositeParityEquiv :
    (ℤ × ℤ) ≃ {p : ℤ × ℤ // ¬ Even (p.1 + p.2)} where
  toFun := jacobiOppositeParityToFun
  invFun := jacobiOppositeParityInvFun
  left_inv := jacobiOppositeParity_left_inv
  right_inv := jacobiOppositeParity_right_inv
noncomputable def jacobiParityReindex :
    ((ℤ × ℤ) ⊕ (ℤ × ℤ)) ≃ (ℤ × ℤ) :=
  (Equiv.sumCongr jacobiSameParityEquiv jacobiOppositeParityEquiv).trans
    (Equiv.sumCompl fun p : ℤ × ℤ => Even (p.1 + p.2))
end QEC.Coding.TannerLiftedProduct


