-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:20:18.125862+00:00
-- url     : https://prove2.me/theorems/6ce93978-3665-4e15-b621-1f55804a587d
-- title:
--   LPSOriginal Cusp Widths
-- statement:
--   Definitions and structural lemmas for LPSOriginal Cusp Widths, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspWidths.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.Cusps
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section
def lpsOriginalCuspGroup (N : ℕ) (ρ : SL(2,ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ ρ)⁻¹ •
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
lemma lpsOriginalCuspGroup_le_SLRange (N : ℕ) (ρ : SL(2,ℤ)) :
    lpsOriginalCuspGroup N ρ ≤ (Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range := by
  intro g hg
  rw [lpsOriginalCuspGroup,ConjAct.toConjAct_inv,
    Subgroup.mem_inv_pointwise_smul_iff,ConjAct.toConjAct_smul] at hg
  rcases hg with ⟨γ,hγ,hγg⟩
  refine ⟨ρ⁻¹*γ*ρ,?_⟩
  simp only [map_mul,map_inv]
  rw [hγg]
  group
instance lpsOriginalCuspGroup_discrete (N : ℕ) (ρ : SL(2,ℤ)) :
    DiscreteTopology (lpsOriginalCuspGroup N ρ) :=
  (Matrix.SpecialLinearGroup.discreteSpecialLinearGroupIntRange (n:=Fin 2)).of_subset
    (lpsOriginalCuspGroup_le_SLRange N ρ)
instance lpsOriginalCuspGroup_detOne (N : ℕ) (ρ : SL(2,ℤ)) :
    (lpsOriginalCuspGroup N ρ).HasDetOne := by
  unfold lpsOriginalCuspGroup
  infer_instance
end
end QEC.Coding.TannerLiftedProduct


