-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
-- name    : QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:48:12.224364+00:00
-- url     : https://prove2.me/theorems/6ff1a158-a0ee-4178-8a43-bfc677843c89
-- title:
--   LPSQuadratic Eisenstein Series
-- statement:
--   Definitions and structural lemmas for LPSQuadratic Eisenstein Series, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuadraticEisensteinSeries.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
noncomputable def lpsQuadraticE2Character (q : ℕ) [Fact q.Prime] : MulChar (ZMod q) ℂ :=
  (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ)
noncomputable def lpsQuadraticE2Twist (q : ℕ) [Fact q.Prime] (z : ℍ) : ℂ :=
  (gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
    ∑ a : Fin q, lpsQuadraticE2Character q (a.val:ZMod q) *
      EisensteinSeries.E2 (((a.val:ℝ)/(q:ℝ)) +ᵥ z)
noncomputable def lpsE2RealTranslation (r : ℝ) : SL(2,ℝ) :=
  ⟨!![1,r;0,1],by simp [Matrix.det_fin_two,Matrix.of_apply]⟩
end QEC.Coding.TannerLiftedProduct


