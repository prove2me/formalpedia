-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:57:47.13506+00:00
-- url     : https://prove2.me/theorems/b3c0c2d9-df0e-4d0b-a457-303b4fae50bd
-- title:
--   LPSOriginal Compact Meromorphic Differential Comparison
-- statement:
--   Definitions and structural lemmas for LPSOriginal Compact Meromorphic Differential Comparison, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCompactMeromorphicDifferentialComparison.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.LinearAlgebra.Isomorphisms
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspChart_cusp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_symm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledInteriorChart_target_pos
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_chart_meromorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_cusp_order
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_projection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJMeromorphicDerivative_ne_zero
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
open scoped UpperHalfPlane Manifold ContDiff
noncomputable section
abbrev LPSOriginalFilledCovectorRepresentatives
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :=
  letI := lpsOriginalFilledTopology N
  letI := lpsOriginalFilledChartedSpace N hN
  letI := lpsOriginalFilled_isManifold N hN
  (x : LPSOriginalFilledCurve N) → TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ
def lpsOriginalFilledCovectorChartCoefficient
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (x : LPSOriginalFilledCurve N) : ℂ → ℂ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact fun z => ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
    (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ)
    x ((chartAt ℂ x).symm z) x ((chartAt ℂ x).symm z)
    (sectionForm ((chartAt ℂ x).symm z)) (1 : ℂ)
def lpsOriginalFilledCovectorChartMeromorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalFilledCovectorRepresentatives N hN) : Prop :=
  letI := lpsOriginalFilledTopology N
  letI := lpsOriginalFilledChartedSpace N hN
  ∀ x : LPSOriginalFilledCurve N,
    MeromorphicOn (lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x)
      (chartAt ℂ x).target
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledCovectorChart_evaluate
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (x y : LPSOriginalFilledCurve N) (v : ℂ)
    (hy : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      y ∈ (chartAt ℂ x).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    sectionForm y v = lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x
      (chartAt ℂ x y) • (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y v : ℂ) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let P : ℂ →L[ℂ] ℂ := ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ
    (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x y x y (sectionForm y)
  let e := trivializationAt ℂ (TangentSpace (M := LPSOriginalFilledCurve N) 𝓘(ℂ)) x
  have he : e.continuousLinearMapAt ℂ y = mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y := by
    rw [mfderiv_chartAt_eq_tangentCoordChange hy]
    exact TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hy
  have hv : P (e.continuousLinearMapAt ℂ y v) = sectionForm y v := by
    dsimp only [P]
    have ht : (trivializationAt ℂ (Bundle.Trivial (LPSOriginalFilledCurve N) ℂ) x).continuousLinearMapAt ℂ y = ContinuousLinearMap.id ℂ ℂ :=
      Bundle.Trivial.continuousLinearMapAt_trivialization ℂ _ ℂ y
    rw [ContinuousLinearMap.inCoordinates, ht, ContinuousLinearMap.id_comp]
    change sectionForm y (e.symmL ℂ y (e.continuousLinearMapAt ℂ y v)) = _
    rw [e.symmL_continuousLinearMapAt hy]
  have hscalar : P (e.continuousLinearMapAt ℂ y v) =
      P (1 : ℂ) • (e.continuousLinearMapAt ℂ y v : ℂ) := by
    let z : ℂ := e.continuousLinearMapAt ℂ y v
    have hz := P.map_smul z (1 : ℂ)
    change P (z * 1) = z * P (1 : ℂ) at hz
    rw [mul_one, mul_comm] at hz
    exact hz
  rw [← hv, hscalar, he]
  congr 1
  unfold lpsOriginalFilledCovectorChartCoefficient
  rw [(chartAt ℂ x).left_inv hy]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalFilledCovectorChartCoefficientLinearMap
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (x : LPSOriginalFilledCurve N) :
    LPSOriginalFilledCovectorRepresentatives N hN →ₗ[ℂ] (ℂ → ℂ) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact
    { toFun := fun sectionForm => lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x
      map_add' := by
        intro sectionForm otherForm
        funext z
        simp [lpsOriginalFilledCovectorChartCoefficient, ContinuousLinearMap.inCoordinates,
          ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
      map_smul' := by
        intro c sectionForm
        funext z
        simp [lpsOriginalFilledCovectorChartCoefficient, ContinuousLinearMap.inCoordinates,
          ContinuousLinearMap.smul_comp] }
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalFilledMeromorphicCovectorSubmodule
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    Submodule ℂ (LPSOriginalFilledCovectorRepresentatives N hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact
    { carrier := {sectionForm | lpsOriginalFilledCovectorChartMeromorphic N hN sectionForm}
      zero_mem' := by
        intro x
        change MeromorphicOn (lpsOriginalFilledCovectorChartCoefficientLinearMap N hN x 0)
          (chartAt ℂ x).target
        rw [map_zero]
        exact MeromorphicOn.const 0
      add_mem' := by
        intro sectionForm otherForm hsection hother x
        change MeromorphicOn
          (lpsOriginalFilledCovectorChartCoefficientLinearMap N hN x (sectionForm+otherForm))
            (chartAt ℂ x).target
        rw [map_add]
        exact (hsection x).add (hother x)
      smul_mem' := by
        intro c sectionForm hsection x
        change MeromorphicOn
          (lpsOriginalFilledCovectorChartCoefficientLinearMap N hN x (c • sectionForm))
            (chartAt ℂ x).target
        rw [map_smul]
        change MeromorphicOn (fun z => c *
          lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x z) (chartAt ℂ x).target
        exact (MeromorphicOn.const c).mul (hsection x) }
abbrev LPSOriginalFilledMeromorphicCovectorRepresentatives
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :=
  ↥(lpsOriginalFilledMeromorphicCovectorSubmodule N hN)
def lpsOriginalFilledFunctionCovector
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ) :
    LPSOriginalFilledCovectorRepresentatives N hN := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact fun y => mfderiv 𝓘(ℂ) 𝓘(ℂ) F y
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual derivative coefficient is the ordinary complex chart derivative, even at nondifferentiable points. -/
lemma lpsOriginalFilledFunctionCovector_chart
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ) (x : LPSOriginalFilledCurve N)
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z ∈ (chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    lpsOriginalFilledCovectorChartCoefficient N hN
      (lpsOriginalFilledFunctionCovector N hN F) x z =
        deriv (F ∘ (chartAt ℂ x).symm) z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := chartAt ℂ x
  let y := e.symm z
  have hy : y ∈ e.source := e.map_target hz
  have he : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := mdifferentiable_chart x
  have hinv := he.mdifferentiableAt_symm hz
  have hchart := he.mdifferentiableAt hy
  let chartDerivative : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) e y
  let inverseDerivative : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) e.symm z
  let functionDerivative : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) F y
  have hcoord : chartDerivative (inverseDerivative (1 : ℂ)) = 1 := by
    exact congrArg (fun L => (L (1 : ℂ) : ℂ)) (he.comp_symm_deriv hz)
  have hvalue := lpsOriginalFilledCovectorChart_evaluate N hN
    (lpsOriginalFilledFunctionCovector N hN F) x y (inverseDerivative (1 : ℂ)) hy
  change functionDerivative (inverseDerivative (1 : ℂ)) =
      lpsOriginalFilledCovectorChartCoefficient N hN
        (lpsOriginalFilledFunctionCovector N hN F) x (e y) *
          chartDerivative (inverseDerivative (1 : ℂ)) at hvalue
  rw [e.right_inv hz,hcoord,mul_one] at hvalue
  by_cases hF : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F y
  · have hmaps : (mfderiv 𝓘(ℂ) 𝓘(ℂ) (F ∘ e.symm) z : ℂ →L[ℂ] ℂ) =
        functionDerivative.comp inverseDerivative := mfderiv_comp z hF hinv
    rw [mfderiv_eq_fderiv] at hmaps
    have hchain := congrArg (fun L : ℂ →L[ℂ] ℂ => L (1 : ℂ)) hmaps
    change deriv (F ∘ e.symm) z = functionDerivative (inverseDerivative (1 : ℂ)) at hchain
    exact hvalue.symm.trans hchain.symm
  · have hnot : ¬ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (F ∘ e.symm) z := by
      intro hcomp
      have hh : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (F ∘ e.symm) (e y) := by
        rw [e.right_inv hz]
        exact hcomp
      have hm := hh.comp y hchart
      have heq : (F ∘ e.symm ∘ e) =ᶠ[𝓝 y] F := by
        filter_upwards [e.open_source.mem_nhds hy] with w hw
        simp only [Function.comp_apply,e.left_inv hw]
      exact hF (hm.congr_of_eventuallyEq heq.symm)
    change mfderiv 𝓘(ℂ) 𝓘(ℂ) F y (inverseDerivative (1 : ℂ)) = _ at hvalue
    rw [mfderiv_zero_of_not_mdifferentiableAt hF] at hvalue
    change (0 : ℂ) = _ at hvalue
    rw [← hvalue,deriv_zero_of_not_differentiableAt
      (mt mdifferentiableAt_iff_differentiableAt.mpr hnot)]
lemma lpsOriginalFilledFunctionCovector_meromorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalFilledCovectorChartMeromorphic N hN
      (lpsOriginalFilledFunctionCovector N hN F) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro x z hz
  have hm : MeromorphicOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target := hF x
  apply (hm.deriv z hz).congr
  filter_upwards [nhdsWithin_le_nhds ((chartAt ℂ x).open_target.mem_nhds hz)] with w hw
  exact (lpsOriginalFilledFunctionCovector_chart N hN F x w hw).symm
def lpsOriginalFilledCovectorRatio
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm otherForm : LPSOriginalFilledCovectorRepresentatives N hN) :
    LPSOriginalFilledCurve N → ℂ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  exact fun y => sectionForm y (1 : ℂ) / otherForm y (1 : ℂ)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual nonzero chart derivative cancels, making the covector ratio independent of the preferred frame. -/
lemma lpsOriginalFilledCovectorRatio_chart
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm otherForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z ∈ (chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    (lpsOriginalFilledCovectorRatio N hN sectionForm otherForm ∘ (chartAt ℂ x).symm) z =
      lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x z /
        lpsOriginalFilledCovectorChartCoefficient N hN otherForm x z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := chartAt ℂ x
  let y := e.symm z
  have hy : y ∈ e.source := e.map_target hz
  have he : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := mdifferentiable_chart x
  let chartDerivative : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) e y
  have hframe : chartDerivative (1 : ℂ) ≠ 0 := by
    intro hzero
    have hmap : mfderiv 𝓘(ℂ) 𝓘(ℂ) e y (1 : ℂ) =
        mfderiv 𝓘(ℂ) 𝓘(ℂ) e y (0 : ℂ) := by
      change chartDerivative (1 : ℂ) = chartDerivative (0 : ℂ)
      rw [map_zero]
      exact hzero
    have h10 : (1 : ℂ) = (0 : ℂ) := (he.mfderiv_injective hy) hmap
    exact one_ne_zero h10
  have hsection := lpsOriginalFilledCovectorChart_evaluate N hN sectionForm x y (1 : ℂ) hy
  have hother := lpsOriginalFilledCovectorChart_evaluate N hN otherForm x y (1 : ℂ) hy
  change sectionForm y (1 : ℂ) =
    lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x (e y) * chartDerivative 1
    at hsection
  change otherForm y (1 : ℂ) =
    lpsOriginalFilledCovectorChartCoefficient N hN otherForm x (e y) * chartDerivative 1
    at hother
  rw [e.right_inv hz] at hsection hother
  change sectionForm y (1 : ℂ) / otherForm y (1 : ℂ) = _
  rw [hsection,hother,mul_div_mul_right _ _ hframe]
lemma lpsOriginalFilledCovectorRatio_meromorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm otherForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (hsection : lpsOriginalFilledCovectorChartMeromorphic N hN sectionForm)
    (hother : lpsOriginalFilledCovectorChartMeromorphic N hN otherForm) :
    lpsOriginalFilledChartMeromorphic N hN
      (lpsOriginalFilledCovectorRatio N hN sectionForm otherForm) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro x z hz
  apply ((hsection x z hz).div (hother x z hz)).congr
  filter_upwards [nhdsWithin_le_nhds ((chartAt ℂ x).open_target.mem_nhds hz)] with w hw
  exact (lpsOriginalFilledCovectorRatio_chart N hN sectionForm otherForm x w hw).symm
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold
noncomputable section
lemma lpsOriginalJComplexDerivative_order_ne_top
    (z : ℂ) (hz : 0 < z.im) :
    meromorphicOrderAt (deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex)) z ≠ ⊤ := by
  let f : ℂ → ℂ := lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex
  have hm : MeromorphicOn (deriv f) UpperHalfPlane.upperHalfPlaneSet :=
    (lpsOriginalHolomorphic_ofComplex_meromorphic lpsOriginalJHolomorphic).deriv
  have hex : ∃ w ∈ UpperHalfPlane.upperHalfPlaneSet,
      meromorphicOrderAt (deriv f) w ≠ ⊤ := by
    by_contra! hall
    apply lpsOriginalJMeromorphicDerivative_ne_zero
    apply Subtype.ext
    rw [lpsOriginalMeromorphicGermCoefficientDerivative_value _ _ f
      (lpsOriginalHolomorphic_ofComplex_meromorphic lpsOriginalJHolomorphic) rfl]
    exact lpsOriginalMeromorphicGerm_zero_of_orders_top UpperHalfPlane.upperHalfPlaneSet
      (deriv f) hall
  exact ((hm.exists_meromorphicOrderAt_ne_top_iff_forall_mem
    (Complex.isConnected_of_upperHalfPlane Set.Subset.rfl
      (by intro w hw; exact (show 0 < w.im from hw).le))).mp hex) z hz
lemma lpsOriginalFilledJDerivativeChart_order_ne_top
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    meromorphicOrderAt (deriv (lpsOriginalFilledJ N ∘ (chartAt ℂ x).symm))
      (chartAt ℂ x x) ≠ ⊤ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  cases x with
  | inl y =>
      let e := lpsOriginalFilledInteriorChart N hN y
      have he : lpsOriginalFilledJ N ∘ e.symm =
          lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex := by
        funext w
        rw [Function.comp_apply,lpsOriginalFilledInteriorChart_symm,
          lpsOriginalFilledJ_projection]
        rfl
      change meromorphicOrderAt (deriv (lpsOriginalFilledJ N ∘ e.symm))
        (e (Sum.inl y)) ≠ ⊤
      rw [he]
      exact lpsOriginalJComplexDerivative_order_ne_top _
        (lpsOriginalFilledInteriorChart_target_pos N hN y _
          (e.map_source (lpsOriginalFilledInteriorChart_mem N hN y)))
  | inr c =>
      change meromorphicOrderAt (deriv (lpsOriginalFilledJ N ∘
        (lpsOriginalFilledCuspChart N c).symm))
          (lpsOriginalFilledCuspChart N c (Sum.inr c)) ≠ ⊤
      rw [lpsOriginalFilledCuspChart_cusp]
      let m := lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c)
      have hm : 0 < m := lpsOriginalCuspWidthNat_positive N _
      have hn : ((-(m : ℤ) : ℤ) : ℂ) ≠ 0 := by
        simp only [Int.cast_neg,Int.cast_natCast,neg_ne_zero]
        exact_mod_cast (Nat.ne_of_gt hm)
      have ho := meromorphicOrderAt_deriv_eq_sub_one hn (lpsOriginalFilledJ_cusp_order N c)
      change meromorphicOrderAt (deriv (fun q : ℂ => lpsOriginalFilledJ N
        ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q))) 0 ≠ ⊤
      rw [ho]
      exact WithTop.coe_ne_top
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledCovectorChart_unit_deriv_ne_zero
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (x y : LPSOriginalFilledCurve N)
    (hy : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      y ∈ (chartAt ℂ x).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y (1 : ℂ) : ℂ) ≠ 0 := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let D : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y
  intro hzero
  have hmap : mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y (1 : ℂ) =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) y (0 : ℂ) := by
    change D (1 : ℂ) = D (0 : ℂ)
    rw [map_zero]
    exact hzero
  have h10 : (1 : ℂ) = (0 : ℂ) := ((mdifferentiable_chart x).mfderiv_injective hy) hmap
  exact one_ne_zero h10
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledJCovector_eventually_ne_zero
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    letI := lpsOriginalFilledTopology N
    ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
      lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) ≠ 0 := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  change {y : LPSOriginalFilledCurve N |
    lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) ≠ 0} ∈
      Filter.codiscreteWithin (Set.univ : Set (LPSOriginalFilledCurve N))
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x hx
  simp only [Set.compl_univ,Set.union_empty]
  let e := chartAt ℂ x
  have hsrc : x ∈ e.source := mem_chart_source ℂ x
  have hm : MeromorphicAt (deriv (lpsOriginalFilledJ N ∘ e.symm)) (e x) :=
    (lpsOriginalFilledJ_chart_meromorphic N hN x (e x) (e.map_source hsrc)).deriv
  have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hm).mp
    (lpsOriginalFilledJDerivativeChart_order_ne_top N hN x)
  have ht : Tendsto e (𝓝[≠] x) (𝓝[≠] (e x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(e.continuousAt hsrc).tendsto.mono_left
      nhdsWithin_le_nhds,e.eventually_ne_nhdsWithin hsrc⟩
  filter_upwards [ht.eventually hn,nhdsWithin_le_nhds (e.open_source.mem_nhds hsrc)]
    with y hyn hy
  let D : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) e y
  have hv := lpsOriginalFilledCovectorChart_evaluate N hN
    (lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N)) x y (1 : ℂ) hy
  change lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) =
    lpsOriginalFilledCovectorChartCoefficient N hN
      (lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N)) x (e y) * D 1 at hv
  rw [lpsOriginalFilledFunctionCovector_chart N hN (lpsOriginalFilledJ N) x
    (e y) (e.map_source hy)] at hv
  rw [hv]
  exact mul_ne_zero hyn (lpsOriginalFilledCovectorChart_unit_deriv_ne_zero N hN x y hy)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The independent native zero relation: actual whole covectors vanish outside a codiscrete set. -/
def lpsOriginalFilledMeromorphicCovectorZeroSubmodule
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    Submodule ℂ (LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) := by
  let := lpsOriginalFilledTopology N
  exact
    { carrier := {sectionForm | ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
          sectionForm.val y = 0}
      zero_mem' := by
        change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
          (0 : LPSOriginalFilledMeromorphicCovectorRepresentatives N hN).val y = 0
        filter_upwards with y
        rfl
      add_mem' := by
        intro sectionForm otherForm hsection hother
        change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
          (sectionForm + otherForm).val y = 0
        change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N), sectionForm.val y = 0 at hsection
        change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N), otherForm.val y = 0 at hother
        filter_upwards [hsection,hother] with y hy hy'
        change sectionForm.val y + otherForm.val y = 0
        rw [hy,hy',add_zero]
      smul_mem' := by
        intro c sectionForm hsection
        change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
          (c • sectionForm).val y = 0
        change ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N), sectionForm.val y = 0 at hsection
        filter_upwards [hsection] with y hy
        change c • sectionForm.val y = 0
        rw [hy]
        apply ContinuousLinearMap.ext
        intro v
        change c * (0 : ℂ) = 0
        exact mul_zero c }
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- ALL actual meromorphic covector sections modulo genuine global codiscrete zero. -/
abbrev LPSOriginalCompactMeromorphicCovectorGerms
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :=
  by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  letI : AddCommGroup (LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :=
    (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
  exact LPSOriginalFilledMeromorphicCovectorRepresentatives N hN ⧸
    lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine inherited structure on the native original quotient. -/
instance lpsOriginalCompactMeromorphicCovectorAddCommGroup
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    AddCommGroup (LPSOriginalCompactMeromorphicCovectorGerms N hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  letI : AddCommGroup (LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :=
    (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
  exact Submodule.Quotient.addCommGroup (lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine inherited structure on the native original quotient. -/
instance lpsOriginalCompactMeromorphicCovectorModule
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    Module ℂ (LPSOriginalCompactMeromorphicCovectorGerms N hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  letI : AddCommGroup (LPSOriginalFilledMeromorphicCovectorRepresentatives N hN) :=
    (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
  exact Submodule.Quotient.module (lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN)
def lpsOriginalFilledFunctionTimesCovector
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (sectionForm : LPSOriginalFilledCovectorRepresentatives N hN) :
    LPSOriginalFilledCovectorRepresentatives N hN :=
  fun y => F y • sectionForm y
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledFunctionTimesCovector_chart
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (sectionForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (x : LPSOriginalFilledCurve N) (z : ℂ) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    lpsOriginalFilledCovectorChartCoefficient N hN
      (lpsOriginalFilledFunctionTimesCovector N hN F sectionForm) x z =
        F ((chartAt ℂ x).symm z) *
          lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  simp [lpsOriginalFilledCovectorChartCoefficient, lpsOriginalFilledFunctionTimesCovector,
    ContinuousLinearMap.inCoordinates, ContinuousLinearMap.smul_comp]
lemma lpsOriginalFilledFunctionTimesCovector_meromorphic
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (sectionForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hsection : lpsOriginalFilledCovectorChartMeromorphic N hN sectionForm) :
    lpsOriginalFilledCovectorChartMeromorphic N hN
      (lpsOriginalFilledFunctionTimesCovector N hN F sectionForm) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro x z hz
  have he : lpsOriginalFilledCovectorChartCoefficient N hN
      (lpsOriginalFilledFunctionTimesCovector N hN F sectionForm) x =
      fun z => F ((chartAt ℂ x).symm z) *
        lpsOriginalFilledCovectorChartCoefficient N hN sectionForm x z :=
    funext (lpsOriginalFilledFunctionTimesCovector_chart N hN F sectionForm x)
  rw [he]
  exact (hF x z hz).mul (hsection x z hz)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original differential compatibility used by the comparison or its semantic fixture. -/
lemma lpsOriginalFilledCovector_eq_zero_of_unit
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (y : LPSOriginalFilledCurve N) (hy : sectionForm y (1 : ℂ) = 0) :
    sectionForm y = 0 := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let A : ℂ →L[ℂ] ℂ := sectionForm y
  have hA : A = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := A.map_smul v (1 : ℂ)
    change A (v * 1) = v * A (1 : ℂ) at hv
    rw [mul_one,show A (1 : ℂ) = 0 from hy,mul_zero] at hv
    exact hv
  exact hA
def lpsOriginalFilledMeromorphicComplexConstants
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    ℂ →+* LPSOriginalFilledMeromorphicFunctionRing N hN where
  toFun c := ⟨fun _ => c,lpsOriginalFilledChartMeromorphic_const N hN c⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
section CompactRatioLinear
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
local notation "R" => LPSOriginalFilledMeromorphicFunctionRing N hN
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "V" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
local instance _p2m_local_instance_391f8f7aa3_629 : Algebra ℂ R := (lpsOriginalFilledMeromorphicComplexConstants N hN).toAlgebra
local instance _p2m_local_instance_391f8f7aa3_630 : Algebra ℂ L := ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict.comp
  (lpsOriginalFilledMeromorphicComplexConstants N hN)).toAlgebra
def lpsOriginalCompactMeromorphicGermAlgHom : R →ₐ[ℂ] L where
  toRingHom := (lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict
  commutes' _ := rfl
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalFilledCovectorRatioLinearMap
    (otherForm : LPSOriginalFilledCovectorRepresentatives N hN)
    (hother : lpsOriginalFilledCovectorChartMeromorphic N hN otherForm) : V →ₗ[ℂ] R where
  toFun sectionForm := ⟨lpsOriginalFilledCovectorRatio N hN sectionForm.val otherForm,
    lpsOriginalFilledCovectorRatio_meromorphic N hN sectionForm.val otherForm sectionForm.property hother⟩
  map_add' := by
    intro sectionForm anotherForm
    apply Subtype.ext
    funext y
    change (sectionForm.val y (1 : ℂ) + anotherForm.val y (1 : ℂ)) / otherForm y (1 : ℂ) =
      sectionForm.val y (1 : ℂ) / otherForm y (1 : ℂ) +
        anotherForm.val y (1 : ℂ) / otherForm y (1 : ℂ)
    exact add_div _ _ _
  map_smul' := by
    intro c sectionForm
    apply Subtype.ext
    funext y
    change (c * sectionForm.val y (1 : ℂ)) / otherForm y (1 : ℂ) =
      c * (sectionForm.val y (1 : ℂ) / otherForm y (1 : ℂ))
    exact mul_div_assoc _ _ _
def lpsOriginalCompactMeromorphicCovectorRatioMap : V →ₗ[ℂ] L :=
  (lpsOriginalCompactMeromorphicGermAlgHom N hN).toLinearMap.comp
    (lpsOriginalFilledCovectorRatioLinearMap N hN
      (lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N))
      (lpsOriginalFilledFunctionCovector_meromorphic N hN (lpsOriginalFilledJ N)
        (lpsOriginalFilledChartMeromorphic_j N hN)))
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ratio map kernel equals the independently defined whole-covector zero relation. -/
lemma lpsOriginalCompactMeromorphicCovectorRatioMap_ker :
    (lpsOriginalCompactMeromorphicCovectorRatioMap N hN).ker =
      lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  ext sectionForm
  rw [LinearMap.mem_ker]
  change lpsOriginalCompactMeromorphicCovectorRatioMap N hN sectionForm = 0 ↔
    ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N), sectionForm.val y = 0
  constructor
  · intro hz
    have hg := congrArg Subtype.val hz
    change ((lpsOriginalFilledCovectorRatio N hN sectionForm.val
      (lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N))) :
        Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) = 0 at hg
    have he := Filter.Germ.coe_eq.mp hg
    filter_upwards [he,lpsOriginalFilledJCovector_eventually_ne_zero N hN] with y hy hdy
    apply lpsOriginalFilledCovector_eq_zero_of_unit N hN sectionForm.val y
    change sectionForm.val y (1 : ℂ) /
      lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) = 0 at hy
    exact (div_eq_zero_iff).mp hy |>.resolve_right hdy
  · intro hz
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hz] with y hy
    change sectionForm.val y (1 : ℂ) /
      lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) = 0
    rw [hy]
    change (0 : ℂ) / _ = 0
    exact zero_div _
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual meromorphic function germ is the ratio of its actual representative times dj. -/
lemma lpsOriginalCompactMeromorphicCovectorRatioMap_surjective :
    Function.Surjective (lpsOriginalCompactMeromorphicCovectorRatioMap N hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro g
  obtain ⟨F,hF⟩ := g.property
  let dj := lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N)
  have hdj : lpsOriginalFilledCovectorChartMeromorphic N hN dj :=
    lpsOriginalFilledFunctionCovector_meromorphic N hN (lpsOriginalFilledJ N)
      (lpsOriginalFilledChartMeromorphic_j N hN)
  let sectionForm : V := ⟨lpsOriginalFilledFunctionTimesCovector N hN F.val dj,
    lpsOriginalFilledFunctionTimesCovector_meromorphic N hN F.val dj F.property hdj⟩
  refine ⟨sectionForm,Subtype.ext ?_⟩
  change (lpsOriginalFilledCovectorRatio N hN sectionForm.val dj :
    Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) = g.val
  rw [←hF]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [lpsOriginalFilledJCovector_eventually_ne_zero N hN] with y hy
  change (F.val y * dj y (1 : ℂ)) / dj y (1 : ℂ) = F.val y
  exact mul_div_cancel_right₀ (F.val y) hy
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- ALL native meromorphic covector germs are equivalent to the ENTIRE independently defined meromorphic field. -/
def lpsOriginalCompactMeromorphicCovectorLinearEquiv :
    LPSOriginalCompactMeromorphicCovectorGerms N hN ≃ₗ[ℂ] L := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  letI : AddCommGroup V := (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
  let f := lpsOriginalCompactMeromorphicCovectorRatioMap N hN
  let Z := lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN
  have hker : f.ker = Z := lpsOriginalCompactMeromorphicCovectorRatioMap_ker N hN
  exact (Submodule.quotEquivOfEq Z f.ker hker.symm).trans
    (f.quotKerEquivOfSurjective (lpsOriginalCompactMeromorphicCovectorRatioMap_surjective N hN))
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual original-curve map used by the differential comparison. -/
def lpsOriginalCompactMeromorphicCovectorClass :
    V →ₗ[ℂ] LPSOriginalCompactMeromorphicCovectorGerms N hN := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  letI : AddCommGroup V := (lpsOriginalFilledMeromorphicCovectorSubmodule N hN).addCommGroup
  exact (lpsOriginalFilledMeromorphicCovectorZeroSubmodule N hN).mkQ
def lpsOriginalFilledMeromorphicFunctionTimesCovector (F : R) (sectionForm : V) : V :=
  ⟨lpsOriginalFilledFunctionTimesCovector N hN F.val sectionForm.val,
    lpsOriginalFilledFunctionTimesCovector_meromorphic N hN F.val sectionForm.val
      F.property sectionForm.property⟩
open scoped ContDiff
end CompactRatioLinear
end
end QEC.Coding.TannerLiftedProduct


