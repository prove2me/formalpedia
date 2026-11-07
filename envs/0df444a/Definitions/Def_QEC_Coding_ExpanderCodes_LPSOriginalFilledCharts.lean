-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCharts
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalFilledCharts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:55:48.91647+00:00
-- url     : https://prove2.me/theorems/332e384c-63f6-41de-8944-d8aec9ac8cf4
-- title:
--   LPSOriginal Filled Charts
-- statement:
--   Definitions and structural lemmas for LPSOriginal Filled Charts, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFilledCharts.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0Quotient
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspRepresentative_orbit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_range
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_cusp_mem
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_open
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_openEmbedding
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_param_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_param_openEmbedding
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
def lpsOriginalFilledCuspChart (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    OpenPartialHomeomorph (LPSOriginalFilledCurve N) ℂ := by
  let := lpsOriginalFilledTopology N
  let r := lpsOriginalCuspRepresentative N c
  let D := (lpsOriginalFilledCuspPartialEquiv N r).target
  let : Nonempty D := ⟨⟨0,lpsOriginalFilledCuspPartialEquiv_target_zero N r⟩⟩
  let e := (lpsOriginalFilledTopology_param_openEmbedding N c).toOpenPartialHomeomorph
    (lpsOriginalFilledCuspParam N c)
  refine { toPartialEquiv := lpsOriginalFilledCuspPartialEquiv N r
           open_source := by
             rw [←lpsOriginalFilledCuspParam_range N c]
             exact (lpsOriginalFilledTopology_param_openEmbedding N c).isOpen_range
           open_target := lpsOriginalFilledCuspPartialEquiv_target_open N r
           continuousOn_toFun := ?_
           continuousOn_invFun := ?_ }
  · have hc : ContinuousOn (fun x => (e.symm x).val) (Set.range (lpsOriginalFilledCuspParam N c)) :=
      continuous_subtype_val.comp_continuousOn (by
        change ContinuousOn e.invFun (Set.range (lpsOriginalFilledCuspParam N c))
        have ht : e.target=Set.range (lpsOriginalFilledCuspParam N c) := by
          simp only [e,IsOpenEmbedding.toOpenPartialHomeomorph_target]
        rw [←ht]
        exact e.continuousOn_invFun)
    rw [lpsOriginalFilledCuspParam_range] at hc
    apply hc.congr
    intro x hx
    have hxr : x∈Set.range (lpsOriginalFilledCuspParam N c) := by
      rw [lpsOriginalFilledCuspParam_range];exact hx
    have hp := (lpsOriginalFilledTopology_param_openEmbedding N c).toOpenPartialHomeomorph_right_inv
      (lpsOriginalFilledCuspParam N c) hxr
    have hq := (lpsOriginalFilledCuspPartialEquiv N r).right_inv (e.symm x).property
    change lpsOriginalFilledCuspPartialEquiv N r
      (lpsOriginalFilledCuspParam N c (e.symm x))=(e.symm x).val at hq
    rw [hp] at hq
    exact hq
  · exact continuousOn_iff_continuous_domRestrict.mpr
      (lpsOriginalFilledTopology_param_continuous N c)
lemma lpsOriginalFilledCuspChart_mem_cusp (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    Sum.inr c∈(lpsOriginalFilledCuspChart N c).source := by
  let := lpsOriginalFilledTopology N
  change Sum.inr c∈(lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).source
  simpa only [lpsOriginalCuspRepresentative_orbit] using
    lpsOriginalFilledCuspPartialEquiv_cusp_mem N (lpsOriginalCuspRepresentative N c)
def lpsOriginalFilledInteriorChart (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    letI := lpsOriginalFilledTopology N
    OpenPartialHomeomorph (LPSOriginalFilledCurve N) ℂ := by
  let := lpsOriginalFilledTopology N
  let := lpsGamma0QuotientChartedSpace N hN
  exact (chartAt ℂ x).lift_openEmbedding (lpsOriginalFilledTopology_interior_openEmbedding N)
lemma lpsOriginalFilledInteriorChart_mem (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    letI := lpsOriginalFilledTopology N
    Sum.inl x∈(lpsOriginalFilledInteriorChart N hN x).source := by
  let := lpsOriginalFilledTopology N
  let := lpsGamma0QuotientChartedSpace N hN
  exact ⟨x,ChartedSpace.mem_chart_source x,rfl⟩
@[instance_reducible]
def lpsOriginalFilledChartedSpace (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsOriginalFilledTopology N
    ChartedSpace ℂ (LPSOriginalFilledCurve N) := by
  let := lpsOriginalFilledTopology N
  refine { atlas := Set.range (lpsOriginalFilledInteriorChart N hN) ∪
                Set.range (lpsOriginalFilledCuspChart N)
           chartAt := Sum.elim (lpsOriginalFilledInteriorChart N hN)
                (lpsOriginalFilledCuspChart N)
           mem_chart_source := ?_
           chart_mem_atlas := ?_ }
  · intro x
    cases x with
    | inl y => exact lpsOriginalFilledInteriorChart_mem N hN y
    | inr c => exact lpsOriginalFilledCuspChart_mem_cusp N c
  · intro x
    cases x with
    | inl y => exact Or.inl ⟨y,rfl⟩
    | inr c => exact Or.inr ⟨c,rfl⟩
end
end QEC.Coding.TannerLiftedProduct


