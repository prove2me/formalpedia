-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
-- name    : Operator_Crouzeix_SmoothSupportDomain
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:41:39.642662+00:00
-- url     : https://prove2.me/theorems/7c59b57a-2efc-4f34-a9ec-d1420dc91f3c
-- title:
--   Smooth Support Domain
-- statement:
--   Definitions and structural lemmas for Smooth Support Domain, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportDomain.lean

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_deriv
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_outwardNormal
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_closure_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_frontier_carrier
import Theorems.Thm_contDiff_polytopeRoundedSupport
import Theorems.Thm_contDiff_polytopeRoundedSupportCurve
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_injOn_smoothSupportCurve_Ico
import Theorems.Thm_isOpen_smoothSupportOpenEnvelope
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_periodic_polytopeRoundedSupport
import Theorems.Thm_periodic_polytopeRoundedSupportCurve
import Theorems.Thm_polytopeRoundedSupportCurve_regular
import Theorems.Thm_polytopeRoundedSupport_add_deriv_deriv_pos
import Theorems.Thm_range_polytopeRoundedSupportCurve_eq_frontier
import Theorems.Thm_smoothSupportDirectionalLinearMap_apply
import Theorems.Thm_strictConvex_smoothSupportOpenEnvelope
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_deriv
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_outwardNormal
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_closure_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_frontier_carrier
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange
attribute [local simp] smoothSupportDirectionalLinearMap_apply


set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff InnerProductSpace
noncomputable def polytopeRoundedSupportDomainOfRange
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hrange : Set.range (polytopeRoundedSupportCurve u delta rho) =
      frontier (smoothSupportOpenEnvelope
        (polytopeRoundedSupport u delta rho))) :
    SmoothJordanDomain where
  carrier := smoothSupportOpenEnvelope
    (polytopeRoundedSupport u delta rho)
  isOpen_carrier := isOpen_smoothSupportOpenEnvelope _
  strictConvex_carrier := strictConvex_smoothSupportOpenEnvelope _
  boundaryParam := polytopeRoundedSupportCurve u delta rho
  boundaryParam_periodic :=
    periodic_polytopeRoundedSupportCurve u delta rho
  boundaryParam_contDiff :=
    contDiff_polytopeRoundedSupportCurve hu delta rho
  boundaryParam_range := hrange
  boundaryParam_injOn := by
    unfold polytopeRoundedSupportCurve
    simpa only [zero_add] using
      injOn_smoothSupportCurve_Ico
        (contDiff_polytopeRoundedSupport hu delta rho)
        (periodic_polytopeRoundedSupport u delta rho)
        (fun theta => by
          unfold smoothSupportCurvatureRadius
          exact polytopeRoundedSupport_add_deriv_deriv_pos
            hu hdelta hrho theta)
        0
  boundaryParam_regular :=
    polytopeRoundedSupportCurve_regular hu hdelta hrho
noncomputable def polytopeRoundedSupportDomain
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    SmoothJordanDomain :=
  polytopeRoundedSupportDomainOfRange hu hdelta hrho
    (range_polytopeRoundedSupportCurve_eq_frontier hu hdelta hrho)
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


