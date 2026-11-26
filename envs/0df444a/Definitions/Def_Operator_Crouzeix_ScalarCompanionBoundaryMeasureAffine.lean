-- Prove2me | Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
-- name    : Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:45:27.287233+00:00
-- url     : https://prove2.me/theorems/124413e1-e9e5-5dd1-894d-eb5766c022cf
-- title:
--   Scalar Companion Boundary Measure Affine
-- statement:
--   Definitions and structural lemmas for Scalar Companion Boundary Measure Affine, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundaryMeasureAffine.lean

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange


set_option autoImplicit false
open Complex MeasureTheory Set
open scoped Interval Real
noncomputable def SmoothJordanDomain.complexAffine
    (Omega : SmoothJordanDomain) (a b : ℂ) (ha : a ≠ 0) :
    SmoothJordanDomain := by
  let e : ℂ ≃ₜ ℂ :=
    (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)
  refine
    { carrier := (fun z => a * z + b) '' Omega.carrier
      isOpen_carrier := ?_
      strictConvex_carrier := ?_
      boundaryParam := fun t => a * Omega.boundaryParam t + b
      boundaryParam_periodic := ?_
      boundaryParam_contDiff := ?_
      boundaryParam_range := ?_
      boundaryParam_injOn := ?_
      boundaryParam_regular := ?_ }
  · change IsOpen (e '' Omega.carrier)
    exact e.isOpenMap Omega.carrier Omega.isOpen_carrier
  · rintro x' ⟨x, hx, hx'⟩ y' ⟨y, hy, hy'⟩ hxy α β hα hβ hsum
    subst x'
    subst y'
    have hxy0 : x ≠ y := by
      intro h
      apply hxy
      rw [h]
    have hcombo :=
      Omega.strictConvex_carrier hx hy hxy0 hα hβ hsum
    change α • e x + β • e y ∈ interior (e '' Omega.carrier)
    rw [← e.image_interior]
    refine ⟨α • x + β • y, hcombo, ?_⟩
    dsimp only [e, Homeomorph.trans_apply]
    change a * (α • x + β • y) + b =
      α • (a * x + b) + β • (a * y + b)
    rw [Complex.real_smul, Complex.real_smul, Complex.real_smul,
      Complex.real_smul]
    have hsumC : (α : ℂ) + (β : ℂ) = 1 := by
      exact_mod_cast hsum
    calc
      a * ((α : ℂ) * x + (β : ℂ) * y) + b =
          a * ((α : ℂ) * x + (β : ℂ) * y) +
            ((α : ℂ) + (β : ℂ)) * b := by rw [hsumC, one_mul]
      _ = (α : ℂ) * (a * x + b) +
          (β : ℂ) * (a * y + b) := by ring
  · intro t
    exact congrArg (fun z => a * z + b)
      (Omega.boundaryParam_periodic t)
  · exact (contDiff_const.mul Omega.boundaryParam_contDiff).add contDiff_const
  · change Set.range (fun t => e (Omega.boundaryParam t)) =
      frontier (e '' Omega.carrier)
    rw [show (fun t => e (Omega.boundaryParam t)) =
        e ∘ Omega.boundaryParam by rfl,
      Set.range_comp, Omega.boundaryParam_range, e.image_frontier]
  · intro x hx y hy hxy
    apply Omega.boundaryParam_injOn hx hy
    apply e.injective
    exact hxy
  · intro t
    have hgamma : HasDerivAt Omega.boundaryParam
        (deriv Omega.boundaryParam t) t :=
      (Omega.boundaryParam_contDiff.differentiable (by norm_num) t).hasDerivAt
    have hderiv : deriv (fun s : ℝ => a * Omega.boundaryParam s + b) t =
        a * deriv Omega.boundaryParam t := by
      have hmul := (hasDerivAt_const t a).mul hgamma
      have hadd := hmul.add (hasDerivAt_const t b)
      rw [show (fun s : ℝ => a * Omega.boundaryParam s + b) =
          (fun _ : ℝ => a) * Omega.boundaryParam +
            (fun _ : ℝ => b) by
        funext s
        rfl]
      simpa only [zero_mul, zero_add, add_zero] using hadd.deriv
    rw [hderiv]
    exact mul_ne_zero ha (Omega.boundaryParam_regular t)


