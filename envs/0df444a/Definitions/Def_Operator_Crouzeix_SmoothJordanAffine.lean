-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
-- name    : Operator_Crouzeix_SmoothJordanAffine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:18:31.210129+00:00
-- url     : https://prove2.me/theorems/62f4f4f1-1eb0-476c-a4e7-aae9d13b3444
-- title:
--   Smooth Jordan Affine
-- statement:
--   Definitions and structural lemmas for Smooth Jordan Affine, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanAffine.lean

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Convex.ContinuousLinearEquiv
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
namespace SmoothJordanDomain
theorem deriv_continuousLinearEquiv_comp (Omega : SmoothJordanDomain)
    (e : ℂ ≃L[ℝ] ℂ) (t : ℝ) :
    deriv (e ∘ Omega.boundaryParam) t = e (deriv Omega.boundaryParam t) := by
  have hdiff : DifferentiableAt ℝ Omega.boundaryParam t :=
    (Omega.boundaryParam_contDiff.differentiable (by norm_num)).differentiableAt
  exact (e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    t hdiff.hasDerivAt).deriv
noncomputable def linearImage (Omega : SmoothJordanDomain)
    (e : ℂ ≃L[ℝ] ℂ) : SmoothJordanDomain where
  carrier := e '' Omega.carrier
  isOpen_carrier := e.toHomeomorph.isOpen_image.mpr Omega.isOpen_carrier
  strictConvex_carrier := e.strictConvex_image.mpr Omega.strictConvex_carrier
  boundaryParam := e ∘ Omega.boundaryParam
  boundaryParam_periodic := Omega.boundaryParam_periodic.comp e
  boundaryParam_contDiff :=
    Omega.boundaryParam_contDiff.continuousLinearMap_comp e.toContinuousLinearMap
  boundaryParam_range := by
    rw [Set.range_comp, Omega.boundaryParam_range]
    exact e.toHomeomorph.image_frontier Omega.carrier
  boundaryParam_injOn := by
    intro x hx y hy hxy
    exact Omega.boundaryParam_injOn hx hy (e.injective hxy)
  boundaryParam_regular := by
    intro t hzero
    rw [deriv_continuousLinearEquiv_comp] at hzero
    exact Omega.boundaryParam_regular t (e.injective (by simpa using hzero))
@[simp] theorem linearImage_carrier (Omega : SmoothJordanDomain)
    (e : ℂ ≃L[ℝ] ℂ) :
    (Omega.linearImage e).carrier = e '' Omega.carrier := rfl
@[simp] theorem linearImage_boundaryParam (Omega : SmoothJordanDomain)
    (e : ℂ ≃L[ℝ] ℂ) :
    (Omega.linearImage e).boundaryParam = e ∘ Omega.boundaryParam := rfl
@[simp] theorem linearImage_boundaryParam_apply (Omega : SmoothJordanDomain)
    (e : ℂ ≃L[ℝ] ℂ) (t : ℝ) :
    (Omega.linearImage e).boundaryParam t = e (Omega.boundaryParam t) := rfl
@[simp] theorem linearImage_boundaryParam_deriv (Omega : SmoothJordanDomain)
    (e : ℂ ≃L[ℝ] ℂ) (t : ℝ) :
    deriv (Omega.linearImage e).boundaryParam t =
      e (deriv Omega.boundaryParam t) := by
  exact deriv_continuousLinearEquiv_comp Omega e t
theorem deriv_const_add_boundaryParam (Omega : SmoothJordanDomain)
    (c : ℂ) (t : ℝ) :
    deriv (fun u => c + Omega.boundaryParam u) t =
      deriv Omega.boundaryParam t := by
  have hdiff : DifferentiableAt ℝ Omega.boundaryParam t :=
    (Omega.boundaryParam_contDiff.differentiable (by norm_num)).differentiableAt
  exact (hdiff.hasDerivAt.const_add c).deriv
noncomputable def translate (Omega : SmoothJordanDomain)
    (c : ℂ) : SmoothJordanDomain where
  carrier := (fun z => c + z) '' Omega.carrier
  isOpen_carrier := (Homeomorph.addLeft c).isOpen_image.mpr Omega.isOpen_carrier
  strictConvex_carrier := Omega.strictConvex_carrier.add_left c
  boundaryParam := fun t => c + Omega.boundaryParam t
  boundaryParam_periodic := by
    simpa only [Function.comp_def] using
      Omega.boundaryParam_periodic.comp (fun z : ℂ => c + z)
  boundaryParam_contDiff := contDiff_const.add Omega.boundaryParam_contDiff
  boundaryParam_range := by
    rw [Set.range_comp' (fun z => c + z), Omega.boundaryParam_range]
    exact (Homeomorph.addLeft c).image_frontier Omega.carrier
  boundaryParam_injOn := by
    intro x hx y hy hxy
    exact Omega.boundaryParam_injOn hx hy (add_left_cancel hxy)
  boundaryParam_regular := by
    intro t
    rw [deriv_const_add_boundaryParam]
    exact Omega.boundaryParam_regular t
noncomputable def ellipse (c : ℂ) (e : ℂ ≃L[ℝ] ℂ)
    (R : ℝ) (hR : 0 < R) : SmoothJordanDomain :=
  ((SmoothJordanDomain.ball 0 R hR).linearImage e).translate c
end SmoothJordanDomain


