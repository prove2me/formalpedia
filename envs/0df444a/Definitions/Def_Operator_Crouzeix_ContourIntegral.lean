-- Prove2me | Definitions.Def_Operator_Crouzeix_ContourIntegral
-- name    : Operator_Crouzeix_ContourIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:29:19.787546+00:00
-- url     : https://prove2.me/theorems/c9c31bb9-46d0-4a88-8f70-fdd0805c65f9
-- title:
--   Contour Integral
-- statement:
--   Definitions and structural lemmas for Contour Integral, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean

import Mathlib.MeasureTheory.Integral.CircleIntegral
set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
def ContourIntegrable (f : ℂ → F) (γ : ℝ → ℂ) : Prop :=
  IntervalIntegrable (fun t => deriv γ t • f (γ t)) volume 0 (2 * π)
noncomputable def contourIntegral (f : ℂ → F) (γ : ℝ → ℂ) : F :=
  ∫ t in (0 : ℝ)..(2 * π), deriv γ t • f (γ t)
section Linearity
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
end Linearity


