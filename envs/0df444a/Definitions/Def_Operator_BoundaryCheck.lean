-- Prove2me | Definitions.Def_Operator_BoundaryCheck
-- name    : Operator_BoundaryCheck
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:57:36.069868+00:00
-- url     : https://prove2.me/theorems/63273f8f-2251-51d5-a101-0a07b066ba5c
-- title:
--   Boundary Check
-- statement:
--   Definitions and structural lemmas for Boundary Check, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean

import Definitions.Def_Operator
set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
namespace CrouzeixPalenciaBoundary
universe u
section NumericalRange
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
noncomputable def numericalRange_boundary (A : E →L[ℂ] E) : Set ℂ :=
  numericalRange A
end NumericalRange
section SpectralSet
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
noncomputable def polynomialSupNorm_boundary
    (p : Polynomial ℂ) (X : Set ℂ) : ℝ :=
  polynomialSupNorm p X
def IsKPolynomialSpectralSet_boundary
    (A : E →L[ℂ] E) (K : ℝ) (X : Set ℂ) : Prop :=
  IsKPolynomialSpectralSet A K X
def IsPolynomialSpectralSet_boundary
    (A : E →L[ℂ] E) (X : Set ℂ) : Prop :=
  IsPolynomialSpectralSet A X
end SpectralSet
section Dilation
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
end Dilation
section Contours
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
def ContourIntegrable_boundary (f : ℂ → F) (γ : ℝ → ℂ) : Prop :=
  ContourIntegrable f γ
noncomputable def contourIntegral_boundary (f : ℂ → F) (γ : ℝ → ℂ) : F :=
  contourIntegral f γ
end Contours
section Approximation
noncomputable def smoothClosedBallApproximation_boundary
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    SmoothConvexApproximation (Metric.closedBall c R) :=
  smoothClosedBallApproximation c R hR
end Approximation
section Auxiliary
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
noncomputable def crouzeixAuxiliaryOperator_boundary
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (h : ℂ → ℂ) : E →L[ℂ] E :=
  crouzeixAuxiliaryOperator A Omega h
noncomputable def crouzeixPolynomialAuxiliaryOperator_boundary
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) : E →L[ℂ] E :=
  crouzeixPolynomialAuxiliaryOperator A Omega p
end Auxiliary
end CrouzeixPalenciaBoundary


