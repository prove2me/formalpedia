-- Prove2me | Definitions.Def_Esgk_PlaneProjectiveHomogenization
-- name    : Esgk_PlaneProjectiveHomogenization
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:45:56.095117+00:00
-- url     : https://prove2.me/theorems/405e6b0d-c765-4ac6-bb5f-cea941338360
-- title:
--   Complex coefficient extension and homogenization
-- statement:
--   This defines real-to-complex coefficient extension, the inclusion of two-variable polynomials into three variables, and homogeneous layers multiplied by a power of the new variable, with truncated natural subtraction in the exponent. Summing layers only through the chosen degree gives the corresponding homogenization.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

 
abbrev ComplexPlanePoly := MvPolynomial (Fin 2) ℂ

 
abbrev ProjectivePlanePoly := MvPolynomial (Fin 3) ℂ

 
def realToComplexPlanePolynomial : PlanePoly →+* ComplexPlanePoly :=
  MvPolynomial.map Complex.ofRealHom

 
def complexPlanePolynomialEmbedding : ComplexPlanePoly →ₐ[ℂ] ProjectivePlanePoly :=
  MvPolynomial.rename Fin.castSucc

 
def realPlanePolynomialProjectiveEmbedding : PlanePoly →+* ProjectivePlanePoly :=
  complexPlanePolynomialEmbedding.toRingHom.comp realToComplexPlanePolynomial

 
def projectivePlaneZ : ProjectivePlanePoly :=
  MvPolynomial.X (Fin.last 2)

 
def planeHomogenizedLayer (D d : ℕ) (p : PlanePoly) : ProjectivePlanePoly :=
  realPlanePolynomialProjectiveEmbedding (MvPolynomial.homogeneousComponent d p) *
    projectivePlaneZ ^ (D - d)


def planeHomogenization (D : ℕ) (p : PlanePoly) : ProjectivePlanePoly :=
  ∑ d ∈ Finset.range (D + 1), planeHomogenizedLayer D d p


end Esgk


