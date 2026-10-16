-- Prove2me | Definitions.Def_Esgk_PlaneCircularLocalChart
-- name    : Esgk_PlaneCircularLocalChart
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:55:49.593893+00:00
-- url     : https://prove2.me/theorems/e7f2eaa7-f5d8-4c18-957a-d4bde6c8dd98
-- title:
--   Local polynomial charts at the circular points
-- statement:
--   This defines substitutions $(X,Y,Z)=(1,c+u,z)$ for complex projective plane polynomials, together with their affine counterparts. The specializations $c=i$ and $c=-i$ give charts at the two circular points at infinity.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneProjectiveHomogenization
import Definitions.Def_Esgk_PlaneRadialQuadratic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

 
abbrev CircularChartPoly := MvPolynomial (Fin 2) ℂ

 
def circularChartU : CircularChartPoly :=
  MvPolynomial.X 0

 
def circularChartZ : CircularChartPoly :=
  MvPolynomial.X 1

 
def affineCircularChart (c : ℂ) : PlanePoly →+* CircularChartPoly :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : ℂ →+* CircularChartPoly).comp Complex.ofRealHom)
    ![1, MvPolynomial.C c + circularChartU]

 
def projectiveCircularChart (c : ℂ) : ProjectivePlanePoly →+* CircularChartPoly :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* CircularChartPoly)
    ![1, MvPolynomial.C c + circularChartU, circularChartZ]

 
def affineCircularChartI : PlanePoly →+* CircularChartPoly :=
  affineCircularChart Complex.I

 
def affineCircularChartJ : PlanePoly →+* CircularChartPoly :=
  affineCircularChart (-Complex.I)

 
def projectiveCircularChartI : ProjectivePlanePoly →+* CircularChartPoly :=
  projectiveCircularChart Complex.I

 
def projectiveCircularChartJ : ProjectivePlanePoly →+* CircularChartPoly :=
  projectiveCircularChart (-Complex.I)


end Esgk


