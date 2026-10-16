-- Prove2me | Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_Shear
-- name    : LeanFormalizations_PachDeZeeuw_CrossingLemma_Shear
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:45:57.721465+00:00
-- url     : https://prove2.me/theorems/64c3129c-dde1-4298-bd5d-628aca7f2ce5
-- title:
--   Shearing planar points and polynomials
-- statement:
--   This defines polynomial substitution by $(X,Y)\mapsto(X+sY,Y)$ and the corresponding inverse coordinate change $(x,y)\mapsto(x-sy,y)$ on points.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


noncomputable def shearVars (s : ℝ) : Fin 2 → PlanePoly :=
  fun i => if i = 0 then MvPolynomial.X 0 + (MvPolynomial.C s) * MvPolynomial.X 1
           else MvPolynomial.X 1

 
noncomputable def shearPoly (s : ℝ) (h : PlanePoly) : PlanePoly :=
  MvPolynomial.aeval (shearVars s) h

 
def shearPoint (s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1 - s * p.2, p.2)


end PachDeZeeuw.Algebraic


