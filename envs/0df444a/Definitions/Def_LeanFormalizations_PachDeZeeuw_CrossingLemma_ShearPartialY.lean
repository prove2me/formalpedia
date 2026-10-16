-- Prove2me | Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY
-- name    : LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:47:42.824236+00:00
-- url     : https://prove2.me/theorems/5b4e1a0f-917a-4817-a9d5-de18292c2131
-- title:
--   The leading homogeneous part along a shear direction
-- statement:
--   This defines the univariate polynomial obtained from the top-degree homogeneous part of a plane polynomial by substituting $(X,Y)=(s,1)$.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_Shear
import Mathlib

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


noncomputable def shearTopPoly (h : PlanePoly) : Polynomial ℝ :=
  ∑ m ∈ h.support, (if m 0 + m 1 = h.totalDegree then
    Polynomial.C (coeff m h) * Polynomial.X ^ (m 0) else 0)


end PachDeZeeuw.Algebraic


