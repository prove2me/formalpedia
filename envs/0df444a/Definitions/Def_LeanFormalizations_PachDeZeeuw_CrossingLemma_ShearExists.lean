-- Prove2me | Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearExists
-- name    : LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearExists
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:49:09.716689+00:00
-- url     : https://prove2.me/theorems/a764c98e-dcd7-4547-8bf3-5a7b6b1d5e66
-- title:
--   A polynomial detecting failure of shear separation
-- statement:
--   For two planar points, this defines the linear polynomial whose value at a shear parameter is the difference of their first coordinates after the shear.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearIrreducible
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY
import Mathlib

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


noncomputable def sepPoly (p q : ℝ × ℝ) : Polynomial ℝ :=
  Polynomial.C (p.1 - q.1) - Polynomial.C (p.2 - q.2) * Polynomial.X


end PachDeZeeuw.Algebraic


