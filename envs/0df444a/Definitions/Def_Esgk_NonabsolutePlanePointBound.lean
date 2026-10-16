-- Prove2me | Definitions.Def_Esgk_NonabsolutePlanePointBound
-- name    : Esgk_NonabsolutePlanePointBound
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:50:50.221177+00:00
-- url     : https://prove2.me/theorems/b6eb1f88-8dd8-46af-b4af-bbc53cb9e8d4
-- title:
--   Real and imaginary coefficient projections
-- statement:
--   This maps a complex plane polynomial to the real plane polynomials obtained by taking the real part or imaginary part of every coefficient.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneNonabsoluteRealPointBound
import Definitions.Def_Esgk_PlaneProjectiveHomogenization
import Definitions.Def_Esgk_PlaneProjectiveModel
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
open scoped ComplexConjugate

 
def complexRealPartPoly (H : ComplexPlanePoly) : PlanePoly :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange Complex.re (by simp) (AddMonoidAlgebra.coeff H))

 
def complexImagPartPoly (H : ComplexPlanePoly) : PlanePoly :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange Complex.im (by simp) (AddMonoidAlgebra.coeff H))


end Esgk


