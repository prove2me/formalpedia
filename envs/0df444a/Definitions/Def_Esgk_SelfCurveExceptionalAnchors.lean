-- Prove2me | Definitions.Def_Esgk_SelfCurveExceptionalAnchors
-- name    : Esgk_SelfCurveExceptionalAnchors
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:59:04.901518+00:00
-- url     : https://prove2.me/theorems/ab47a17b-1b5c-4ed9-a362-0eff381a936c
-- title:
--   Exceptional anchors from singular points
-- statement:
--   This selects first-sample anchors that are singular points of the polynomial chosen for the second supporting curve. It then adjoins a separately specified set of exceptional axis anchors.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_AuxiliaryCircleNoncontainment
import Definitions.Def_Esgk_AuxiliaryIncidenceDeletion
import Definitions.Def_Esgk_PachDeZeeuwQuadraticDegree
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Basic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Bezout
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry PachDeZeeuw PachDeZeeuw.Algebraic

 
noncomputable def selfCurveSingularAnchors {d : ℕ}
    (X : PreparedBipartiteInput d) : Finset X.P₁ := by
  classical
  exact Finset.univ.filter fun p ↦
    (p : PachDeZeeuw.Algebraic.Point2) ∈
      SingularPointSet (preparedSecondCurvePolynomial X)


noncomputable def selfCurveExceptionalAnchors {d : ℕ}
    (X : PreparedBipartiteInput d) (axisAnchors : Finset X.P₁) : Finset X.P₁ := by
  classical
  exact selfCurveSingularAnchors X ∪ axisAnchors


end Esgk


