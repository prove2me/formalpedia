-- Prove2me | Definitions.Def_Esgk_SelfCurveExceptionalIsometryFamilies
-- name    : Esgk_SelfCurveExceptionalIsometryFamilies
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:01:16.096989+00:00
-- url     : https://prove2.me/theorems/bf837633-f375-458d-8421-3e601d923f83
-- title:
--   Fixed anchors and labels induced by isometries
-- statement:
--   For a plane isometry, this defines sample anchors fixed by it and ordered sample pairs related by it. Taking unions over finite isometry families gives the corresponding exceptional anchor and label sets.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_SelfCurveExceptionalAnchors
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Basic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry PachDeZeeuw

 
noncomputable def selfCurveFixedAnchorsFor {d : ℕ}
    (X : PreparedBipartiteInput d) (g : Point2 ≃ᵢ Point2) : Finset X.P₁ := by
  classical
  exact Finset.univ.filter fun p ↦ g (p : Point2) = (p : Point2)


noncomputable def selfCurveAxisAnchorsFromReflections {d : ℕ}
    (X : PreparedBipartiteInput d) (reflections : Finset (Point2 ≃ᵢ Point2)) :
    Finset X.P₁ := by
  classical
  exact reflections.biUnion (selfCurveFixedAnchorsFor X)


noncomputable def selfCurveSymmetryLabelsFor {d : ℕ}
    (X : PreparedBipartiteInput d) (g : Point2 ≃ᵢ Point2) :
    Finset (X.P₁ × X.P₁) := by
  classical
  exact (Finset.univ.product Finset.univ).filter fun ij ↦
    g (ij.1 : Point2) = (ij.2 : Point2)


noncomputable def selfCurveSymmetryLabels {d : ℕ}
    (X : PreparedBipartiteInput d) (symmetries : Finset (Point2 ≃ᵢ Point2)) :
    Finset (X.P₁ × X.P₁) := by
  classical
  exact symmetries.biUnion (selfCurveSymmetryLabelsFor X)


end Esgk


