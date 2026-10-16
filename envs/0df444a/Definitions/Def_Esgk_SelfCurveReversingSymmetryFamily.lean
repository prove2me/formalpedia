-- Prove2me | Definitions.Def_Esgk_SelfCurveReversingSymmetryFamily
-- name    : Esgk_SelfCurveReversingSymmetryFamily
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:05:51.61389+00:00
-- url     : https://prove2.me/theorems/e1be5807-f20b-4a07-b5e8-78c2e0c35f9d
-- title:
--   Orientation-reversing symmetries of a common curve
-- statement:
--   For prepared incidence data supported on a single curve, this selects the orientation-reversing members of its finite family of curve-preserving isometries.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PachDeZeeuwQuadraticDegree
import Definitions.Def_Esgk_RichnessLevels
import Definitions.Def_Esgk_SelfCurveCompleteSymmetryFamily
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Basic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveInterface
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open PachDeZeeuw


noncomputable def selfCurveReversingCarrierSymmetries
    {d : ℕ} {X : PreparedBipartiteInput d}
    (hself : SelfCurvePreparedInput X) : Finset (Point2 ≃ᵢ Point2) := by
  classical
  exact (selfCurveCarrierSymmetries hself).filter fun g ↦ ¬ IsDirect g


end Esgk


